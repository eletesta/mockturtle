/* mockturtle: C++ logic network library
 * Copyright (C) 2018-2019  EPFL
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */

#include "experiments.hpp"

#include <lorina/lorina.hpp>
#include <mockturtle/algorithms/balancing.hpp>
#include <mockturtle/algorithms/balancing/sop_balancing.hpp>
#include <mockturtle/algorithms/cleanup.hpp>
#include <mockturtle/algorithms/collapse_mapped.hpp>
#include <mockturtle/algorithms/cut_rewriting.hpp>
#include <mockturtle/algorithms/detail/database_generator.hpp>
#include <mockturtle/algorithms/lut_mapping.hpp>
#include <mockturtle/algorithms/mig_algebraic_rewriting.hpp>
#include <mockturtle/algorithms/mig_algebraic_rewriting_buffers.hpp>
#include <mockturtle/algorithms/mig_feasible_resub.hpp>
#include <mockturtle/algorithms/mig_resub.hpp>
#include <mockturtle/algorithms/node_resynthesis.hpp>
#include <mockturtle/algorithms/node_resynthesis/akers.hpp>
#include <mockturtle/algorithms/node_resynthesis/exact.hpp>
#include <mockturtle/algorithms/node_resynthesis/mig4_npn.hpp>
#include <mockturtle/algorithms/refactoring.hpp>
#include <mockturtle/io/aiger_reader.hpp>
#include <mockturtle/io/blif_reader.hpp>
#include <mockturtle/io/index_list.hpp>
#include <mockturtle/io/verilog_reader.hpp>
#include <mockturtle/io/write_verilog.hpp>
#include <mockturtle/networks/aig.hpp>
#include <mockturtle/views/depth_view.hpp>
#include <mockturtle/views/fanout_view.hpp>
#include <mockturtle/views/mapping_view.hpp>

#include <fmt/format.h>

#include <string>
#include <vector>

namespace detail
{

template<class Ntk>
struct if_cost
{
  uint32_t operator()( mockturtle::depth_view<Ntk> const& ntk, mockturtle::node<Ntk> const& n ) const
  {
    //mockturtle::depth_view<Ntk> ntk_d{ntk};
    uint32_t cost = 0;
    ntk.foreach_fanin( n, [&]( const auto& f ) {
      if ( ntk.node_to_index( ntk.get_node( f ) ) == 0 )
        return true;
      cost = ntk.level( n ) - ntk.level( ntk.get_node( f ) ) - 1;
      // add something on the fanout
      return true;
    } );
    return cost;
  }
};

int compute_buffers( mockturtle::mig_network mig )
{
  mockturtle::depth_view depth_mig{mig};
  std::vector<int> buffers( mig.size(), 0 );
  int number_buff = 0;

  mig.foreach_gate( [&]( auto f ) {
    auto main_depth = depth_mig.level( f );
    mig.foreach_fanin( f, [&]( auto const& s ) {
      auto index = mig.node_to_index( mig.get_node( s ) );
      if ( index == 0 )
        return true;
      int diff = main_depth - 1 - depth_mig.level( mig.get_node( s ) ) - buffers[index];
      if ( diff >= 0 )
      {
        buffers[index] = buffers[index] + diff;
      }
      return true;
    } );
  } );

  auto total_depth = depth_mig.depth();
  mig.foreach_po( [&]( auto s, auto i ) {
    if ( depth_mig.level( mig.get_node( s ) ) == total_depth )
      return true;
    auto index = mig.node_to_index( mig.get_node( s ) );
    if ( index == 0 )
      return true;
    int diff = total_depth - depth_mig.level( mig.get_node( s ) ) - buffers[index];
    if ( diff >= 0 )
    {
      buffers[index] = buffers[index] + diff;
    }
    return true;
  } );

  for ( auto h = 0u; h < buffers.size(); h++ )
  {
    number_buff = number_buff + buffers[h];
  }
  return number_buff;
}

int compute_buffers_aig( mockturtle::aig_network aig )
{
  mockturtle::depth_view depth_aig{aig};
  std::vector<int> buffers( aig.size(), 0 );
  int number_buff = 0;

  aig.foreach_gate( [&]( auto f ) {
    auto main_depth = depth_aig.level( f );
    aig.foreach_fanin( f, [&]( auto const& s ) {
      auto index = aig.node_to_index( aig.get_node( s ) );
      if ( index == 0 )
        return true;
      int diff = main_depth - 1 - depth_aig.level( aig.get_node( s ) ) - buffers[index];
      if ( diff >= 0 )
      {
        buffers[index] = buffers[index] + diff;
      }
      return true;
    } );
  } );

  auto total_depth = depth_aig.depth();
  aig.foreach_po( [&]( auto s, auto i ) {
    if ( depth_aig.level( aig.get_node( s ) ) == total_depth )
      return true;
    auto index = aig.node_to_index( aig.get_node( s ) );
    if ( index == 0 )
      return true;
    int diff = total_depth - depth_aig.level( aig.get_node( s ) ) - buffers[index];
    if ( diff >= 0 )
    {
      buffers[index] = buffers[index] + diff;
    }
    return true;
  } );

  for ( auto h = 0u; h < buffers.size(); h++ )
  {
    number_buff = number_buff + buffers[h];
  }
  return number_buff;
}

} // namespace detail

template<typename Ntk>
mockturtle::klut_network lut_map( Ntk const& ntk, uint32_t k = 4 )
{
  mockturtle::write_verilog( ntk, "/tmp/network.v" );
  system( fmt::format( "../../abc/abc -q \"/tmp/network.v; &get; &if -a -K {}; &put; write_blif /tmp/output.blif\"", k ).c_str() );

  mockturtle::klut_network klut;
  if ( lorina::read_blif( "/tmp/output.blif", mockturtle::blif_reader( klut ) ) != lorina::return_code::success )
  {
    std::cout << "ERROR 1" << std::endl;
    std::abort();
    return klut;
  }
  return klut;
}

void example1()
{
  /* enumerate NPN representatives */
  std::unordered_set<kitty::dynamic_truth_table, kitty::hash<kitty::dynamic_truth_table>> classes;
  kitty::dynamic_truth_table tt( 5u );
  auto i = 0;
  do
  {
    i++;
    const auto res = kitty::exact_npn_canonization( tt );
    classes.insert( std::get<0>( res ) );
    kitty::next_inplace( tt );
  } while ( !kitty::is_const0( tt ) );

  std::cout << "[i] enumerated "
            << ( 1 << ( 1 << tt.num_vars() ) ) << " functions into "
            << classes.size() << " classes." << std::endl;

  /* generate database with exact XMG synthesis */
  mockturtle::mig_network mig;
  mockturtle::exact_mig_resynthesis_params ps;
  ps.num_candidates = 5u;
  mockturtle::detail::database_generator_params ps_db;
  mockturtle::exact_mig_resynthesis<mockturtle::mig_network> exact( ps );
  ps_db.verbose = true;
  ps_db.multiple_candidates = true;
  mockturtle::detail::database_generator dbgen( mig, exact, ps_db );
  for ( const auto& f : classes )
  {
    dbgen.add_function( f );

    std::cout << ".";
    std::cout.flush();
  }
  mockturtle::write_verilog( mig, "db_5.v" );
}

void example2()
{
  using namespace experiments;

  /* load database from file */
  mockturtle::mig_network mig_db;
  read_verilog( "db.v", mockturtle::verilog_reader( mig_db ) );

  /* option 1: XMG strategy using database from file */
  mockturtle::mig4_npn_resynthesis_params ps;
  ps.multiple_depth = false;
  ps.verbose = true;
  mockturtle::mig4_npn_resynthesis<mockturtle::mig_network> mig_resyn( mockturtle::detail::to_index_list( mig_db ), ps );

  experiments::experiment<std::string, uint32_t, uint32_t, uint32_t, uint32_t, bool> exp( "miglut_nodepth", "benchmark", "LUTs", "MIG", "depth", "buffers", "eq cec" );

  for ( auto const& benchmark : epfl_benchmarks( experiments::all ) )
  {
    fmt::print( "[i] processing {}\n", benchmark );

    /* read aig */
    mockturtle::aig_network aig;
    if ( lorina::read_aiger( experiments::benchmark_path( benchmark ), mockturtle::aiger_reader( aig ) ) != lorina::return_code::success )
    {
      std::cout << "ERROR 2" << std::endl;
      std::abort();
      return;
    }

    /* LUT map AIG into k-LUT network */
    auto klut = lut_map( aig, 4u );

    /* resynthesize klut with resynthesis strategies */
    mockturtle::mig_network mig;
    mig = mockturtle::node_resynthesis<mockturtle::mig_network>( klut, mig_resyn );
    mockturtle::depth_view depth_mig{mig};

    exp( benchmark, klut.size(), mig.size(), depth_mig.depth(), detail::compute_buffers( mig ), experiments::abc_cec( mig, benchmark ) );
  }

  exp.save();
  exp.table();
}

// for debug
void example3()
{
  /* load database from file */
  mockturtle::mig_network mig_db;
  read_verilog( "db.v", mockturtle::verilog_reader( mig_db ) );

  /* option 1: XMG strategy using database from file */
  mockturtle::mig4_npn_resynthesis_params ps;
  ps.multiple_if = true;
  ps.verbose = true;
  mockturtle::mig4_npn_resynthesis<mockturtle::mig_network> mig_resyn( mockturtle::detail::to_index_list( mig_db ), ps );

  auto file = "../experiments/benchmarks/int2float.aig";

  /* read aig */
  mockturtle::aig_network aig;
  if ( lorina::read_aiger( file, mockturtle::aiger_reader( aig ) ) != lorina::return_code::success )
  {
    std::cout << "ERROR 2" << std::endl;
    std::abort();
    return;
  }

  /* LUT map AIG into k-LUT network */
  auto klut = lut_map( aig, 4u );

  /* resynthesize klut with resynthesis strategies */
  mockturtle::mig_network mig;
  mig = mockturtle::node_resynthesis<mockturtle::mig_network>( klut, mig_resyn );
  mockturtle::depth_view depth_mig{mig};
  std::cout << "klut | mig | depth | eq \n";
  std::cout << klut.size() << " | " << mig.size() << " | " << depth_mig.depth() << "      | " << experiments::abc_cec( mig, "int2float" ) << std::endl;
}

// compare with and without depth
void example4()
{
  using namespace experiments;

  /* load database from file */
  mockturtle::mig_network mig_db;
  read_verilog( "db.v", mockturtle::verilog_reader( mig_db ) );

  /* option 1: XMG strategy using database from file */
  mockturtle::mig4_npn_resynthesis_params ps;
  ps.multiple_depth = false;
  //ps.verbose = true;
  mockturtle::mig4_npn_resynthesis<mockturtle::mig_network> mig_resyn( mockturtle::detail::to_index_list( mig_db ), ps );

  ps.multiple_depth = true;
  mockturtle::mig4_npn_resynthesis<mockturtle::mig_network> mig_resyn2( mockturtle::detail::to_index_list( mig_db ), ps );

  experiments::experiment<std::string, uint32_t, uint32_t, uint32_t, uint32_t, bool, uint32_t, uint32_t, uint32_t, bool, int> exp( "miglut_compare", "benchmark", "LUTs", "MIG_1", "depth_1", "buffers_1", "eq cec1", "MIG_2", "depth_2", "buffers_2", "eq cec_2", "buffer_change" );

  for ( auto const& benchmark : sce_benchmarks() )
  {
    fmt::print( "[i] processing {}\n", benchmark );
    if ( benchmark == "hyp" )
      continue;

    /* read aig */
    mockturtle::aig_network aig;
    if ( lorina::read_aiger( experiments::benchmark_sce_path( benchmark ), mockturtle::aiger_reader( aig ) ) != lorina::return_code::success )
    {
      std::cout << "ERROR 2" << std::endl;
      std::abort();
      return;
    }

    /* LUT map AIG into k-LUT network */
    auto klut = lut_map( aig, 4u );

    /* resynthesize klut with resynthesis strategies */
    mockturtle::mig_network mig;
    mig = mockturtle::node_resynthesis<mockturtle::mig_network>( klut, mig_resyn );
    mockturtle::depth_view depth_mig{mig};

    mockturtle::mig_network mig2;
    mig2 = mockturtle::node_resynthesis<mockturtle::mig_network>( klut, mig_resyn2 );
    mockturtle::depth_view depth_mig2{mig2};

    auto buffers1 = detail::compute_buffers( mig );
    auto buffers2 = detail::compute_buffers( mig2 );
    exp( benchmark, klut.size(), mig.size(), depth_mig.depth(), buffers1, experiments::abc_cec_sce( mig, benchmark ), mig2.size(), depth_mig2.depth(), buffers2, experiments::abc_cec_sce( mig2, benchmark ), buffers1 - buffers2 );
  }

  exp.save();
  exp.table();
}

// example 4 but until saturation are results
void example5()
{
  using namespace experiments;

  /* load database from file */
  mockturtle::mig_network mig_db;
  read_verilog( "db.v", mockturtle::verilog_reader( mig_db ) );

  /* option 1: XMG strategy using database from file */
  mockturtle::mig4_npn_resynthesis_params ps;
  ps.multiple_depth = false;
  //ps.verbose = true;
  mockturtle::mig4_npn_resynthesis<mockturtle::mig_network> mig_resyn( mockturtle::detail::to_index_list( mig_db ), ps );

  ps.multiple_depth = true;
  mockturtle::mig4_npn_resynthesis<mockturtle::mig_network> mig_resyn2( mockturtle::detail::to_index_list( mig_db ), ps );

  experiments::experiment<std::string, uint32_t, uint32_t, uint32_t, uint32_t, bool, uint32_t, uint32_t, uint32_t, bool, int> exp( "miglut_compare", "benchmark", "LUTs", "MIG_1", "depth_1", "buffers_1", "eq cec1", "MIG_2", "depth_2", "buffers_2", "eq cec_2", "buffer_change" );

  for ( auto const& benchmark : sce_benchmarks() )
  {
    fmt::print( "[i] processing {}\n", benchmark );
    if ( benchmark == "hyp" )
      continue;

    /* read aig */
    mockturtle::aig_network aig;
    if ( lorina::read_aiger( experiments::benchmark_sce_path( benchmark ), mockturtle::aiger_reader( aig ) ) != lorina::return_code::success )
    {
      std::cout << "ERROR 2" << std::endl;
      std::abort();
      return;
    }

    /* LUT map AIG into k-LUT network */
    auto klut = lut_map( aig, 4u );

    /* resynthesize klut with resynthesis strategies */
    mockturtle::mig_network mig;
    mig = mockturtle::node_resynthesis<mockturtle::mig_network>( klut, mig_resyn );

    while ( true )
    {
      mockturtle::mig_network new_mig;
      mockturtle::depth_view depth_mig{mig};
      auto const mig_depth_before = depth_mig.depth();
      auto const klut_size_before = klut.size();
      new_mig = mockturtle::node_resynthesis<mockturtle::mig_network>( klut, mig_resyn );

      mockturtle::depth_view depth_mig_new{new_mig};
      auto const new_klut = lut_map( new_mig );

      if ( new_klut.size() >= klut_size_before )
        break;
      if ( depth_mig_new.depth() > mig_depth_before )
        break;

      klut = new_klut;
      mig = new_mig;
    }

    mockturtle::depth_view depth_mig{mig};
    mockturtle::mig_network mig2;
    mig2 = mockturtle::node_resynthesis<mockturtle::mig_network>( klut, mig_resyn2 );

    while ( true )
    {
      mockturtle::mig_network new_mig;
      mockturtle::depth_view depth_mig{mig2};
      auto const mig_depth_before = depth_mig.depth();
      auto const klut_size_before = klut.size();
      new_mig = mockturtle::node_resynthesis<mockturtle::mig_network>( klut, mig_resyn2 );
      mockturtle::depth_view depth_mig_new{new_mig};
      auto const new_klut = lut_map( new_mig );

      if ( new_klut.size() >= klut_size_before )
        break;
      if ( depth_mig_new.depth() > mig_depth_before )
        break;

      klut = new_klut;
      mig2 = new_mig;
    }

    mockturtle::depth_view depth_mig2{mig2};

    auto buffers1 = detail::compute_buffers( mig );
    auto buffers2 = detail::compute_buffers( mig2 );
    exp( benchmark, klut.size(), mig.size(), depth_mig.depth(), buffers1, experiments::abc_cec_sce( mig, benchmark ), mig2.size(), depth_mig2.depth(), buffers2, experiments::abc_cec_sce( mig2, benchmark ), buffers1 - buffers2 );
  }

  exp.save();
  exp.table();
}

// example 5 + agebraic rewriting
void example6()
{
  using namespace experiments;

  /* load database from file */
  mockturtle::mig_network mig_db;
  read_verilog( "db.v", mockturtle::verilog_reader( mig_db ) );

  /* option 1: XMG strategy using database from file */
  mockturtle::mig4_npn_resynthesis_params ps;

  //ps.multiple_depth = true;
  mockturtle::mig4_npn_resynthesis<mockturtle::mig_network> mig_resyn2( mockturtle::detail::to_index_list( mig_db ), ps );

  experiments::experiment<std::string, uint32_t, uint32_t, uint32_t, uint32_t, bool, uint32_t, uint32_t, uint32_t, uint32_t, bool, int> exp( "miglut_compare", "benchmark", "MIG_1", "depth_1", "buffers_1", "cost_1", "eq cec1", "MIG_2", "depth_2", "buffers_2", "cost_2", "eq cec_2", "buffer_change" );

  for ( auto const& benchmark : sce_benchmarks() )
  {
    fmt::print( "[i] processing {}\n", benchmark );
    if ( benchmark == "hyp" )
      continue;

    /* read aig */
    mockturtle::aig_network aig;
    if ( lorina::read_aiger( experiments::benchmark_sce_path( benchmark ), mockturtle::aiger_reader( aig ) ) != lorina::return_code::success )
    {
      std::cout << "ERROR 2" << std::endl;
      std::abort();
      return;
    }

    /* LUT map AIG into k-LUT network */
    auto klut = lut_map( aig, 4u );

    mockturtle::mig_network mig2;
    mig2 = mockturtle::node_resynthesis<mockturtle::mig_network>( klut, mig_resyn2 );

    /*while ( true )
    {
      mockturtle::mig_network new_mig;
      mockturtle::depth_view depth_mig{mig2};
      auto const mig_depth_before = depth_mig.depth();
      auto const klut_size_before = klut.size();
      new_mig = mockturtle::node_resynthesis<mockturtle::mig_network>( klut, mig_resyn2 );
      mockturtle::depth_view depth_mig_new{new_mig};
      auto const new_klut = lut_map( new_mig );

      if ( new_klut.size() >= klut_size_before )
        break;
      if ( depth_mig_new.depth() > mig_depth_before )
        break;

      klut = new_klut;
      mig2 = new_mig;
    }*/

    using view_t = mockturtle::depth_view<mockturtle::fanout_view<mockturtle::mig_network>>;
    using view_f = mockturtle::fanout_view<mockturtle::mig_network>;

    view_f f_view{mig2};
    view_t depth_mig2{f_view};

    //mockturtle::depth_view depth_mig2{mig2};
    auto const size_b = mig2.size();
    auto const depth_b = depth_mig2.depth();
    auto buffers1 = detail::compute_buffers( mig2 );

    mockturtle::mig_algebraic_depth_rewriting_params ps;
    ps.strategy = mockturtle::mig_algebraic_depth_rewriting_params::aggressive;
    //ps.allow_area_increase = false;
    mig_algebraic_depth_rewriting_buffers( depth_mig2, ps );
    mockturtle::mig_network mig4 = depth_mig2;
    mig4 = cleanup_dangling( mig4 );
    auto buffers2 = detail::compute_buffers( mig4 );
    mockturtle::depth_view depth_mig4{mig4};

    exp( benchmark, size_b, depth_b, buffers1, buffers1 + size_b, experiments::abc_cec_sce( mig2, benchmark ), mig4.size(), depth_mig4.depth(), buffers2, buffers2 + mig4.size(), experiments::abc_cec_sce( mig4, benchmark ), buffers1 - buffers2 );
  }

  exp.save();
  exp.table();
}

// example 6 + resub
void example7()
{
  using namespace experiments;

  /* load database from file */
  mockturtle::mig_network mig_db;
  read_verilog( "db.v", mockturtle::verilog_reader( mig_db ) );

  /* option 1: XMG strategy using database from file */
  mockturtle::mig4_npn_resynthesis_params ps;

  ps.multiple_depth = true;
  mockturtle::mig4_npn_resynthesis<mockturtle::mig_network> mig_resyn2( mockturtle::detail::to_index_list( mig_db ), ps );

  experiments::experiment<std::string, uint32_t, uint32_t, uint32_t, uint32_t, bool, uint32_t, uint32_t, uint32_t, bool, int> exp( "miglut_compare", "benchmark", "LUTs", "MIG_1", "depth_1", "buffers_1", "eq cec1", "MIG_2", "depth_2", "buffers_2", "eq cec_2", "buffer_change" );

  for ( auto const& benchmark : sce_benchmarks() )
  {
    fmt::print( "[i] processing {}\n", benchmark );
    if ( benchmark == "hyp" )
      continue;

    /* read aig */
    mockturtle::aig_network aig;
    if ( lorina::read_aiger( experiments::benchmark_sce_path( benchmark ), mockturtle::aiger_reader( aig ) ) != lorina::return_code::success )
    {
      std::cout << "ERROR 2" << std::endl;
      std::abort();
      return;
    }

    /* LUT map AIG into k-LUT network */
    auto klut = lut_map( aig, 4u );

    mockturtle::mig_network mig2;
    mig2 = mockturtle::node_resynthesis<mockturtle::mig_network>( klut, mig_resyn2 );

    while ( true )
    {
      mockturtle::mig_network new_mig;
      mockturtle::depth_view depth_mig{mig2};
      auto const mig_depth_before = depth_mig.depth();
      auto const klut_size_before = klut.size();
      new_mig = mockturtle::node_resynthesis<mockturtle::mig_network>( klut, mig_resyn2 );
      mockturtle::depth_view depth_mig_new{new_mig};
      auto const new_klut = lut_map( new_mig );

      if ( new_klut.size() >= klut_size_before )
        break;
      if ( depth_mig_new.depth() > mig_depth_before )
        break;

      klut = new_klut;
      mig2 = new_mig;
    }

    mockturtle::depth_view depth_mig2{mig2};
    mig_algebraic_depth_rewriting( depth_mig2 );

    auto const size_b = depth_mig2.size();
    auto const depth_b = depth_mig2.depth();
    auto buffers1 = detail::compute_buffers( depth_mig2 );

    mockturtle::mig_network mig3 = depth_mig2;

    using view_t = mockturtle::depth_view<mockturtle::fanout_view<mockturtle::mig_network>>;
    using view_f = mockturtle::fanout_view<mockturtle::mig_network>;
    view_f fanout_view{mig3};
    view_t resub_view{fanout_view};

    mockturtle::resubstitution_params ps;
    //ps.verbose = true;
    ps.max_divisors = 150;
    mig_feasible_resubstitution( resub_view, ps );

    mig3 = cleanup_dangling( mig3 );
    mockturtle::depth_view depth_mig3{mig3};
    auto buffers2 = detail::compute_buffers( mig3 );

    exp( benchmark, klut.size(), size_b, depth_b, buffers1, experiments::abc_cec_sce( depth_mig2, benchmark ), mig3.size(), depth_mig3.depth(), buffers2, experiments::abc_cec_sce( mig3, benchmark ), buffers1 - buffers2 );
  }

  exp.save();
  exp.table();
}

// example 7 but saturation of results -- complete flow
void example7_bis()
{
  using namespace experiments;

  /* load database from file */
  mockturtle::mig_network mig_db;
  read_verilog( "db.v", mockturtle::verilog_reader( mig_db ) );

  /* option 1: XMG strategy using database from file */
  mockturtle::mig4_npn_resynthesis_params ps;

  ps.multiple_if = false;
  mockturtle::mig4_npn_resynthesis<mockturtle::mig_network> mig_resyn2( mockturtle::detail::to_index_list( mig_db ), ps );

  ps.multiple_if = false;
  ps.multiple_depth = false;
  mockturtle::mig4_npn_resynthesis<mockturtle::mig_network> mig_resyn_start( mockturtle::detail::to_index_list( mig_db ), ps );

  experiments::experiment<std::string, uint32_t, uint32_t, uint32_t, uint32_t, uint32_t, uint32_t, uint32_t, uint32_t, bool, uint32_t, uint32_t, uint32_t, uint32_t, bool, int> exp( "miglut_compare", "benchmark", "AIG_1", "depth_aig", "buffers_aig", "cost_aig",
                                                                                                                                                                                     "MIG_1", "depth_1", "buffers_1", "cost_1", "eq cec1", "MIG_2", "depth_2", "buffers_2", "cost_2", "eq cec_2", "buffer_change" );

  for ( auto const& benchmark : sce_benchmarks() )
  {
    fmt::print( "[i] processing {}\n", benchmark );
    if ( benchmark == "hyp" )
      continue;

    /* read aig */
    mockturtle::aig_network aig;
    if ( lorina::read_aiger( experiments::benchmark_sce_path( benchmark ), mockturtle::aiger_reader( aig ) ) != lorina::return_code::success )
    {
      std::cout << "ERROR 2" << std::endl;
      std::abort();
      return;
    }

    auto size_aig = aig.num_gates();
    mockturtle::depth_view aig_depth{aig};
    auto depth_aig = aig_depth.depth();
    auto buffers_aig = detail::compute_buffers_aig( aig );

    /* LUT map AIG into k-LUT network */
    auto klut = lut_map( aig, 4u );

    mockturtle::mig_network mig1;
    mig1 = mockturtle::node_resynthesis<mockturtle::mig_network>( klut, mig_resyn_start );
    mockturtle::depth_view depth_mig1{mig1};
    auto const size_b = mig1.num_gates();
    auto const depth_b = depth_mig1.depth();
    auto buffers1 = detail::compute_buffers( mig1 );

    mockturtle::mig_network mig2;
    mig2 = mockturtle::node_resynthesis<mockturtle::mig_network>( klut, mig_resyn2 );

    /*while ( true )
    {
      mockturtle::mig_network new_mig;
      mockturtle::depth_view depth_mig{mig2};
      auto const mig_depth_before = depth_mig.depth();
      auto const klut_size_before = klut.size();
      new_mig = mockturtle::node_resynthesis<mockturtle::mig_network>( klut, mig_resyn2 );
      mockturtle::depth_view depth_mig_new{new_mig};
      auto const new_klut = lut_map( new_mig );

      if ( new_klut.size() >= klut_size_before )
        break;
      if ( depth_mig_new.depth() > mig_depth_before )
        break;

      klut = new_klut;
      mig2 = new_mig;
    }*/

    using view_t = mockturtle::depth_view<mockturtle::fanout_view<mockturtle::mig_network>>;
    using view_f = mockturtle::fanout_view<mockturtle::mig_network>;

    view_f f_view{mig2};
    view_t depth_mig2{f_view};
    mockturtle::mig_algebraic_depth_rewriting_params ps;
    ps.strategy = mockturtle::mig_algebraic_depth_rewriting_params::aggressive;
    //mig_algebraic_depth_rewriting_buffers( depth_mig2, ps );
    //mig_algebraic_depth_rewriting_buffers( depth_mig2, ps );
    mig_algebraic_depth_rewriting( depth_mig2, ps );
    mig_algebraic_depth_rewriting( depth_mig2, ps );

    mockturtle::mig_network mig3 = depth_mig2;
    mig3 = cleanup_dangling( mig3 );
    mockturtle::mig_network mig4 = depth_mig2;
    mig4 = cleanup_dangling( mig4 );

    mockturtle::resubstitution_params ps2;
    //ps2.max_divisors = 300;
    ps2.max_divisors = 150;
    //ps2.verbose =true;
    ps2.max_inserts = 1;

    auto original_buffer = detail::compute_buffers( mig3 );
    auto i = 0u;
    while ( true )
    {
      if ( i >= 0 )
        break;
      i++;
      view_f fanout_view{mig4};
      view_t resub_view{fanout_view};
      //mig_feasible_resubstitution( resub_view, ps2 );
      mig_resubstitution( resub_view, ps2 );

      mig4 = cleanup_dangling( mig4 );
      //if ( detail::compute_buffers( mig4 ) >= original_buffer )
      //  break;
      mig3 = mig4;
      ////original_buffer = detail::compute_buffers( mig4 );
    }

    view_f f_view3{mig3};
    view_t depth_mig3{f_view3};
    //mig_algebraic_depth_rewriting_buffers( depth_mig3, ps );
    //mig_algebraic_depth_rewriting_buffers( depth_mig3, ps );
    //mig_algebraic_depth_rewriting( depth_mig3, ps );
    //mig_algebraic_depth_rewriting( depth_mig3, ps );

    mockturtle::mig_network mig5 = depth_mig3;
    mig5 = cleanup_dangling( mig5 );
    mockturtle::depth_view depth_mig5{mig5};
    auto buffers2 = detail::compute_buffers( mig5 );

    mockturtle::write_verilog( mig5, fmt::format( "{}_mig_debug.v", benchmark ) );

    exp( benchmark, size_aig, depth_aig, buffers_aig, buffers_aig + size_aig, size_b, depth_b, buffers1, buffers1 + size_b, experiments::abc_cec_sce( depth_mig2, benchmark ), mig5.num_gates(), depth_mig5.depth(), buffers2, buffers2 + mig5.num_gates(), experiments::abc_cec_sce( mig5, benchmark ), buffers1 - buffers2 );
  }

  exp.save();
  exp.table();
}

// new starting point
void example7_c()
{
  using namespace experiments;

  experiments::experiment<std::string, uint32_t, uint32_t, uint32_t, uint32_t, bool, uint32_t, uint32_t, uint32_t, uint32_t, bool, int> exp( "miglut_compare", "benchmark",
                                                                                                                                             "MIG_1", "depth_1", "buffers_1", "cost_1", "eq cec1", "MIG_2", "depth_2", "buffers_2", "cost_2", "eq cec_2", "buffer_change" );

  for ( auto const& benchmark : sce_benchmarks() )
  {
    fmt::print( "[i] processing {}\n", benchmark );
    if ( benchmark == "hyp" )
      continue;

    mockturtle::mig_network mig;
    if ( read_verilog( experiments::benchmark_sce_mig_path( benchmark ), mockturtle::verilog_reader( mig ) ) != lorina::return_code::success )
    {
      std::cout << "ERROR 2" << std::endl;
      std::abort();
      return;
    }

    mockturtle::depth_view depth_mig1{mig};
    auto const size_b = mig.size();
    auto const depth_b = depth_mig1.depth();
    auto buffers1 = detail::compute_buffers( mig );
    auto mig2 = mig;

    using view_t = mockturtle::depth_view<mockturtle::fanout_view<mockturtle::mig_network>>;
    using view_f = mockturtle::fanout_view<mockturtle::mig_network>;

    view_f f_view{mig2};
    view_t depth_mig2{f_view};
    mockturtle::mig_algebraic_depth_rewriting_params ps;
    ps.strategy = mockturtle::mig_algebraic_depth_rewriting_params::aggressive;
    std::cout << " depth\n";
    mig_algebraic_depth_rewriting_buffers( depth_mig2, ps );
    mig_algebraic_depth_rewriting_buffers( depth_mig2, ps );

    mockturtle::mig_network mig3 = depth_mig2;
    mig3 = cleanup_dangling( mig3 );
    mockturtle::mig_network mig4 = depth_mig2;
    mig4 = cleanup_dangling( mig4 );

    mockturtle::resubstitution_params ps2;
    ps2.max_divisors = 300;
    ps2.max_inserts = 1;

    auto original_buffer = detail::compute_buffers( mig3 );
    auto i = 0u;
    std::cout << " resub\n";
    while ( true )
    {
      if ( i > 3 )
        break;
      i++;
      view_f fanout_view{mig4};
      view_t resub_view{fanout_view};
      std::cout << " resub\n";
      mig_feasible_resubstitution( resub_view, ps2 );

      mig4 = cleanup_dangling( mig4 );
      if ( detail::compute_buffers( mig4 ) >= original_buffer )
        break;
      mig3 = mig4;
    }

    view_f f_view3{mig3};
    view_t depth_mig3{f_view3};
    std::cout << " depth\n";
    mig_algebraic_depth_rewriting_buffers( depth_mig3, ps );
    mig_algebraic_depth_rewriting_buffers( depth_mig3, ps );

    mockturtle::mig_network mig5 = depth_mig3;
    mig5 = cleanup_dangling( mig5 );
    mockturtle::depth_view depth_mig5{mig5};
    auto buffers2 = detail::compute_buffers( mig5 );

    exp( benchmark, size_b, depth_b, buffers1, buffers1 + size_b, experiments::abc_cec_sce_mig( depth_mig2, benchmark ), mig5.size(), depth_mig5.depth(), buffers2, buffers2 + mig5.size(), experiments::abc_cec_sce_mig( mig5, benchmark ), buffers1 - buffers2 );
  }

  exp.save();
  exp.table();
}

void example8()
{
  using namespace experiments;

  /* load database from file */
  mockturtle::mig_network mig_db;
  read_verilog( "db.v", mockturtle::verilog_reader( mig_db ) );

  mockturtle::mig4_npn_resynthesis_params ps;
  mockturtle::mig4_npn_resynthesis<mockturtle::mig_network> mig_resyn( mockturtle::detail::to_index_list( mig_db ), ps );

  ps.multiple_depth = true;
  mockturtle::mig4_npn_resynthesis<mockturtle::mig_network> mig_resyn2( mockturtle::detail::to_index_list( mig_db ), ps );

  ps.multiple_depth = false;
  ps.multiple_if = true;
  mockturtle::mig4_npn_resynthesis<mockturtle::mig_network> mig_resyn3( mockturtle::detail::to_index_list( mig_db ), ps );

  experiments::experiment<std::string, uint32_t, uint32_t, uint32_t, uint32_t, uint32_t, uint32_t, uint32_t, uint32_t, float, float> exp( "miglut_compare", "benchmark", "imbalance_factor_1", "size_1", "total_cost_1", "depth_1", "imbalance_factor_2", "size_2", "total_cost_2", "depth_2", "impr_if %", "impr_total_cost %" );

  for ( auto const& benchmark : sce_benchmarks() )
  {
    fmt::print( "[i] processing {}\n", benchmark );

    /* read aig */
    mockturtle::aig_network aig;
    if ( lorina::read_aiger( experiments::benchmark_sce_path( benchmark ), mockturtle::aiger_reader( aig ) ) != lorina::return_code::success )
    {
      std::cout << "ERROR 2" << std::endl;
      std::abort();
      return;
    }

    /* LUT map AIG into k-LUT network */
    auto klut = lut_map( aig, 4u );

    /* resynthesize klut with resynthesis strategies */
    mockturtle::mig_network mig;
    mig = mockturtle::node_resynthesis<mockturtle::mig_network>( klut, mig_resyn );
    mockturtle::depth_view mig_depth{mig};

    //mockturtle::mig_network mig2;
    //mig2 = mockturtle::node_resynthesis<mockturtle::mig_network>( klut, mig_resyn2 );
    //mockturtle::depth_view mig_depth2{mig2};

    mockturtle::mig_network mig3;
    mig3 = mockturtle::node_resynthesis<mockturtle::mig_network>( klut, mig_resyn3 );

    auto buffers1 = detail::compute_buffers( mig );
    //auto buffers2 = detail::compute_buffers( mig2 );
    auto buffers3 = detail::compute_buffers( mig3 );

    if ( buffers1 < buffers3 )
    {
      mig3 = mig;
      buffers3 = detail::compute_buffers( mig3 );
    }

    mockturtle::depth_view mig_depth3{mig3};

    exp( benchmark, buffers1, mig.size(), mig.size() + buffers1, mig_depth.depth(),
         buffers3, mig3.size(), mig3.size() + buffers3, mig_depth3.depth(), 100 * ( buffers1 - buffers3 ) / buffers1, 100 * ( int( mig.size() + buffers1 - mig3.size() - buffers3 ) ) / ( mig.size() + buffers1 ) );
  }

  exp.save();
  exp.table();
}

// compute cost original AIG
void example8_b()
{
  using namespace experiments;

  experiments::experiment<std::string, uint32_t, uint32_t, uint32_t, uint32_t> exp( "miglut_compare", "benchmark", "imbalance_factor_1", "size_1", "total_cost_1", "depth_1" );

  for ( auto const& benchmark : sce_benchmarks() )
  {
    fmt::print( "[i] processing {}\n", benchmark );

    /* read aig */
    mockturtle::aig_network aig;
    if ( lorina::read_aiger( experiments::benchmark_sce_path( benchmark ), mockturtle::aiger_reader( aig ) ) != lorina::return_code::success )
    {
      std::cout << "ERROR 2" << std::endl;
      std::abort();
      return;
    }

    mockturtle::depth_view aig_depth{aig};

    auto buffers1 = detail::compute_buffers_aig( aig );

    exp( benchmark, buffers1, aig.num_gates(), aig.num_gates() + buffers1, aig_depth.depth() );
    // buffers3, mig3.size(), mig3.size() + buffers3, mig_depth3.depth(), 100 * ( buffers1 - buffers3 ) / buffers1, 100 * ( int( mig.size() + buffers1 - mig3.size() - buffers3 ) ) / ( mig.size() + buffers1 ) );
  }

  exp.save();
  exp.table();
}

// new starting poing for MIGs
void example9()
{
  using namespace experiments;

  /* load database from file */
  mockturtle::mig_network mig_db;
  read_verilog( "db.v", mockturtle::verilog_reader( mig_db ) );

  /* option 1: XMG strategy using database from file */
  mockturtle::mig4_npn_resynthesis_params ps;

  ps.multiple_depth = true;
  mockturtle::mig4_npn_resynthesis<mockturtle::mig_network> mig_resyn2( mockturtle::detail::to_index_list( mig_db ), ps );

  experiments::experiment<std::string, uint32_t, uint32_t, uint32_t, uint32_t, bool, uint32_t, uint32_t, uint32_t, bool, int> exp( "miglut_compare", "benchmark", "LUTs", "MIG_1", "depth_1", "buffers_1", "eq cec1", "MIG_2", "depth_2", "buffers_2", "eq cec_2", "buffer_change" );

  for ( auto const& benchmark : sce_benchmarks() )
  {
    fmt::print( "[i] processing {}\n", benchmark );
    if ( benchmark == "hyp" )
      continue;

    /* read aig */
    mockturtle::aig_network aig;
    if ( lorina::read_aiger( experiments::benchmark_sce_path( benchmark ), mockturtle::aiger_reader( aig ) ) != lorina::return_code::success )
    {
      std::cout << "ERROR 2" << std::endl;
      std::abort();
      return;
    }

    /* LUT map AIG into k-LUT network */
    auto klut = lut_map( aig, 4u );

    mockturtle::mig_network mig2;
    mig2 = mockturtle::node_resynthesis<mockturtle::mig_network>( klut, mig_resyn2 );

    mockturtle::depth_view depth_mig2{mig2};
    auto const size_b = mig2.size();
    auto const depth_b = depth_mig2.depth();
    auto buffers1 = detail::compute_buffers( mig2 );

    mockturtle::depth_view depth_mig3{mig2};
    mig_algebraic_depth_rewriting( depth_mig3 );
    mig_algebraic_depth_rewriting( depth_mig3 );

    mig2 = depth_mig3;

    while ( true )
    {
      mockturtle::mig_network new_mig;
      mockturtle::depth_view depth_mig{mig2};
      auto const mig_depth_before = depth_mig.depth();
      auto const klut_size_before = klut.size();
      new_mig = mockturtle::node_resynthesis<mockturtle::mig_network>( klut, mig_resyn2 );
      mockturtle::depth_view depth_mig_new{new_mig};
      auto const new_klut = lut_map( new_mig );

      if ( new_klut.size() >= klut_size_before )
        break;
      if ( depth_mig_new.depth() > mig_depth_before )
        break;

      klut = new_klut;
      mig2 = new_mig;
    }

    mockturtle::depth_view depth_mig4{mig2};
    mig_algebraic_depth_rewriting( depth_mig4 );
    mig_algebraic_depth_rewriting( depth_mig4 );
    mig_algebraic_depth_rewriting( depth_mig4 );
    auto buffers2 = detail::compute_buffers( depth_mig4 );

    exp( benchmark, klut.size(), size_b, depth_b, buffers1, experiments::abc_cec_sce( mig2, benchmark ), depth_mig4.size(), depth_mig4.depth(), buffers2, experiments::abc_cec_sce( depth_mig2, benchmark ), buffers1 - buffers2 );
  }

  exp.save();
  exp.table();
}

// exact synthesis + depth + resub modified -- see effect of each step
void example10()
{
  using namespace experiments;

  /* load database from file */
  mockturtle::mig_network mig_db;
  read_verilog( "db.v", mockturtle::verilog_reader( mig_db ) );

  /* option 1: XMG strategy using database from file */
  mockturtle::mig4_npn_resynthesis_params ps;

  ps.multiple_depth = false;
  mockturtle::mig4_npn_resynthesis<mockturtle::mig_network> mig_resyn( mockturtle::detail::to_index_list( mig_db ), ps );

  ps.multiple_depth = true;
  ps.multiple_if = true;
  mockturtle::mig4_npn_resynthesis<mockturtle::mig_network> mig_resyn2( mockturtle::detail::to_index_list( mig_db ), ps );

  experiments::experiment<std::string, uint32_t, uint32_t, uint32_t, uint32_t, uint32_t, uint32_t, uint32_t, uint32_t, int, uint32_t, uint32_t, uint32_t, uint32_t, int, uint32_t, uint32_t, uint32_t, uint32_t, int, bool> exp( "miglut_compare",
                                                                                                                                                                                                                                 "benchmark", "MIG_b", "depth_b", "buffers_b", "cost_b", "MIG_1", "depth_1", "buffers_1", "cost_1", "impro_1:b", "MIG_2", "depth_2", "buffers_2", "cost_2", "impro_2:1",
                                                                                                                                                                                                                                 "MIG_3", "depth_3", "buffers_3", "cost_3", "impro_3:2", "eq cec" );
  for ( auto const& benchmark : sce_benchmarks() )
  {
    fmt::print( "[i] processing {}\n", benchmark );

    /* read aig */
    mockturtle::aig_network aig;
    if ( lorina::read_aiger( experiments::benchmark_sce_path( benchmark ), mockturtle::aiger_reader( aig ) ) != lorina::return_code::success )
    {
      std::cout << "ERROR 2" << std::endl;
      std::abort();
      return;
    }

    /* LUT map AIG into k-LUT network */
    auto klut = lut_map( aig, 4u );

    mockturtle::mig_network mig1;
    mig1 = mockturtle::node_resynthesis<mockturtle::mig_network>( klut, mig_resyn );
    mockturtle::depth_view depth_mig1{mig1};

    //using view_t = mockturtle::depth_view<mockturtle::fanout_view<mockturtle::mig_network>>;
    using view_f = mockturtle::fanout_view<mockturtle::depth_view<mockturtle::mig_network>>;
    /*auto mig22 = mig1;
    std::cout << " fanout stats original MIG exact: \n";
    view_f f_view11{mig22};

    float sum_fanout = 0;
    auto max_fanout = 0;
    auto counter = 0;
    //auto index = 0u;
    f_view11.foreach_gate( [&]( auto const& n, auto i ) {
      if ( f_view11.fanout_size( n ) > max_fanout )
        {
          max_fanout = f_view11.fanout_size( n );
          //index = f_view11.node_to_index(n);
        }
      sum_fanout = sum_fanout + f_view11.fanout_size( n );
      if ( f_view11.fanout_size( n ) > 4 )
        counter++;
      return true;
    } );

    float avg_fanout = sum_fanout / f_view11.num_gates();

    std::cout << " the max fanout is = " << max_fanout << std::endl;
    std::cout << " the avg. fanout is = " << avg_fanout << std::endl;
    std::cout << " fanout larger than 4 = " << counter << std::endl;
    
    // the end 
    */

    auto const size_a = mig1.num_gates();
    auto const depth_a = depth_mig1.depth();
    auto buffers_a = detail::compute_buffers( mig1 );
    
    mockturtle::mig_network mig2 = mig1;
    ///mockturtle::cut_rewriting_params ps3;
    //ps3.cut_enumeration_ps.cut_size = 4;
    //ps3.verbose = true;
    //std::cout << " cut rewriting ... \n";
    //cut_rewriting_with_compatibility_graph( mig2, mig_resyn2, ps3, nullptr, detail::if_cost<mockturtle::depth_view<mockturtle::mig_network>>() );
    //mig2 = mig2_d;
    //mig2 = cleanup_dangling( mig2 );
    //if ( detail::compute_buffers( mig2 ) > buffers_a )
    //mig2 = mig1;

    mig2 = mockturtle::node_resynthesis<mockturtle::mig_network>( klut, mig_resyn2 );
    mig2 = cleanup_dangling( mig2 );
    mockturtle::mig_algebraic_depth_rewriting_params ps2;
    ps2.strategy = mockturtle::mig_algebraic_depth_rewriting_params::aggressive;
    ps2.allow_area_increase = false; 
    mockturtle::depth_view depth_mig2{mig2};
    
    //mig_algebraic_depth_rewriting( depth_mig1);
    //using view_t = mockturtle::depth_view<mockturtle::fanout_view<mockturtle::mig_network>>;
    
    /*mig22 = mig2;
    std::cout << " fanout stats MIG exact: \n";
    view_f f_view22{mig22};

    sum_fanout = 0;
    max_fanout = 0;
    counter = 0;
    f_view22.foreach_gate( [&]( auto const& n, auto i ) {
      if ( f_view22.fanout_size( n ) > max_fanout )
        max_fanout = f_view22.fanout_size( n );
      sum_fanout = sum_fanout + f_view22.fanout_size( n );
      if ( f_view22.fanout_size( n ) > 4 )
        counter++;
      return true;
    } );

    avg_fanout = sum_fanout / f_view22.num_gates();

    std::cout << " the max fanout is = " << max_fanout << std::endl;
    std::cout << " the avg. fanout is = " << avg_fanout << std::endl;
    std::cout << " fanout larger than 4 = " << counter << std::endl;
    // the end
    */
    mig2 = depth_mig2; 
    auto const size_b = mig2.num_gates();
    auto const depth_b = depth_mig2.depth();
    auto buffers_b = detail::compute_buffers( mig2 );
    //std::cout << size_b << " " << depth_b << " " << buffers_b << std::endl;

    //view_f depth_view{mig2};
    view_f mig_f{depth_mig2};
    ps2.strategy = mockturtle::mig_algebraic_depth_rewriting_params::aggressive;
    ps2.allow_area_increase = true; 
    std::cout << " depth optimization ... \n";
    mig_algebraic_depth_rewriting_buffers( mig_f, ps2 );

    mockturtle::mig_network mig5 = mig_f;
    mig5 = cleanup_dangling( mig5 );

    /*auto mig55 = mig5;
    // fanout stats
    std::cout << " fanout stats MIG depth: \n";

    view_f f_view{mig55};

    sum_fanout = 0;
    max_fanout = 0;
    counter = 0;
    f_view.foreach_gate( [&]( auto const& n, auto i ) {
      if ( f_view.fanout_size( n ) > max_fanout )
        max_fanout = f_view.fanout_size( n );
      sum_fanout = sum_fanout + f_view.fanout_size( n );
      if ( f_view.fanout_size( n ) > 4 )
        counter++;
      return true;
    } );

    avg_fanout = sum_fanout / f_view.num_gates();

    std::cout << " the max fanout is = " << max_fanout << std::endl;
    std::cout << " the avg. fanout is = " << avg_fanout << std::endl;
    std::cout << " fanout larger than 4 = " << counter << std::endl;

    // the end
    */

    mockturtle::depth_view depth_mig5{mig5};

    auto const size_c = mig5.num_gates();
    auto const depth_c = depth_mig5.depth();
    auto buffers_c = detail::compute_buffers( mig5 );

    mockturtle::resubstitution_params ps;
    ps.max_divisors = 300;

    //mockturtle::depth_view fanout_view3{mig5};
    //view_f resub_view{fanout_view3};
    std::cout << " resub ... \n";
    mig_feasible_resubstitution( mig5, ps );

    mig5 = cleanup_dangling( mig5 );
    mockturtle::depth_view depth_mig3{mig5};

    //std::cout << " fanout stats MIG resub: \n";
    /*mig55 = mig5;
    view_f f_view2{mig55};

    sum_fanout = 0;
    max_fanout = 0;
    counter = 0;
    auto index = 0;
    f_view2.foreach_gate( [&]( auto const& n, auto i ) {
      if ( f_view2.fanout_size( n ) > max_fanout )
        {
          max_fanout = f_view2.fanout_size( n );
          index = f_view2.node_to_index(n);
        }
      sum_fanout = sum_fanout + f_view2.fanout_size( n );
      if ( f_view2.fanout_size( n ) > 4 )
        counter++;
      return true;
    } );

    avg_fanout = sum_fanout / f_view2.num_gates();

    std::cout << " the max fanout is = " << max_fanout << std::endl;
    std::cout << " the avg. fanout is = " << avg_fanout << std::endl;
    std::cout << " fanout larger than 4 = " << counter << std::endl;
    std::cout << " node = " << index << std::endl;

    // the end
    */

    view_f mig_f2{depth_mig3};
    std::cout << " depth optimization ... \n";
    mig_algebraic_depth_rewriting_buffers( mig_f2, ps2 );
    mig5 = mig_f2; 
    mig5 = cleanup_dangling( mig5 );

    mig_feasible_resubstitution( mig5, ps );

    mig5 = cleanup_dangling( mig5 );
    
    mockturtle::depth_view mig5_d{mig5};
    auto const size_d = mig5.num_gates();
    auto const depth_d = mig5_d.depth();
    auto buffers_d = detail::compute_buffers( mig5 );

    //mockturtle::write_verilog( mig5, fmt::format( "{}_mig.v", benchmark ) );
    exp( benchmark, size_a, depth_a, buffers_a, size_a + buffers_a, size_b, depth_b, buffers_b, size_b + buffers_b, size_a + buffers_a - size_b - buffers_b, size_c, depth_c, buffers_c, size_c + buffers_c, size_b + buffers_b - size_c - buffers_c,
         size_d, depth_d, buffers_d, size_d + buffers_d, size_c + buffers_c - size_d - buffers_d, experiments::abc_cec_sce( mig2, benchmark ) );
  }

  exp.save();
  exp.table();
}

void example_aqfp()
{
  using namespace experiments;

  /* load database from file */
  mockturtle::mig_network mig_db;
  read_verilog( "db.v", mockturtle::verilog_reader( mig_db ) );

  /* option 1: XMG strategy using database from file */
  mockturtle::mig4_npn_resynthesis_params ps;

  ps.multiple_depth = false;
  mockturtle::mig4_npn_resynthesis<mockturtle::mig_network> mig_resyn( mockturtle::detail::to_index_list( mig_db ), ps );

  ps.multiple_depth = false;
  ps.multiple_if = false;
  mockturtle::mig4_npn_resynthesis<mockturtle::mig_network> mig_resyn2( mockturtle::detail::to_index_list( mig_db ), ps );

  experiments::experiment<std::string, uint32_t, uint32_t, uint32_t, uint32_t, uint32_t, uint32_t, uint32_t, uint32_t, int, uint32_t, uint32_t, uint32_t, uint32_t, int, uint32_t, uint32_t, uint32_t, uint32_t, int, bool> exp( "miglut_compare",
                                                                                                                                                                                                                                 "benchmark", "MIG_b", "depth_b", "buffers_b", "cost_b", "MIG_1", "depth_1", "buffers_1", "cost_1", "impro_1:b", "MIG_2", "depth_2", "buffers_2", "cost_2", "impro_2:1",
                                                                                                                                                                                                                                 "MIG_3", "depth_3", "buffers_3", "cost_3", "impro_3:2", "eq cec" );
  for ( auto const& benchmark : aqfp_benchmarks() )
  {
    fmt::print( "[i] processing {}\n", benchmark );

    /* read aig */
    mockturtle::aig_network aig;
    if ( lorina::read_aiger( experiments::benchmark_aqfp_path( benchmark ), mockturtle::aiger_reader( aig ) ) != lorina::return_code::success )
    {
      std::cout << "ERROR 2" << std::endl;
      std::abort();
      return;
    }

    /* LUT map AIG into k-LUT network */
    auto klut = lut_map( aig, 4u );

    mockturtle::mig_network mig1;
    mig1 = mockturtle::node_resynthesis<mockturtle::mig_network>( klut, mig_resyn );
    mockturtle::depth_view depth_mig1{mig1};

    using view_t = mockturtle::depth_view<mockturtle::fanout_view<mockturtle::mig_network>>;
    using view_f = mockturtle::fanout_view<mockturtle::mig_network>;

    auto const size_a = mig1.num_gates();
    auto const depth_a = depth_mig1.depth();
    auto buffers_a = detail::compute_buffers( mig1 );

    mockturtle::mig_network mig2;
    mig2 = mockturtle::node_resynthesis<mockturtle::mig_network>( klut, mig_resyn2 );
    mockturtle::depth_view depth_mig2{mig2};

    using view_t = mockturtle::depth_view<mockturtle::fanout_view<mockturtle::mig_network>>;
    using view_f = mockturtle::fanout_view<mockturtle::mig_network>;

    auto const size_b = mig2.num_gates();
    auto const depth_b = depth_mig2.depth();
    auto buffers_b = detail::compute_buffers( mig2 );

    view_f fanout_view{mig2};
    view_t depth_view4{fanout_view};
    mockturtle::mig_algebraic_depth_rewriting_params ps2;
    ps2.strategy = mockturtle::mig_algebraic_depth_rewriting_params::aggressive;
    ps2.allow_area_increase = false;
    mig_algebraic_depth_rewriting( depth_view4, ps2 );

    mockturtle::mig_network mig5 = depth_view4;
    mig5 = cleanup_dangling( mig5 );

    auto mig55 = mig5;

    mockturtle::depth_view depth_mig5{mig5};

    auto const size_c = mig5.num_gates();
    auto const depth_c = depth_mig5.depth();
    auto buffers_c = detail::compute_buffers( mig5 );

    mockturtle::resubstitution_params ps;
    ps.max_divisors = 150;

    view_f fanout_view3{mig5};
    view_t resub_view{fanout_view3};
    mig_resubstitution( resub_view, ps );

    mig5 = cleanup_dangling( mig5 );

    mockturtle::akers_resynthesis<mockturtle::mig_network> resyn;
    mockturtle::refactoring( mig5, resyn );
    mig5 = cleanup_dangling( mig5 );

    mockturtle::depth_view depth_mig3{mig5};

    mig_algebraic_depth_rewriting( depth_mig3, ps2 );
    mig5 = depth_mig3;
    mig5 = cleanup_dangling( mig5 );

    //mockturtle::refactoring( mig5, resyn );
    //mig5 = cleanup_dangling( mig5 );

    mockturtle::depth_view depth_mig55{mig5};
    auto const size_d = mig5.num_gates();
    auto const depth_d = depth_mig55.depth();
    auto buffers_d = detail::compute_buffers( mig5 );

    //mockturtle::write_verilog( mig5, fmt::format( "{}_mign_aqfp.v", benchmark ) );

    exp( benchmark, size_a, depth_a, buffers_a, size_a + buffers_a, size_b, depth_b, buffers_b, size_b + buffers_b, size_a + buffers_a - size_b - buffers_b, size_c, depth_c, buffers_c, size_c + buffers_c, size_b + buffers_b - size_c - buffers_c,
         size_d, depth_d, buffers_d, size_d + buffers_d, size_c + buffers_c - size_d - buffers_d, experiments::abc_cec_aqfp( mig2, benchmark ) );
  }

  exp.save();
  exp.table();
}

void example_debug()
{

  mockturtle::mig_network mig;
  auto benchmark = "c7552_mig";
  if ( read_verilog( "c7552_mig_debug.v", mockturtle::verilog_reader( mig ) ) != lorina::return_code::success )
  {
    std::cout << "ERROR 2" << std::endl;
    std::abort();
    return;
  }
  using view_t = mockturtle::depth_view<mockturtle::fanout_view<mockturtle::mig_network>>;
  using view_f = mockturtle::fanout_view<mockturtle::mig_network>;

  view_f fanout_view{mig};
  view_t resub_view{fanout_view};

  mockturtle::resubstitution_params ps;
  ps.max_inserts = 2;
  mig_resubstitution( resub_view, ps );
  mig = cleanup_dangling( mig );

  mockturtle::write_verilog( mig, fmt::format( "{}_debug_resub.v", benchmark ) );
}

void example_refactoring()
{
  using namespace experiments;

  experiments::experiment<std::string, uint32_t, uint32_t, uint32_t, uint32_t, bool, uint32_t, uint32_t, uint32_t, uint32_t, bool, int> exp( "mig_refactoring", "benchmark",
                                                                                                                                             "MIG_1", "depth_1", "buffers_1", "cost_1", "eq cec1", "MIG_2", "depth_2", "buffers_2", "cost_2", "eq cec_2", "buffer_change" );

  for ( auto const& benchmark : sce_benchmarks() )
  {
    fmt::print( "[i] processing {}\n", benchmark );
    if ( benchmark == "hyp" )
      continue;

    mockturtle::mig_network mig;
    if ( read_verilog( experiments::benchmark_sce_mig_path( benchmark ), mockturtle::verilog_reader( mig ) ) != lorina::return_code::success )
    {
      std::cout << "ERROR 2" << std::endl;
      std::abort();
      return;
    }

    mockturtle::depth_view depth_mig1{mig};
    auto const size_b = mig.num_gates();
    auto const depth_b = depth_mig1.depth();
    auto buffers1 = detail::compute_buffers( mig );
    auto mig2 = mig;

    mockturtle::akers_resynthesis<mockturtle::mig_network> resyn;
    mockturtle::refactoring( mig2, resyn );
    mig2 = cleanup_dangling( mig2 );

    mockturtle::depth_view depth_mig2{mig2};

    using view_t = mockturtle::depth_view<mockturtle::fanout_view<mockturtle::mig_network>>;
    using view_f = mockturtle::fanout_view<mockturtle::mig_network>;

    mockturtle::mig_algebraic_depth_rewriting_params ps;
    ps.strategy = mockturtle::mig_algebraic_depth_rewriting_params::aggressive;

    view_f f_view3{mig2};
    view_t depth_mig3{f_view3};
    mig_algebraic_depth_rewriting_buffers( depth_mig3, ps );
    mig_algebraic_depth_rewriting_buffers( depth_mig3, ps );

    mockturtle::mig_network mig5 = depth_mig3;
    mig5 = cleanup_dangling( mig5 );
    mockturtle::depth_view depth_mig5{mig5};
    auto buffers2 = detail::compute_buffers( mig5 );

    exp( benchmark, size_b, depth_b, buffers1, buffers1 + size_b, experiments::abc_cec_sce_mig( depth_mig2, benchmark ), mig5.num_gates(), depth_mig5.depth(), buffers2, buffers2 + mig5.num_gates(), experiments::abc_cec_sce_mig( mig2, benchmark ), buffers1 + size_b - mig5.num_gates() - buffers2 );
  }
  exp.save();
  exp.table();
}

int main()
{
  example10();
  return 0;
}
