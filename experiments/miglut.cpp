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
#include <mockturtle/algorithms/cleanup.hpp>
#include <mockturtle/algorithms/collapse_mapped.hpp>
#include <mockturtle/algorithms/cut_rewriting.hpp>
#include <mockturtle/algorithms/detail/database_generator.hpp>
#include <mockturtle/algorithms/lut_mapping.hpp>
#include <mockturtle/algorithms/mig_algebraic_rewriting.hpp>
#include <mockturtle/algorithms/mig_feasible_resub.hpp>
#include <mockturtle/algorithms/node_resynthesis.hpp>
#include <mockturtle/algorithms/node_resynthesis/exact.hpp>
#include <mockturtle/algorithms/node_resynthesis/mig4_npn.hpp>
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
    auto const size_b = mig2.size();
    auto const depth_b = depth_mig2.depth();
    auto buffers1 = detail::compute_buffers( mig2 );

    mig_algebraic_depth_rewriting( depth_mig2 );
    auto buffers2 = detail::compute_buffers( depth_mig2 );

    exp( benchmark, klut.size(), size_b, depth_b, buffers1, experiments::abc_cec_sce( mig2, benchmark ), depth_mig2.size(), depth_mig2.depth(), buffers2, experiments::abc_cec_sce( depth_mig2, benchmark ), buffers1 - buffers2 );
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
    ps.max_divisors = 300;
    mig_feasible_resubstitution( resub_view, ps );

    mig3 = cleanup_dangling( mig3 );
    mockturtle::depth_view depth_mig3{mig3};
    auto buffers2 = detail::compute_buffers( mig3 );

    exp( benchmark, klut.size(), size_b, depth_b, buffers1, experiments::abc_cec_sce( depth_mig2, benchmark ), mig3.size(), depth_mig3.depth(), buffers2, experiments::abc_cec_sce( mig3, benchmark ), buffers1 - buffers2 );
  }

  exp.save();
  exp.table();
}

// example 7 but saturation of results
void example7_bis()
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
    mig_algebraic_depth_rewriting( depth_mig2 );
    mig_algebraic_depth_rewriting( depth_mig2 );

    mockturtle::mig_network mig3 = depth_mig2;
    mig3 = cleanup_dangling( mig3 );
    mockturtle::mig_network mig4 = depth_mig2;
    mig4 = cleanup_dangling( mig4 );

    auto const size_b = mig3.size();
    auto const depth_b = depth_mig2.depth();
    auto buffers1 = detail::compute_buffers( mig3 );

    using view_t = mockturtle::depth_view<mockturtle::fanout_view<mockturtle::mig_network>>;
    using view_f = mockturtle::fanout_view<mockturtle::mig_network>;
    
    mockturtle::resubstitution_params ps;
    ps.max_divisors = 300;

    auto original_buffer = detail::compute_buffers( mig3 );
    auto i = 0u; 
    while ( true )
    {
      if (i > 30)
      break; 
      i++;
      view_f fanout_view{mig4};
      view_t resub_view{fanout_view};
      mig_feasible_resubstitution( resub_view, ps );

      mig4 = cleanup_dangling( mig4 );
      if (detail::compute_buffers( mig4 ) >= original_buffer )
      break;
      mig3 = mig4; 
      //original_buffer = detail::compute_buffers( mig4 );
    }

    mockturtle::depth_view depth_mig3{mig3};
    auto buffers2 = detail::compute_buffers( mig3 );

    exp( benchmark, klut.size(), size_b, depth_b, buffers1, experiments::abc_cec_sce( depth_mig2, benchmark ), mig3.size(), depth_mig3.depth(), buffers2, experiments::abc_cec_sce( mig3, benchmark ), buffers1 - buffers2 );
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

  experiments::experiment<std::string, uint32_t, uint32_t, uint32_t, uint32_t, uint32_t, uint32_t, int, int> exp( "miglut_compare", "benchmark", "imbalance_factor1", "total_cost_1", "imbalance_factor2", "total_cost_2", "imbalance_factor3", "total_cost_3", "change_1:3", "change_2:3" );

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

    mockturtle::mig_network mig2;
    mig2 = mockturtle::node_resynthesis<mockturtle::mig_network>( klut, mig_resyn2 );

    mockturtle::mig_network mig3;
    mig3 = mockturtle::node_resynthesis<mockturtle::mig_network>( klut, mig_resyn3 );

    auto buffers1 = detail::compute_buffers( mig );
    auto buffers2 = detail::compute_buffers( mig2 );
    auto buffers3 = detail::compute_buffers( mig3 );

    exp( benchmark, buffers1, mig.size() + buffers1, buffers2, mig2.size() + buffers2,
         buffers3, mig3.size() + buffers3, buffers1 - buffers3, buffers2 - buffers3 );
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
    auto buffers2 = detail::compute_buffers( depth_mig4);

    exp( benchmark, klut.size(), size_b, depth_b, buffers1, experiments::abc_cec_sce( mig2, benchmark ), depth_mig4.size(), depth_mig4.depth(), buffers2, experiments::abc_cec_sce( depth_mig2, benchmark ), buffers1 - buffers2 );
  }

  exp.save();
  exp.table();
}

// debug is example 3
int main()
{
  example9();
  return 0;
}
