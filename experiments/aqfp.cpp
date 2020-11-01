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
#include <mockturtle/algorithms/mig_algebraic_rewriting_splitters.hpp>
#include <mockturtle/algorithms/mig_feasible_resub.hpp>
#include <mockturtle/algorithms/mig_resub.hpp>
#include <mockturtle/algorithms/mig_resub_splitters.hpp>
#include <mockturtle/algorithms/node_resynthesis.hpp>
#include <mockturtle/algorithms/node_resynthesis/akers.hpp>
#include <mockturtle/algorithms/node_resynthesis/exact.hpp>
#include <mockturtle/algorithms/node_resynthesis/mig4_npn.hpp>
#include <mockturtle/algorithms/node_resynthesis/mig_npn.hpp>
#include <mockturtle/algorithms/refactoring.hpp>
#include <mockturtle/io/aiger_reader.hpp>
#include <mockturtle/io/blif_reader.hpp>
#include <mockturtle/io/index_list.hpp>
#include <mockturtle/io/verilog_reader.hpp>
#include <mockturtle/io/write_verilog.hpp>
#include <mockturtle/networks/aig.hpp>
#include <mockturtle/views/depth_view.hpp>
#include <mockturtle/views/fanout_limit_view.hpp>
#include <mockturtle/views/fanout_view.hpp>
#include <mockturtle/views/mapping_view.hpp>

#include <fmt/format.h>

#include <string>
#include <vector>

/*namespace detail
{

template<class Ntk>
struct jj_cost
{
  uint32_t operator()( Ntk const& ntk, mockturtle::node<Ntk> const& n ) const
  {
    uint32_t cost = 0;
    if ( ntk.fanout_size( n ) == 1 )
      cost = ntk.fanout_size( n );
    else if ( ntk.fanout_size( n ) <= 4 )
      cost = 3;
    else
      cost = 11;
    return cost;
  }
};

template<class Ntk>
int used_as_po( Ntk const& ntk, mockturtle::node<Ntk> const& n )
{
  int count = 0;
  ntk.foreach_po( [&]( auto s ) {
    if ( ntk.get_node( s ) == n )
      count++;
    return true;
  } );
  return count;
}

template<class Ntk>
struct fanout_cost_depth_local
{
  uint32_t operator()( Ntk const& ntk, mockturtle::node<Ntk> const& n ) const
  {
    uint32_t cost = 0;
    if ( ntk.is_pi( n ) )
      cost = 0;
    else if ( ntk.fanout_size( n ) + used_as_po( n ) == 1 )
      cost = 1;
    else if ( ( ntk.fanout_size( n ) + used_as_po( n ) > 1 ) && ( ntk.fanout_size( n ) + used_as_po( n ) < 5 ) )
      cost = 2;
    else if ( ( ntk.fanout_size( n ) + used_as_po( n ) > 4 ) ) //&& ( ntk.fanout_size( n ) < 17 ) )
      cost = 3;
    return cost;
  }
};

template<class Ntk>
uint32_t compute_maxfanout( Ntk ntk )
{
  auto max_fanout = 0;
  ntk.foreach_gate( [&]( auto const& n ) {
    if ( ntk.fanout_size( n ) + used_as_po( n ) > max_fanout )
      max_fanout = ntk.fanout_size( n ) + used_as_po( n );
    return true;
  } );
  return max_fanout;
}

template<class Ntk>
int compute_buffers( Ntk mig )
{
  mockturtle::depth_view_params ps_d;
  mockturtle::depth_view depth_mig{mig, detail::fanout_cost_depth_local<Ntk>(), ps_d};
  std::vector<int> buffers( mig.size(), 0 );
  int number_buff = 0;

  mig.foreach_gate( [&]( auto f ) {
    auto main_depth = depth_mig.level( f );
    mig.foreach_fanin( f, [&]( auto const& s ) {
      if ( mig.is_pi( mig.get_node( s ) ) )
        return true;
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

template<class Ntk>
int cost( Ntk ntk, mockturtle::node<Ntk> const& n )
{
  auto cost = 0;
  if ( ( ntk.fanout_size( n ) + used_as_po( n ) > 1 ) && ( ntk.fanout_size( n ) + used_as_po( n ) < 5 ) )
    cost = 1;
  else if ( ( ntk.fanout_size( n ) + used_as_po( n ) > 4 ) ) //&& ( ntk.fanout_size( n ) < 17 ) )
    cost = 2;
  return cost;
}

template<class Ntk>
int compute_buffers_not_shared( Ntk mig )
{
  mockturtle::depth_view_params ps_d;
  mockturtle::depth_view depth_mig{mig, detail::fanout_cost_depth_local<Ntk>(), ps_d};
  std::vector<std::vector<int>> buffers( mig.size() );
  int number_buff = 0;

  mig.foreach_gate( [&]( auto f ) {
    auto main_depth = depth_mig.level( f );
    auto index2 = mig.node_to_index( f );
    mig.foreach_fanin( f, [&]( auto const& s ) {
      auto index = mig.node_to_index( mig.get_node( s ) );
      if ( index == 0 )
        return true;
      if ( is_pi( ntk.get_node( s ) ) )  /* this will not balance the pis
        return true;
      int diff = main_depth - 1 - depth_mig.level( mig.get_node( s ) ) - detail::cost( mig, f );
      for ( auto g = 0u; g < diff; g++ )
      {
        if ( g < buffers[index].size() )
          buffers[index][g]++;
        else
          buffers[index].push_back( 1 );
      }
      return true;
    } );
  } );

  // balacing pos
  auto total_depth = depth_mig.depth();
  mig.foreach_po( [&]( auto s ) {
    if ( depth_mig.level( mig.get_node( s ) ) == total_depth )
      return true;
    auto index = mig.node_to_index( mig.get_node( s ) );
    if ( index == 0 )
      return true;
    int diff = total_depth - depth_mig.level( mig.get_node( s ) ); // - buffers[index];
    for ( auto g = 0u; g < diff; g++ )
    {
      if ( g < buffers[index].size() )
        buffers[index][g]++;
      else
        buffers[index].push_back( 1 );
    }
    return true;
  } );

  for ( auto h = 0u; h < buffers.size(); h++ )
  {
    if ( buffers[h].size() == 0 )
      continue;
    number_buff = number_buff + buffers[h].size();
    for ( auto g = 0; g < buffers[h].size(); g++ )
    {
      int x = buffers[h][g] / 4 + ( buffers[h][g] % 4 != 0 );
      number_buff = number_buff + x - 1;
    }
  }
  return number_buff;
}

template<class Ntk>
uint32_t JJ_number_final( Ntk ntk )
{
  auto JJ = 0;
  ntk.foreach_gate( [&]( auto const& n ) {
    if ( ntk.fanout_size( n ) + used_as_po( n ) == 1 )
      JJ = JJ + 6;
    else if ( ntk.fanout_size( n ) + used_as_po( n ) <= 4 )
      JJ = JJ + 8;
    else if ( ntk.fanout_size( n ) + used_as_po( n ) <= 16 )
      JJ = JJ + 16;
    // this should not happen in the new limit fanout view
    else if ( ntk.fanout_size( n ) + used_as_po( n ) <= 20 )
      JJ = JJ + 16 + 8;
    else if ( ntk.fanout_size( n ) + used_as_po( n ) <= 32 )
      JJ = JJ + 16 * 2;
    else if ( ntk.fanout_size( n ) + used_as_po( n ) <= 36 )
      JJ = JJ + 16 * 2 + 8;
    else if ( ntk.fanout_size( n ) + used_as_po( n ) <= 48 )
      JJ = JJ + 16 * 3;
    return true;
  } );
  auto buffers = compute_buffers_not_shared( ntk );
  JJ = JJ + buffers * 2;
  return JJ;
}

template<class Ntk>
uint32_t compute_maxfanout_inputs( Ntk ntk )
{
  auto max_fanout = 0;
  ntk.foreach_pi( [&]( auto const& n, auto i ) {
    if ( ntk.fanout_size( n ) + used_as_po( n ) > max_fanout )
      max_fanout = ntk.fanout_size( n ) + used_as_po( n );
    return true;
  } );
  return max_fanout;
}

template<class Ntk>
uint32_t compute_fanout4_inputs( Ntk ntk )
{
  auto fanout4 = 0;
  ntk.foreach_pi( [&]( auto const& n, auto i ) {
    if ( ntk.fanout_size( n ) + used_as_po( n ) > 16 )
      fanout4++;
    return true;
  } );
  return fanout4;
}

template<class Ntk>
uint32_t compute_fanout4( Ntk ntk )
{
  auto fanout4 = 0;
  ntk.foreach_gate( [&]( auto const& n, auto i ) {
    if ( ntk.fanout_size( n ) + used_as_po( n ) > 16 )
      fanout4++;
    return true;
  } );
  return fanout4;
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

using view_t = mockturtle::depth_view<mockturtle::fanout_view<mockturtle::mig_network>>;
using view_f = mockturtle::fanout_view<mockturtle::mig_network>;

void example_aqfp()
{
  using namespace experiments;

  /* load database from file 
  mockturtle::mig_network mig_db;
  read_verilog( "db.v", mockturtle::verilog_reader( mig_db ) );

  /* option 1: XMG strategy using database from file 
  mockturtle::mig4_npn_resynthesis_params ps;
  mockturtle::mig4_npn_resynthesis<mockturtle::mig_network> mig_resyn( mockturtle::detail::to_index_list( mig_db ), ps );

  experiments::experiment<std::string, uint32_t, uint32_t, uint32_t, uint32_t, float, float, bool> exp( "mig_aqfp", "benchmark", "size MIG", "depth", "size MIG our", "depth our", "impro. size", "impro. depth ", "eq cec" );

  std::map<std::string, std::tuple<uint32_t, uint32_t>> opt_aig;
  opt_aig.emplace( "c432", std::make_tuple( 2784, 36 ) );
  opt_aig.emplace( "c499", std::make_tuple( 4982, 27 ) );
  opt_aig.emplace( "c880", std::make_tuple( 5104, 35 ) );
  opt_aig.emplace( "c1355", std::make_tuple( 4790, 25 ) );
  opt_aig.emplace( "c1908", std::make_tuple( 6164, 41 ) );
  opt_aig.emplace( "c2670", std::make_tuple( 11574, 26 ) );
  opt_aig.emplace( "c3540", std::make_tuple( 11618, 58 ) );
  opt_aig.emplace( "c5315", std::make_tuple( 22860, 49 ) );
  opt_aig.emplace( "c6288", std::make_tuple( 52806, 176 ) );
  opt_aig.emplace( "c7552", std::make_tuple( 23834, 52 ) );

  std::map<std::string, std::tuple<uint32_t, uint32_t>> soa_mig;
  soa_mig.emplace( "c432", std::make_tuple( 3072, 39 ) );
  soa_mig.emplace( "c880", std::make_tuple( 5914, 30 ) );
  soa_mig.emplace( "c1908", std::make_tuple( 6818, 38 ) );
  soa_mig.emplace( "c5315", std::make_tuple( 30910, 40 ) );
  soa_mig.emplace( "c6288", std::make_tuple( 25870, 94 ) );

  std::map<std::string, std::tuple<uint32_t, uint32_t>> soa_mig_sd;
  soa_mig_sd.emplace( "c17", std::make_tuple( 6, 3 ) );
  soa_mig_sd.emplace( "c432", std::make_tuple( 121, 26 ) );
  soa_mig_sd.emplace( "c880", std::make_tuple( 274, 18 ) );
  soa_mig_sd.emplace( "c1908", std::make_tuple( 263, 21 ) );
  soa_mig_sd.emplace( "c5315", std::make_tuple( 1248, 23 ) );
  soa_mig_sd.emplace( "c6288", std::make_tuple( 984, 48 ) );

  for ( auto const& benchmark : aqfp_benchmarks() )
  {
    fmt::print( "[i] processing {}\n", benchmark );

    /* read aig 
    mockturtle::aig_network aig;
    if ( lorina::read_aiger( experiments::benchmark_aqfp_path( benchmark ), mockturtle::aiger_reader( aig ) ) != lorina::return_code::success )
    {
      std::cout << "ERROR 2" << std::endl;
      std::abort();
      return;
    }

    mockturtle::depth_view_params ps_d;
    mockturtle::depth_view aig_d{aig};
    mockturtle::depth_view aig_d_s{aig, detail::fanout_cost_depth_local<mockturtle::aig_network>(), ps_d};

    //auto const size_a = aig.num_gates();
    //auto const depth_a = aig_d.depth();
    auto const JJ_a = std::get<0>( soa_mig_sd[benchmark] );
    auto const depth_a_splitters = std::get<1>( soa_mig_sd[benchmark] );
    //auto const max_fanout_a = detail::compute_maxfanout( aig );
    //auto const node_larger_16_a = detail::compute_fanout4( aig );

    /* LUT map AIG into k-LUT network 
    auto klut = lut_map( aig, 4u );

    mockturtle::mig_network mig1;
    mig1 = mockturtle::node_resynthesis<mockturtle::mig_network>( klut, mig_resyn );
    mockturtle::depth_view mig1_d{mig1};
    mockturtle::depth_view mig1_d_s{mig1, detail::fanout_cost_depth_local<mockturtle::mig_network>(), ps_d};

    /*auto const size_a = mig1.num_gates();
    auto const depth_a = mig1_d.depth();
    auto const JJ_a = JJ_number_final(mig1);
    auto const depth_a_splitters = mig1_d_s.depth();
    auto const max_fanout_a = detail::compute_maxfanout( mig1 );
    auto const node_larger_16_a = detail::compute_fanout4( mig1 );
    std::cout << " cut rewriting ... \n";
    mockturtle::cut_rewriting_params ps;
    ps.cut_enumeration_ps.cut_size = 4;
    auto i = 0;
    while ( i < 10 )
    {
      i++;
      mig1 = cut_rewriting( mig1, mig_resyn, ps, nullptr );
      //mig1 = cut_rewriting<mockturtle::mig_network, decltype( mig_resyn ), mockturtle::fanout_cost<mockturtle::mig_network>>( mig1, mig_resyn, ps, nullptr );
      //cut_rewriting_with_compatibility_graph( mig1, mig_resyn, ps, nullptr, detail::fanout_cost<mockturtle::mig_network>() );
      mig1 = cleanup_dangling( mig1 );
    }

    mockturtle::depth_view mig1_dd{mig1};
    mockturtle::depth_view mig1_dd_s{mig1, detail::fanout_cost_depth_local<mockturtle::mig_network>(), ps_d};

    auto size_b = mig1.num_gates();
    auto depth_b = mig1_dd.depth();
    auto depth_b_splitters = mig1_dd_s.depth();
    auto max_fanout_b = detail::compute_maxfanout( mig1 );
    auto node_larger_16_b = detail::compute_fanout4( mig1 );

    // Option 1 -- not consider splitters in the delay -- limit fanout
    // Option 2 -- consider splitters
    // -> almost same results
    std::cout << " depth ... \n";
    mockturtle::mig_algebraic_depth_rewriting_params ps2;
    while ( true )
    {
      mockturtle::depth_view mig1_dd_d{mig1};
      auto depth = mig1_dd_d.depth();
      ps2.strategy = mockturtle::mig_algebraic_depth_rewriting_params::aggressive;
      //ps2.allow_area_increase = false;
      //mig_algebraic_depth_rewriting_splitters( mig1_dd_d, ps2 );
      mig_algebraic_depth_rewriting( mig1_dd_d, ps2 );
      ps2.strategy = mockturtle::mig_algebraic_depth_rewriting_params::dfs;
      //mig_algebraic_depth_rewriting_splitters( mig1_dd_d, ps2 );
      mig_algebraic_depth_rewriting( mig1_dd_d, ps2 );

      if ( mig1_dd_d.depth() >= depth )
        break;
      mig1 = mig1_dd_d;
      mig1 = cleanup_dangling( mig1 );
    }

    mockturtle::mig_network mig2 = mig1_dd;
    mig2 = cleanup_dangling( mig2 );

    mockturtle::depth_view mig2_dd{mig2};
    mockturtle::depth_view mig2_dd_s{mig2, detail::fanout_cost_depth_local<mockturtle::mig_network>(), ps_d};

    auto size_c = mig2.num_gates();
    auto depth_c = mig2_dd.depth();
    auto depth_c_splitters = mig2_dd_s.depth();
    auto max_fanout_c = detail::compute_maxfanout( mig2 );
    auto node_larger_16_c = detail::compute_fanout4( mig2 );

    size_b = mig2.num_gates();
    depth_b = mig2_dd.depth();
    depth_b_splitters = mig2_dd_s.depth();
    max_fanout_b = detail::compute_maxfanout( mig2 );
    node_larger_16_b = detail::compute_fanout4( mig2 );

    std::cout << " resub ... \n";
    mockturtle::resubstitution_params ps_r;
    ps_r.max_divisors = 150;
    ps_r.max_inserts = 1;
    while ( true )
    {
      auto size_o = mig2.num_gates();
      //mockturtle::depth_view mig2_dd_r{mig2, detail::fanout_cost_depth_local<mockturtle::mig_network>(), ps_d};
      //mig_resubstitution_splitters( mig2_dd_r, ps_r );
      mockturtle::depth_view mig2_dd_r{mig2};
      mig_resubstitution( mig2_dd_r, ps_r );
      mig2 = mig2_dd_r;
      mig2 = cleanup_dangling( mig2 );
      if ( mig2.num_gates() >= size_o )
        break;
    }

    while ( true )
    {
      mockturtle::depth_view mig1_dd_d{mig2};
      auto depth = mig1_dd_d.depth();
      ps2.strategy = mockturtle::mig_algebraic_depth_rewriting_params::aggressive;
      //ps2.allow_area_increase = false;
      //mig_algebraic_depth_rewriting_splitters( mig1_dd_d, ps2 );
      mig_algebraic_depth_rewriting( mig1_dd_d, ps2 );
      ps2.strategy = mockturtle::mig_algebraic_depth_rewriting_params::dfs;
      //mig_algebraic_depth_rewriting_splitters( mig1_dd_d, ps2 );
      mig_algebraic_depth_rewriting( mig1_dd_d, ps2 );

      if ( mig1_dd_d.depth() >= depth )
        break;
      mig2 = mig1_dd_d;
      mig2 = cleanup_dangling( mig2 );
    }

    mig2 = cleanup_dangling( mig2 );
    std::cout << " resub ... \n";
    while ( true )
    {
      auto size_o = mig2.num_gates();
      //mockturtle::depth_view mig2_dd_r{mig2, detail::fanout_cost_depth_local<mockturtle::mig_network>(), ps_d};
      //mig_resubstitution_splitters( mig2_dd_r, ps_r );
      mockturtle::depth_view mig2_dd_r{mig2};
      mig_resubstitution( mig2, ps_r );
      //mig2 = mig2_dd_r;
      mig2 = cleanup_dangling( mig2 );
      if ( mig2.num_gates() >= size_o )
        break;
    }

    mockturtle::depth_view mig3_dd{mig2};
    mockturtle::depth_view mig3_dd_s{mig2, detail::fanout_cost_depth_local<mockturtle::mig_network>(), ps_d};

    size_c = mig2.num_gates();
    depth_c = mig3_dd.depth();
    depth_c_splitters = mig3_dd_s.depth();
    auto const JJ_c = detail::JJ_number_final( mig2 );
    max_fanout_c = detail::compute_maxfanout( mig2 );
    node_larger_16_c = detail::compute_fanout4( mig2 );

    //float impr_JJ = ( float( JJ_a ) - float( JJ_c ) ) / float( JJ_a ) * 100;
    //float impr_levels = ( float( depth_a_splitters ) - float( depth_c_splitters ) ) / float( depth_a_splitters ) * 100;
    float impr_size = ( float( JJ_a ) - float( size_c ) ) / float( JJ_a ) * 100;
    float impr_levels = ( float( depth_a_splitters ) - float( depth_c ) ) / float( depth_a_splitters ) * 100;

    //mockturtle::write_verilog( mig2, fmt::format( "{}_mig_aqfp.v", benchmark ) );

    exp( benchmark,
         JJ_a, depth_a_splitters,
         size_c, depth_c, //max_fanout_c, node_larger_16_c,
         impr_size, impr_levels, experiments::abc_cec_aqfp( mig2, benchmark ) );
  }

  exp.save();
  exp.table();
}

void start_aig()
{
  using namespace experiments;

  experiments::experiment<std::string, uint32_t, uint32_t, uint32_t, uint32_t, int, int, uint32_t, uint32_t, bool> exp( "mig_aqfp", "benchmark", "size Soa AIG", "depthsoa AIG", "size our AIG", "depth our AIG", "diff size", "diff depth ", "max fanout", "# nodes > 16", "eq cec" );

  std::map<std::string, std::tuple<uint32_t, uint32_t>> opt_aig;
  opt_aig.emplace( "c17", std::make_tuple( 6, 3 ) );
  opt_aig.emplace( "c432", std::make_tuple( 122, 26 ) );
  opt_aig.emplace( "c880", std::make_tuple( 306, 27 ) );
  opt_aig.emplace( "c1908", std::make_tuple( 296, 21 ) );
  opt_aig.emplace( "c5315", std::make_tuple( 1325, 26 ) );
  opt_aig.emplace( "c6288", std::make_tuple( 1870, 89 ) );

  for ( auto const& benchmark : aqfp_benchmarks() )
  {
    fmt::print( "[i] processing {}\n", benchmark );

    /* read aig 
    mockturtle::aig_network aig;
    if ( lorina::read_aiger( experiments::benchmark_aqfp_path( benchmark ), mockturtle::aiger_reader( aig ) ) != lorina::return_code::success )
    {
      std::cout << "ERROR 2" << std::endl;
      std::abort();
      return;
    }

    auto const size_a = std::get<0>( opt_aig[benchmark] );
    auto const depth_a = std::get<1>( opt_aig[benchmark] );

    mockturtle::depth_view aig_d{aig};
    auto const size_b = aig.num_gates();
    auto const depth_b = aig_d.depth();
    auto const max_fanout_b = detail::compute_maxfanout( aig );
    auto const node_larger_16_b = detail::compute_fanout4( aig );

    exp( benchmark,
         size_a, depth_a,
         size_b, depth_b, //max_fanout_c, node_larger_16_c,
         size_a - size_b, depth_a - depth_b, max_fanout_b, node_larger_16_b, experiments::abc_cec_aqfp( aig, benchmark ) );
  }

  exp.save();
  exp.table();
}

void check_cost()
{
  using namespace experiments;

  experiments::experiment<std::string, uint32_t, uint32_t, uint32_t, uint32_t, uint32_t> exp( "mig_aqfp", "benchmark", "size", "depth", "# JJs", "Depth JJs", "Number of buffers" );

  for ( auto const& benchmark : test_benchmarks() )
  {
    fmt::print( "[i] processing {}\n", benchmark );

    //if ( benchmark != "test2" )
    //continue;
    /* read aig 
    mockturtle::mig_network mig;
    if ( lorina::read_verilog( experiments::benchmark_test_path( benchmark ), mockturtle::verilog_reader( mig ) ) != lorina::return_code::success )
    {
      std::cout << "ERROR 2" << std::endl;
      std::abort();
      return;
    }

    mig = cleanup_dangling( mig );
    mockturtle::depth_view_params ps_d;
    mockturtle::depth_view mig_d{mig};
    mockturtle::depth_view mig_d_s{mig, detail::fanout_cost_depth_local<mockturtle::mig_network>(), ps_d};
    auto const JJ_b = detail::JJ_number_final( mig );
    auto const depth_b_spli = mig_d_s.depth();
    auto const size_b = mig.num_gates();
    auto const depth_b = mig_d.depth();
    auto const buffers = detail::compute_buffers_not_shared( mig );

    exp( benchmark, size_b, depth_b,
         JJ_b, depth_b_spli,
         buffers );
  }

  exp.save();
  exp.table();
}

void debug()
{
  mockturtle::mig_network mig;
  auto benchmark = "c6288";
  if ( read_verilog( "c6288_mig_aqfp.v", mockturtle::verilog_reader( mig ) ) != lorina::return_code::success )
  {
    std::cout << "ERROR 2" << std::endl;
    std::abort();
    return;
  }

  mockturtle::resubstitution_params ps;
  ps.max_inserts = 1;
  ps.max_divisors = 150;
  auto i = 0;
  while ( true )
  {
    i++;
    auto size_o = mig.num_gates();
    mig_resubstitution( mig, ps );
    mig = cleanup_dangling( mig );
    if ( experiments::abc_cec_aqfp( mig, benchmark ) == false )
    {
      std::cout << "iteration numero " << i << std::endl;
      break;
    }
    if ( mig.num_gates() >= size_o )
      break;
  }

  mockturtle::write_verilog( mig, fmt::format( "{}_mig_resub.v", benchmark ) );
}

void start_mig()
{
  using namespace experiments;

  mockturtle::mig_network mig_db;
  read_verilog( "db.v", mockturtle::verilog_reader( mig_db ) );

  /* option 1: XMG strategy using database from file 
  mockturtle::mig4_npn_resynthesis_params ps;
  ps.multiple_depth = true;
  mockturtle::mig4_npn_resynthesis<mockturtle::mig_network> mig_resyn( mockturtle::detail::to_index_list( mig_db ), ps );

  experiments::experiment<std::string, uint32_t, uint32_t, uint32_t, uint32_t, int, int, uint32_t, uint32_t, bool> exp( "mig_aqfp", "benchmark", "size Soa MIG", "depth Soa MIG", "size our AIG", "depth our MIG", "diff size", "diff depth ", "max fanout", "# nodes > 16", "eq cec" );

  std::map<std::string, std::tuple<uint32_t, uint32_t>> opt_mig;
  opt_mig.emplace( "c17", std::make_tuple( 6, 3 ) );
  opt_mig.emplace( "c432", std::make_tuple( 121, 26 ) );
  opt_mig.emplace( "c880", std::make_tuple( 274, 18 ) );
  opt_mig.emplace( "c1908", std::make_tuple( 263, 21 ) );
  opt_mig.emplace( "c5315", std::make_tuple( 1248, 23 ) );
  opt_mig.emplace( "c6288", std::make_tuple( 984, 48 ) );

  for ( auto const& benchmark : aqfp_benchmarks() )
  {
    fmt::print( "[i] processing {}\n", benchmark );

    /* read aig 
    mockturtle::mig_network mig;
    if ( lorina::read_aiger( experiments::benchmark_aqfp_path( benchmark ), mockturtle::aiger_reader( mig ) ) != lorina::return_code::success )
    {
      std::cout << "ERROR 2" << std::endl;
      std::abort();
      return;
    }

    auto const size_a = std::get<0>( opt_mig[benchmark] );
    auto const depth_a = std::get<1>( opt_mig[benchmark] );

    mockturtle::cut_rewriting_params ps_c;
    ps_c.cut_enumeration_ps.cut_size = 4;
    while ( true )
    {
      std::cout << " wowo\n";
      auto size_opt = mig.num_gates();
      mig = cut_rewriting( mig, mig_resyn, ps_c, nullptr );
      mig = cleanup_dangling( mig );
      if ( mig.num_gates() >= size_opt )
        break;
    }

    mockturtle::depth_view aig_d{mig};
    auto const size_b = mig.num_gates();
    auto const depth_b = aig_d.depth();
    auto const max_fanout_b = detail::compute_maxfanout( mig );
    auto const node_larger_16_b = detail::compute_fanout4( mig );

    exp( benchmark,
         size_a, depth_a,
         size_b, depth_b, //max_fanout_c, node_larger_16_c,
         size_a - size_b, depth_a - depth_b, max_fanout_b, node_larger_16_b, experiments::abc_cec_aqfp( mig, benchmark ) );
  }

  exp.save();
  exp.table();
}

void flow_mig()
{
  using namespace experiments;

  mockturtle::mig_network mig_db;
  read_verilog( "db.v", mockturtle::verilog_reader( mig_db ) );

  /* option 1: XMG strategy using database from file 
  mockturtle::mig4_npn_resynthesis_params ps;
  ps.multiple_depth = true;
  mockturtle::mig4_npn_resynthesis<mockturtle::mig_network> mig_resyn( mockturtle::detail::to_index_list( mig_db ), ps );

  experiments::experiment<std::string, uint32_t, uint32_t, uint32_t, uint32_t, int, int, uint32_t, uint32_t, bool> exp( "mig_aqfp", "benchmark", "# JJs Soa MIG", "depth JJs Soa MIG", "# JJs opt. MIG", "depth JJs opt. MIG", "diff size", "diff depth ", "max fanout", "# nodes > 16", "eq cec" );

  std::map<std::string, std::tuple<uint32_t, uint32_t>> opt_mig;
  opt_mig.emplace( "c17", std::make_tuple( 6, 3 ) );
  opt_mig.emplace( "c432", std::make_tuple( 121, 26 ) );
  opt_mig.emplace( "c880", std::make_tuple( 274, 18 ) );
  opt_mig.emplace( "c1908", std::make_tuple( 263, 21 ) );
  opt_mig.emplace( "c5315", std::make_tuple( 1248, 23 ) );
  opt_mig.emplace( "c6288", std::make_tuple( 984, 48 ) );

  std::map<std::string, std::tuple<uint32_t, uint32_t>> soa_mig;
  soa_mig.emplace( "c17", std::make_tuple( 60, 5 ) );
  soa_mig.emplace( "c432", std::make_tuple( 3072, 39 ) );
  soa_mig.emplace( "c880", std::make_tuple( 5914, 30 ) );
  soa_mig.emplace( "c1908", std::make_tuple( 6818, 38 ) );
  soa_mig.emplace( "c5315", std::make_tuple( 30910, 40 ) );
  soa_mig.emplace( "c6288", std::make_tuple( 25870, 94 ) );

  for ( auto const& benchmark : aqfp_benchmarks() )
  {
    fmt::print( "[i] processing {}\n", benchmark );

    /* read aig 
    mockturtle::mig_network mig;
    if ( lorina::read_aiger( experiments::benchmark_aqfp_path( benchmark ), mockturtle::aiger_reader( mig ) ) != lorina::return_code::success )
    {
      std::cout << "ERROR 2" << std::endl;
      std::abort();
      return;
    }

    auto const size_a = std::get<0>( soa_mig[benchmark] );
    auto const depth_a = std::get<1>( soa_mig[benchmark] );

    mockturtle::cut_rewriting_params ps_c;
    ps_c.cut_enumeration_ps.cut_size = 4;
    while ( true )
    {
      std::cout << " wowo\n";
      auto size_opt = mig.num_gates();
      mig = cut_rewriting( mig, mig_resyn, ps_c, nullptr );
      mig = cleanup_dangling( mig );
      if ( mig.num_gates() >= size_opt )
        break;
    }

    std::cout << " depth ... \n";
    mockturtle::mig_algebraic_depth_rewriting_params ps_a;
    mockturtle::depth_view mig1_dd{mig}; //, detail::fanout_cost_depth_local<mockturtle::mig_network>(), ps_d};

    while ( true )
    {
      mockturtle::depth_view mig1_dd_d{mig};
      auto depth = mig1_dd_d.depth();
      ps_a.overhead = 1.1;
      ps_a.strategy = mockturtle::mig_algebraic_depth_rewriting_params::aggressive;
      mig_algebraic_depth_rewriting_splitters( mig1_dd_d, ps_a );
      mig = mig1_dd_d;
      mig = cleanup_dangling( mig );
      //ps_a.strategy = mockturtle::mig_algebraic_depth_rewriting_params::dfs;
      //mig_algebraic_depth_rewriting_splitters( mig1_dd_d, ps_a );
      //mig = mig1_dd_d;
      //mig = cleanup_dangling( mig );

      if ( mig1_dd_d.depth() >= depth )
        break;
    }

    mockturtle::depth_view_params ps_d;
    mockturtle::depth_view mig2_dd{mig};
    mockturtle::depth_view mig2_dd_s{mig, detail::fanout_cost_depth_local<mockturtle::mig_network>(), ps_d};

    std::cout << " resub ... \n";
    mockturtle::resubstitution_params ps_r;
    ps_r.max_divisors = 150;
    ps_r.max_inserts = 1;
    //ps_r.progress = true;
    auto i = 0;
    while ( true )
    {
      //i++;
      // if ( i > 1 )
      //  break;
      auto size_o = mig.num_gates();
      mockturtle::depth_view mig2_dd_r{mig, detail::fanout_cost_depth_local<mockturtle::mig_network>(), ps_d};
      mig_resubstitution_splitters( mig2_dd_r, ps_r );
      mig = mig2_dd_r;
      mig = cleanup_dangling( mig );
      if ( mig.num_gates() >= size_o )
        break;
    }

    while ( true )
    {
      mockturtle::depth_view mig1_dd_d{mig};
      auto depth = mig1_dd_d.depth();
      mig_algebraic_depth_rewriting_splitters( mig1_dd_d, ps_a );
      mig = mig1_dd_d;
      mig = cleanup_dangling( mig );
      if ( mig1_dd_d.depth() >= depth )
        break;
    }

    mig = cleanup_dangling( mig );
    std::cout << " resub ... \n";
    i = 0;
    while ( true )
    {
      i++;
      if ( i > 2 )
        break;
      auto size_o = mig.num_gates();
      mockturtle::depth_view mig2_dd_r{mig, detail::fanout_cost_depth_local<mockturtle::mig_network>(), ps_d};
      mig_resubstitution_splitters( mig2_dd_r, ps_r );
      mig = mig2_dd_r;
      mig = cleanup_dangling( mig );
      if ( mig.num_gates() >= size_o )
        break;
    }

    mockturtle::depth_view mig3_dd{mig};
    mockturtle::depth_view mig3_dd_s{mig, detail::fanout_cost_depth_local<mockturtle::mig_network>(), ps_d};

    auto const size_c = mig.num_gates();
    auto const depth_c = mig3_dd.depth();
    auto const depth_c_splitters = mig3_dd_s.depth();
    auto const JJ_c = detail::JJ_number_final( mig );
    auto const max_fanout_c = detail::compute_maxfanout( mig );
    auto const node_larger_16_c = detail::compute_fanout4( mig );

    exp( benchmark,
         size_a, depth_a,
         JJ_c, depth_c_splitters,
         size_a - JJ_c, depth_a - depth_c_splitters, max_fanout_c, node_larger_16_c, experiments::abc_cec_aqfp( mig, benchmark ) );
  }

  exp.save();
  exp.table();
}

void flow_mig_final()
{
  using namespace experiments;

  mockturtle::mig_network mig_db;
  read_verilog( "db.v", mockturtle::verilog_reader( mig_db ) );

  /* option 1: XMG strategy using database from file 
  mockturtle::mig4_npn_resynthesis_params ps;
  using view_mig_t = mockturtle::fanout_limit_view<mockturtle::mig_network>;
  //ps.multiple_depth = true;
  mockturtle::mig4_npn_resynthesis<mockturtle::mig_network> mig_resyn( mockturtle::detail::to_index_list( mig_db ), ps );

  experiments::experiment<std::string, uint32_t, uint32_t, uint32_t, uint32_t, uint32_t, uint32_t, uint32_t, uint32_t, uint32_t, float, uint32_t, float, uint32_t, uint32_t, uint32_t, float, uint32_t, float, bool> exp( "mig_aqfp", "benchmark", "size MIG", "Size MIG f", "depth MIG", "max. fanout", "# nodes > 16", "JJs MIG", "Levels JJs MIG", "size Opt. MIG", "SIze Opt MIG f", "imrp. size", "depth Opt. MIG", "imrp. depth", "max. fanout Opt MIG", "# nodes > 16 Opt MIG", "JJs Opt MIG", "imrp. JJS", "Levels JJs Opt MIG", "imrp Levels", "eq cec" );

  for ( auto const& benchmark : aqfp_benchmarks() )
  {
    if ( benchmark != "c5315" )
      continue;
    fmt::print( "[i] processing {}\n", benchmark );

    /* read aig 
    mockturtle::mig_network mig;
    if ( lorina::read_verilog( experiments::benchmark_aqfp_path( benchmark ), mockturtle::verilog_reader( mig ) ) != lorina::return_code::success )
    {
      std::cout << "ERROR 2" << std::endl;
      std::abort();
      return;
    }

    std::cout << "_____________________\n";
    mig.foreach_gate( [&]( const auto& n ) {
      if ( mig.fanout_size( n ) >= 16 )
      {
        std::cout << "[mig] node " << n << " has " << mig.fanout_size( n ) << " fanouts" << std::endl;
      }
    } );

    mockturtle::depth_view_params ps_d;
    mockturtle::depth_view mig_d2{mig};
    mockturtle::depth_view mig2_dd2{mig, detail::fanout_cost_depth_local<mockturtle::mig_network>(), ps_d};
    auto const size_b = mig.num_gates();
    auto const depth_b = mig_d2.depth();
    auto const depth_b_splitters = mig2_dd2.depth();
    auto const JJ_b = detail::JJ_number_final( mig );
    auto const max_fanout_b = detail::compute_maxfanout( mig );
    auto const node_larger_16_b = detail::compute_fanout4( mig );

    mockturtle::fanout_limit_view_params ps{15u};
    mockturtle::mig_network mig2;
    mockturtle::fanout_limit_view lim_mig{mig2, ps};

    if ( lorina::read_verilog( experiments::benchmark_aqfp_path( benchmark ), mockturtle::verilog_reader( lim_mig ) ) != lorina::return_code::success )
    {
      std::cout << "ERROR 2" << std::endl;
      std::abort();
      return;
    }

    lim_mig.foreach_gate( [&]( const auto& n ) {
      if ( lim_mig.fanout_size( n ) >= 16 )
      {
        std::cout << "[lim_mig] node " << n << " has " << lim_mig.fanout_size( n ) << " fanouts" << std::endl;
      }
    } );

    auto const size_fanout_b = lim_mig.num_gates();
    // auto klut = lut_map( mig, 4u );

    //&lim_mig = mockturtle::node_resynthesis<view_mig_t>( klut, mig_resyn );
    //mig = mockturtle::node_resynthesis<mockturtle::mig_network>( klut, mig_resyn );
    //mig = cleanup_dangling( mig );
    //mockturtle::write_verilog( mig, fmt::format( "../experiments/benchmarks_aqfp/{}.v", benchmark ) );
    //&lim_mig = cleanup_dangling( lim_mig );
    //mockturtle::depth_view mig2_d2_f{lim_mig};

    auto i = 0;
    while ( true )
    {
      i++;
      if ( i > 10 )
        break;
      mockturtle::mig_algebraic_depth_rewriting_params ps_a;
      mockturtle::depth_view mig1_dd_d{lim_mig};
      auto depth = mig1_dd_d.depth();
      ps_a.overhead = 1;
      ps_a.strategy = mockturtle::mig_algebraic_depth_rewriting_params::aggressive;
      ps_a.allow_area_increase = false;
      mig_algebraic_depth_rewriting_splitters( mig1_dd_d, ps_a );
      mig = mig1_dd_d;
      mig = cleanup_dangling( mig );

      //mockturtle::depth_view mig2_dd_s{mig, detail::fanout_cost_depth_local<mockturtle::mig_network>(), ps_d};

      mockturtle::resubstitution_params ps_r;
      ps_r.max_divisors = 200;
      ps_r.max_inserts = 1;

      auto size_o = mig.num_gates();
      mockturtle::depth_view mig2_dd_r{mig, detail::fanout_cost_depth_local<mockturtle::mig_network>(), ps_d};
      //mig_resubstitution( mig, ps_r );
      mig_resubstitution_splitters( mig2_dd_r, ps_r );
      mig = mig2_dd_r;
      mig = cleanup_dangling( mig );

      auto const mig2 = cleanup_dangling( mig );

      mockturtle::akers_resynthesis<mockturtle::mig_network> resyn;

      refactoring( mig, resyn, {}, nullptr, detail::jj_cost<mockturtle::mig_network>() );
      mig = cleanup_dangling( mig );

      mockturtle::depth_view mig2_dd_a{mig, detail::fanout_cost_depth_local<mockturtle::mig_network>(), ps_d};
      mockturtle::depth_view mig2_dd{mig};

      if ( ( mig.num_gates() > mig2.num_gates() ) || ( mig2_dd_a.depth() > mig2_dd_r.depth() ) || ( mig2_dd.depth() > mig1_dd_d.depth() ) )
        mig = mig2;

      mig = cleanup_dangling( mig );

      mockturtle::depth_view mig2_dd_d_y{mig, detail::fanout_cost_depth_local<mockturtle::mig_network>(), ps_d};
      mockturtle::depth_view mig2_dd_y{mig};

      if ( ( mig.num_gates() >= size_o ) || ( mig1_dd_d.depth() >= depth ) )
        break;
    }

    mockturtle::depth_view mig3_dd{mig};
    mockturtle::depth_view mig3_dd_s{mig, detail::fanout_cost_depth_local<mockturtle::mig_network>(), ps_d};

    auto const size_c = mig.num_gates();
    auto const size_fanout_c = 0; //lim_mig2.num_gates();

    auto const depth_c = mig3_dd.depth();

    //assert( depth_c == mig3_dd_f.depth() );
    auto const depth_c_splitters = mig3_dd_s.depth();
    auto const JJ_c = detail::JJ_number_final( mig );
    auto const max_fanout_c = detail::compute_maxfanout( mig );
    auto const node_larger_16_c = detail::compute_fanout4( mig );

    exp( benchmark, size_b, size_fanout_b, depth_b, max_fanout_b, node_larger_16_b,
         JJ_b, depth_b_splitters,
         size_c, size_fanout_c, float( float( size_b - size_c ) / float( size_b ) * 100 ), depth_c, float( float( depth_b - depth_c ) / float( depth_b ) * 100 ), max_fanout_c, node_larger_16_c,
         JJ_c, float( float( JJ_b - JJ_c ) / float( JJ_b ) * 100 ), depth_c_splitters, float( float( depth_b_splitters - depth_c_splitters ) / float( depth_b_splitters ) * 100 ),
         experiments::abc_cec_aqfp( mig, benchmark ) );
  }

  exp.save();
  exp.table();
}*/

int main()
{
  //flow_mig_final();
  return 0;
}
