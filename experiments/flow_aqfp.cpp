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

namespace detail
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
    else if ( ntk.fanout_size( n ) + used_as_po( ntk, n ) == 1 )
      cost = 1;
    else if ( ( ntk.fanout_size( n ) + used_as_po( ntk, n ) > 1 ) && ( ntk.fanout_size( n ) + used_as_po( ntk, n ) < 5 ) )
      cost = 2;
    else if ( ( ntk.fanout_size( n ) + used_as_po( ntk, n ) > 4 ) ) //&& ( ntk.fanout_size( n ) < 17 ) )
      cost = 3;
    return cost;
  }
};

template<class Ntk>
uint32_t compute_maxfanout( Ntk ntk )
{
  auto max_fanout = 0;
  ntk.foreach_gate( [&]( auto const& n ) {
    if ( ntk.fanout_size( n ) > max_fanout ) //+ used_as_po( ntk, n ) > max_fanout )
      max_fanout = ntk.fanout_size( n ) ; //+ used_as_po( ntk, n );
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
  if ( ( ntk.fanout_size( n ) + used_as_po( ntk, n ) > 1 ) && ( ntk.fanout_size( n ) + used_as_po( ntk, n ) < 5 ) )
    cost = 1;
  else if ( ( ntk.fanout_size( n ) + used_as_po( ntk, n ) > 4 ) ) //&& ( ntk.fanout_size( n ) < 17 ) )
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
      if ( mig.is_pi( mig.get_node( s ) ) ) /* this will not balance the pis*/
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
    if ( ntk.fanout_size( n ) + used_as_po( ntk, n ) == 1 )
      JJ = JJ + 6;
    else if ( ntk.fanout_size( n ) + used_as_po( ntk, n ) <= 4 )
      JJ = JJ + 8;
    else if ( ntk.fanout_size( n ) + used_as_po( ntk, n ) <= 16 )
      JJ = JJ + 16;
    // this should not happen in the new limit fanout view
    else if ( ntk.fanout_size( n ) + used_as_po( ntk, n ) <= 20 )
      JJ = JJ + 16 + 8;
    else if ( ntk.fanout_size( n ) + used_as_po( ntk, n ) <= 32 )
      JJ = JJ + 16 * 2;
    else if ( ntk.fanout_size( n ) + used_as_po( ntk, n ) <= 36 )
      JJ = JJ + 16 * 2 + 8;
    else if ( ntk.fanout_size( n ) + used_as_po( ntk, n ) <= 48 )
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
    if ( ntk.fanout_size( n ) + used_as_po( ntk, n ) > max_fanout )
      max_fanout = ntk.fanout_size( n ) + used_as_po( ntk, n );
    return true;
  } );
  return max_fanout;
}

template<class Ntk>
uint32_t compute_fanout4_inputs( Ntk ntk )
{
  auto fanout4 = 0;
  ntk.foreach_pi( [&]( auto const& n, auto i ) {
    if ( ntk.fanout_size( n ) > 16 ) //+ used_as_po( n ) > 16 )
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
    if ( ntk.fanout_size( n )  > 16 ) //+ used_as_po( ntk, n ) > 16 )
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

void flow_mig_final()
{
  using namespace experiments;

  /* limit the fanout to max 16 */
  using view_mig_t = mockturtle::fanout_limit_view<mockturtle::mig_network>;

  experiments::experiment<std::string, uint32_t, uint32_t, uint32_t, uint32_t, uint32_t, uint32_t, uint32_t, float, uint32_t, float, uint32_t, uint32_t, bool> exp( "mig_aqfp", "benchmark", "size MIG", "Size MIG f", "depth MIG", "max. fanout", "# nodes > 16", "size Opt. MIG", "Size Opt MIG f", "imrp. size", "depth Opt. MIG", "imrp. depth", "max. fanout Opt MIG", "# nodes > 16 Opt MIG", "eq cec" );

  for ( auto const& benchmark : aqfp_benchmarks() )
  {
    if ( benchmark != "c432" )
      continue;
    fmt::print( "[i] processing {}\n", benchmark );

    /* read aig */
    mockturtle::mig_network mig;
    if ( lorina::read_verilog( experiments::benchmark_aqfp_path( benchmark ), mockturtle::verilog_reader( mig ) ) != lorina::return_code::success )
    {
      std::cout << "ERROR 2" << std::endl;
      std::abort();
      return;
    }

    mig.foreach_gate( [&]( const auto& n ) {
      if ( mig.fanout_size( n ) >= 16 )
      {
        std::cout << "[mig] node " << n << " has " << mig.fanout_size( n ) << " fanouts" << std::endl;
      }
    } );

    mockturtle::depth_view_params ps_d;
    mockturtle::depth_view mig_d2{mig};
    //mockturtle::depth_view mig2_dd2{mig, detail::fanout_cost_depth_local<mockturtle::mig_network>(), ps_d}; // this will be used to evaluate the depth with splitters
    auto const size_b = mig.num_gates();
    auto const depth_b = mig_d2.depth();

    mockturtle::fanout_limit_view_params ps{16u};
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
    auto const max_fanout_b = detail::compute_maxfanout( lim_mig );
    auto const node_larger_16_b = detail::compute_fanout4( lim_mig );

    auto i = 0;
    while ( true )
    {
      i++;
      if ( i > 1 )
        break;
      mockturtle::mig_algebraic_depth_rewriting_params ps_a;
      mockturtle::depth_view mig1_dd_d{lim_mig}; // is this enough?
      auto depth = mig1_dd_d.depth();
      ps_a.overhead = 1;
      ps_a.strategy = mockturtle::mig_algebraic_depth_rewriting_params::aggressive;
      ps_a.allow_area_increase = false;
      mig_algebraic_depth_rewriting_splitters( mig1_dd_d, ps_a );

      std::cout << " lim mig size " << lim_mig.num_gates() << std::endl;

      mockturtle::resubstitution_params ps_r;
      ps_r.max_divisors = 200;
      ps_r.max_inserts = 1;

      auto size_o = lim_mig.num_gates();
      mockturtle::depth_view mig2_dd_r{lim_mig, detail::fanout_cost_depth_local<mockturtle::mig_network>(), ps_d};
      mig_resubstitution_splitters( mig2_dd_r, ps_r );
      std::cout << " lim mig size " << lim_mig.num_gates() << std::endl;
      std::cout << " mig size " << mig.num_gates() << std::endl;

      //mig = lim_mig;
      //mockturtle::fanout_limit_view<mockturtle::mig_network> lim_mig2{cleanup_dangling( mig ), ps};
      //mockturtle::fanout_limit_view lim_mig2{mig, ps};

      //auto const mig2 = cleanup_dangling( mig );

      /* mockturtle::akers_resynthesis<mockturtle::mig_network> resyn;

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
        break;*/
    }

    mockturtle::depth_view mig3_dd{mig};
    mockturtle::depth_view mig3_dd_s{mig, detail::fanout_cost_depth_local<mockturtle::mig_network>(), ps_d};

    auto const size_c = mig.num_gates();
    auto const size_fanout_c = lim_mig.num_gates();
    auto const depth_c = mig3_dd.depth();

    auto const depth_c_splitters = mig3_dd_s.depth();
    auto const JJ_c = detail::JJ_number_final( mig );
    auto const max_fanout_c = detail::compute_maxfanout( mig );
    auto const node_larger_16_c = detail::compute_fanout4( mig );

    exp( benchmark, size_b, size_fanout_b, depth_b, max_fanout_b, node_larger_16_b,
         size_c, size_fanout_c, float( float( size_b - size_c ) / float( size_b ) * 100 ), depth_c, float( float( depth_b - depth_c ) / float( depth_b ) * 100 ), max_fanout_c, node_larger_16_c,
         experiments::abc_cec_aqfp( mig, benchmark ) );
  }

  exp.save();
  exp.table();
}

int main()
{
  flow_mig_final();
  return 0;
}
