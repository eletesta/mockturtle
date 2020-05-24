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

#include <lorina/aiger.hpp>
#include <mockturtle/algorithms/collapse_mapped.hpp>
#include <mockturtle/algorithms/equivalence_checking.hpp>
#include <mockturtle/algorithms/lut_mapping.hpp>
#include <mockturtle/algorithms/miter.hpp>
#include <mockturtle/algorithms/node_resynthesis.hpp>
#include <mockturtle/algorithms/node_resynthesis/dsd.hpp>
#include <mockturtle/algorithms/node_resynthesis/exact.hpp>
#include <mockturtle/io/aiger_reader.hpp>
#include <mockturtle/networks/aig.hpp>
#include <mockturtle/networks/klut.hpp>
#include <mockturtle/views/mapping_view.hpp>

#include <lorina/lorina.hpp>
#include <mockturtle/algorithms/equivalence_checking.hpp>
#include <mockturtle/algorithms/miter.hpp>
#include <mockturtle/io/aiger_reader.hpp>
#include <mockturtle/io/verilog_reader.hpp>
#include <mockturtle/networks/mig.hpp>
#include <mockturtle/views/fanout_limit_view.hpp>

#include <fmt/format.h>

std::vector<std::string> benchmarks = {
    // "benchmarks/c17.aig",
    "benchmarks_aqfp/c432.v",
    //"benchmarks/c.v",
    //"benchmarks/c432.v",
    "benchmarks_aqfp/c5315.v",
}; /* benchmarks */

std::string benchmark_path( std::string const& path )
{
  return std::string{"/Users/testa/Desktop/mockturtle/experiments/"} + path;
}

template<class Ntk>
bool abc_cec( Ntk const& ntk, std::string const& benchmark )
{
  mockturtle::write_bench( ntk, "/tmp/test.bench" );
  std::string command = fmt::format( "../../abc/abc -q \"cec -n {} /tmp/test.bench\"", benchmark_path( benchmark ) );

  std::array<char, 128> buffer;
  std::string result;
  std::unique_ptr<FILE, decltype( &pclose )> pipe( popen( command.c_str(), "r" ), pclose );
  if ( !pipe )
  {
    throw std::runtime_error( "popen() failed" );
  }
  while ( fgets( buffer.data(), buffer.size(), pipe.get() ) != nullptr )
  {
    result += buffer.data();
  }

  return result.size() >= 23 && result.substr( 0u, 23u ) == "Networks are equivalent";
}

int main()
{
  using namespace experiments;
  using namespace mockturtle;

  for ( const auto& benchmark : ::benchmarks )
  {
    fmt::print( "[i] processing {}\n", benchmark );

    mig_network mig;

    if ( lorina::read_verilog( ::benchmark_path( benchmark ), verilog_reader( mig ) ) != lorina::return_code::success )
    {
      fmt::print( "[e] parse error\n" );
    }

    /* count number of nodes that exceed the fanout limit */
    unsigned count_mig = 0u;
    mig.foreach_node( [&]( const auto& node ) {
      if ( mig.is_constant( node ) )
        return true; /* next */
      if ( mig.is_pi( node ) )
        return true; /* next */
      if ( mig.fanout_size( node ) > 16 )
      {
        count_mig++;
        fmt::print( "[mig] node {} with fanout_size {} (is_pi = {})\n", node, mig.fanout_size( node ), mig.is_pi( node ) );
      }
      return true;
    } );

    fmt::print( "[mig] has {} nodes with fanout > 16\n", count_mig );
    fmt::print( "[mig] size = {} \n", mig.num_gates() );

    mig_network mig2;
    fanout_limit_view lim_mig( mig2 );

    if ( lorina::read_verilog( ::benchmark_path( benchmark ), verilog_reader( lim_mig ) ) != lorina::return_code::success )
    {
      fmt::print( "[e] parse error\n" );
    }
    auto count = 0u;
    lim_mig.foreach_node( [&]( const auto& node ) {
      if ( lim_mig.is_constant( node ) )
        return true; /* next */
      if ( lim_mig.is_pi( node ) )
        return true; /* next */

      if ( lim_mig.fanout_size( node ) > 16 )
      {
        count++;
        fmt::print( "[mig2] node {} with fanout_size {} (is_pi = {})\n", node, lim_mig.fanout_size( node ), lim_mig.is_pi( node ) );
      }
      return true;
    } );

    if ( count > 0 )
      fmt::print( "--> [mig2] has nodes with fanout > 16 -- this should not happen? \n", count );
    
    if ( ( count_mig == 0 ) && ( mig.num_gates() != lim_mig.num_gates() ) )
      fmt::print( " --> since all nodes of [mig] have fanout <= 16, [mig] and [mig2] needs to have the same size -- why not?\n" );

    fmt::print( "[mig2] size = {} \n", lim_mig.num_gates() );

    /* check if I specify ps = 16 [nothing should change!]*/

    fanout_limit_view_params ps;
    ps.fanout_limit = 16;
    mig_network mig3;
    fanout_limit_view lim_mig2( mig3, ps );

    if ( lorina::read_verilog( ::benchmark_path( benchmark ), verilog_reader( lim_mig2 ) ) != lorina::return_code::success )
    {
      fmt::print( "[e] parse error\n" );
    }
    count = 0u;
    lim_mig2.foreach_node( [&]( const auto& node ) {
      if ( lim_mig2.is_constant( node ) )
        return true; /* next */
      if ( lim_mig2.is_pi( node ) )
        return true; /* next */

      if ( lim_mig2.fanout_size( node ) > 16 )
      {
        count++;
        fmt::print( "[mig3] node {} with fanout_size {} (is_pi = {})\n", node, lim_mig2.fanout_size( node ), lim_mig2.is_pi( node ) );
      }
      return true;
    } );

    if ( count > 0 )
      fmt::print( "--> [mig3] has nodes with fanout > 16 -- this should not happen? \n" );
    if ( ( count_mig == 0 ) && ( mig.num_gates() != lim_mig2.num_gates() ) )
      fmt::print( " --> since all nodes of [mig] have fanout <= 16, [mig] and [mig3] needs to have the same size -- why not?\n" );

    fmt::print( "[mig3] size = {} \n", lim_mig2.num_gates() );

    if ( lim_mig.num_gates() != lim_mig2.num_gates() )
      fmt::print( "---> [mig2] and [mig3] have different number of nodes -- why?\n" );

    /*{
      
      bool const cec = ::abc_cec( mig2, benchmark );
      fmt::print( "[i] cec mig <-> mig2 = {}\n", cec );
    }

    {
      bool const cec = ::abc_cec( mig3, benchmark );
      fmt::print( "[i] cec mig <-> mig3 = {}\n", cec );
    }*/
  }

  return 0;
}
