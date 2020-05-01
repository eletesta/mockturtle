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

/*!
  \file mig_resub.hpp
  \brief Resubstitution

  \author Heinz Riener
*/

#pragma once

#include <algorithm>

#include <mockturtle/algorithms/mig_resub.hpp>
#include <mockturtle/algorithms/resubstitution.hpp>
#include <mockturtle/networks/mig.hpp>

namespace mockturtle
{

/*! \brief Statistics for resubstitution.
 *
 * The data structure `resubstitution_stats` provides data collected by running
 * `resubstitution`.
 */
struct resubstitution_stats_feasible
{
  /*! \brief Total runtime. */
  stopwatch<>::duration time_total{0};

  /*! \brief Accumulated runtime for cut computation. */
  stopwatch<>::duration time_cuts{0};

  /*! \brief Accumulated runtime for cut evaluation/computing a resubsitution. */
  stopwatch<>::duration time_eval{0};

  /*! \brief Accumulated runtime for divisor computation. */
  stopwatch<>::duration time_divs{0};

  /*! \brief Accumulated runtime for updating the network. */
  stopwatch<>::duration time_substitute{0};

  /*! \brief Accumulated runtime for simulation. */
  stopwatch<>::duration time_simulation{0};

  /*! \brief Initial network size (before resubstitution) */
  uint64_t initial_size{0};

  /*! \brief Total number of divisors  */
  uint64_t num_total_divisors{0};

  /*! \brief Total number of leaves  */
  uint64_t num_total_leaves{0};

  /*! \brief Total number of gain  */
  uint64_t estimated_gain{0};

  void report() const
  {
    std::cout << fmt::format( "[i] total time                                                  ({:>5.2f} secs)\n", to_seconds( time_total ) );
    std::cout << fmt::format( "[i]   cut time                                                  ({:>5.2f} secs)\n", to_seconds( time_cuts ) );
    std::cout << fmt::format( "[i]   divs time                                                 ({:>5.2f} secs)\n", to_seconds( time_divs ) );
    std::cout << fmt::format( "[i]   simulation time                                           ({:>5.2f} secs)\n", to_seconds( time_simulation ) );
    std::cout << fmt::format( "[i]   evaluation time                                           ({:>5.2f} secs)\n", to_seconds( time_eval ) );
    std::cout << fmt::format( "[i]   substitute                                                ({:>5.2f} secs)\n", to_seconds( time_substitute ) );
    std::cout << fmt::format( "[i] total divisors            = {:8d}\n", ( num_total_divisors ) );
    std::cout << fmt::format( "[i] total leaves              = {:8d}\n", ( num_total_leaves ) );
    std::cout << fmt::format( "[i] estimated gain            = {:8d} ({:>5.2f}%)\n",
                              estimated_gain, ( ( 100.0 * estimated_gain ) / initial_size ) );
  }
};

namespace detail
{

template<class Ntk, class Simulator, class ResubFn, class TT, class Node_mffc>
class resubstitution_buffers_impl
{
public:
  using node = typename Ntk::node;
  using signal = typename Ntk::signal;

  explicit resubstitution_buffers_impl( Ntk& ntk, resubstitution_params const& ps, resubstitution_stats_feasible& st, typename ResubFn::stats& resub_st )
      : ntk( ntk ), sim( ntk, ps.max_divisors, ps.max_pis ), ps( ps ), st( st ), resub_st( resub_st )
  {
    st.initial_size = ntk.num_gates();

    auto const update_level_of_new_node = [&]( const auto& n ) {
      ntk.resize_levels();
      update_node_level( n );
    };

    auto const update_level_of_existing_node = [&]( node const& n, const auto& old_children ) {
      (void)old_children;
      ntk.resize_levels();
      update_node_level( n );
    };

    auto const update_level_of_deleted_node = [&]( const auto& n ) {
      ntk.set_level( n, -1 );
    };

    ntk._events->on_add.emplace_back( update_level_of_new_node );

    ntk._events->on_modified.emplace_back( update_level_of_existing_node );

    ntk._events->on_delete.emplace_back( update_level_of_deleted_node );
  }

  void run()
  {
    stopwatch t( st.time_total );

    /* start the managers */
    cut_manager<Ntk> mgr( ps.max_pis );

    progress_bar pbar{ntk.size(), "resub |{0}| node = {1:>4}   cand = {2:>4}   est. gain = {3:>5}", ps.progress};

    auto const size = ntk.num_gates();
    std::vector<std::vector<node>> depth_order( ntk.depth() + 1 );
    std::vector<node> ordered;

    ntk.foreach_gate( [&]( auto const& n, auto i ) {
      depth_order[ntk.level( n )].push_back( n );
      return true; /* next gate */
    } );
    for ( auto h = 0u; h < depth_order.size(); h++ )
    {
      for ( auto g = 0u; g < depth_order[h].size(); g++ )
      {
        ordered.push_back( depth_order[h][g] );
      }
    }

    auto i = 0u;
    for ( node n : ordered ) // assume all nodes in the previous levels are already done
    {
      if ( i >= size )
        break; /* terminate */

      pbar( i, i, candidates, st.estimated_gain );
      i++;

      if ( ntk.is_dead( n ) )
        continue; /* next */

      /* skip balanced nodes */
      auto ok_nodes = 0;
      ntk.foreach_fanin( n, [&]( const auto& f ) {
        if ( ntk.level( n ) == ntk.level( ntk.get_node( f ) ) - 1 )
          ok_nodes++;
        return true;
      } );
      if ( ok_nodes == int( ntk.fanin_size( n ) ) )
      {
        continue;
      }

      /* skip nodes with many fanouts */
      if ( ntk.fanout_size( n ) > ps.skip_fanout_limit_for_roots )
        continue; /* next */

      /* compute a reconvergence-driven cut */
      auto const leaves = call_with_stopwatch( st.time_cuts, [&]() {
        return reconv_driven_cut( mgr, ntk, n );
      } );

      /* evaluate this cut */
      auto const g = call_with_stopwatch( st.time_eval, [&]() {
        return evaluate( n, leaves );
      } );
      if ( !g )
      {
        continue; /* next */
      }

      /* update progress bar */
      candidates++;
      st.estimated_gain += last_gain;

      /* update network */
      call_with_stopwatch( st.time_substitute, [&]() {
        ntk.substitute_node( n, *g );
      } );
    }
  }

private:
  void update_node_level( node const& n, bool top_most = true )
  {
    uint32_t curr_level = ntk.level( n );

    uint32_t max_level = 0;
    ntk.foreach_fanin( n, [&]( const auto& f ) {
      auto const p = ntk.get_node( f );
      auto const fanin_level = ntk.level( p );
      if ( fanin_level > max_level )
      {
        max_level = fanin_level;
      }
      return true; /* next fanin */
    } );
    ++max_level;

    if ( curr_level != max_level )
    {
      ntk.set_level( n, max_level );

      /* update only one more level */
      if ( top_most )
      {
        ntk.foreach_fanout( n, [&]( const auto& p ) {
          update_node_level( p, false );
          return true; /* next fanout */
        } );
      }
    }
  }

  void simulate( std::vector<node> const& leaves )
  {
    sim.resize();
    for ( auto i = 0u; i < divs.size(); ++i )
    {
      const auto d = divs.at( i );

      /* skip constant 0 */
      if ( d == 0 )
        continue;

      /* assign leaves to variables */
      if ( i < leaves.size() )
      {
        sim.assign( d, i + 1 );
        continue;
      }

      /* compute truth tables of inner nodes */
      sim.assign( d, i - uint32_t( leaves.size() ) + ps.max_pis + 1 );
      std::vector<typename Simulator::truthtable_t> tts;
      ntk.foreach_fanin( d, [&]( const auto& s, auto i ) {
        (void)i;
        tts.emplace_back( sim.get_tt( ntk.make_signal( ntk.get_node( s ) ) ) ); /* ignore sign */
        return true;                                                            /* next fanin */
      } );

      auto const tt = ntk.compute( d, tts.begin(), tts.end() );
      sim.set_tt( i - uint32_t( leaves.size() ) + ps.max_pis + 1, tt );
    }

    /* normalize truth tables */
    sim.normalize( divs );
  }

  std::optional<signal> evaluate( node const& root, std::vector<node> const& leaves )
  {
    uint32_t const required = std::numeric_limits<uint32_t>::max();

    last_gain = 0;

    Node_mffc collector( ntk );
    auto num_mffc = collector.run( root, leaves, temp );

    /* collect the divisor nodes in the cut */
    bool div_comp_success = call_with_stopwatch( st.time_divs, [&]() {
      return collect_divisors( root, leaves, required );
    } );

    if ( !div_comp_success )
    {
      return std::nullopt;
    }

    /* update statistics */
    st.num_total_divisors += num_divs;
    st.num_total_leaves += leaves.size();

    /* simulate the collected divisors */
    call_with_stopwatch( st.time_simulation, [&]() { simulate( leaves ); } );

    auto care = kitty::create<TT>( static_cast<unsigned int>( leaves.size() ) );
    if ( ps.use_dont_cares )
      care = ~satisfiability_dont_cares( ntk, leaves, ps.window_size );
    else
      care = ~care;

    ResubFn resub_fn( ntk, sim, divs, num_divs, resub_st );
    return resub_fn( root, care, required, ps.max_inserts );
  }

  void collect_divisors_rec( node const& n, std::vector<node>& internal )
  {
    /* skip visited nodes */
    if ( ntk.visited( n ) == ntk.trav_id() )
      return;
    ntk.set_visited( n, ntk.trav_id() );

    ntk.foreach_fanin( n, [&]( const auto& f ) {
      collect_divisors_rec( ntk.get_node( f ), internal );
      return true; /* next fanin */
    } );

    /* collect the internal nodes */
    if ( ntk.value( n ) == 0 && n != 0 ) /* ntk.fanout_size( n ) */
    {
      internal.emplace_back( n );
    }
  }

  bool collect_divisors( node const& root, std::vector<node> const& leaves, uint32_t required )
  {
    /* add the leaves of the cuts to the divisors */
    divs.clear();

    ntk.incr_trav_id();
    for ( const auto& l : leaves )
    {
      divs.emplace_back( l );
      ntk.set_visited( l, ntk.trav_id() );
    }
    /* mark nodes in the MFFC */
    for ( const auto& t : temp )
      ntk.set_value( t, 1 );

    /* collect the cone (without MFFC) */
    collect_divisors_rec( root, divs );

    /* unmark the current MFFC */
    for ( const auto& t : temp )
      ntk.set_value( t, 0 );

    /* check if the number of divisors is not exceeded */
    if ( int( divs.size() + temp.size() - leaves.size() ) >= int( ps.max_divisors - ps.max_pis ) )
    {
      return false;
    }

    /* get the number of divisors to collect */
    int32_t limit = ps.max_divisors - ps.max_pis - ( uint32_t( divs.size() ) + 1 - uint32_t( leaves.size() ) + uint32_t( temp.size() ) );

    /* explore the fanouts, which are not in the MFFC */
    int32_t counter = 0;
    bool quit = false;

    /* NOTE: this is tricky and cannot be converted to a range-based loop */
    auto size = divs.size();
    for ( auto i = 0u; i < size; ++i )
    {
      auto const d = divs.at( i );

      if ( ntk.fanout_size( d ) > ps.skip_fanout_limit_for_divisors )
        continue;

      /* if the fanout has all fanins in the set, add it */
      ntk.foreach_fanout( d, [&]( node const& p ) {
        if ( ntk.visited( p ) == ntk.trav_id() || ntk.level( p ) > required )
          return true; /* next fanout */

        bool all_fanins_visited = true;
        ntk.foreach_fanin( p, [&]( const auto& g ) {
          if ( ntk.visited( ntk.get_node( g ) ) != ntk.trav_id() )
          {
            all_fanins_visited = false;
            return false; /* terminate fanin-loop */
          }
          return true; /* next fanin */
        } );

        if ( !all_fanins_visited )
          return true; /* next fanout */

        bool has_root_as_child = false;
        ntk.foreach_fanin( p, [&]( const auto& g ) {
          if ( ntk.get_node( g ) == root )
          {
            has_root_as_child = true;
            return false; /* terminate fanin-loop */
          }
          return true; /* next fanin */
        } );

        if ( has_root_as_child )
          return true; /* next fanout */

        divs.emplace_back( p );
        ++size;
        ntk.set_visited( p, ntk.trav_id() );

        /* quit computing divisors if there are too many of them */
        if ( ++counter == limit )
        {
          quit = true;
          return false; /* terminate fanout-loop */
        }

        return true; /* next fanout */
      } );

      if ( quit )
        break;
    }

    /* get the number of divisors */
    num_divs = uint32_t( divs.size() );

    /* add the nodes in the MFFC */
    for ( const auto& t : temp )
    {
      divs.emplace_back( t );
    }

    assert( root == divs.at( divs.size() - 1u ) );
    assert( divs.size() - leaves.size() <= ps.max_divisors - ps.max_pis );

    return true;
  }

private:
  Ntk& ntk;
  Simulator sim;

  resubstitution_params const& ps;
  resubstitution_stats_feasible& st;
  typename ResubFn::stats& resub_st;

  /* temporary statistics for progress bar */
  uint32_t candidates{0};
  uint32_t last_gain{0};

  std::vector<node> temp;
  std::vector<node> divs;
  uint32_t num_divs{0};
}; // namespace detail

} // namespace detail

template<typename Ntk, typename Simulator, typename TT>
struct mig_feasible_resub_functor
{
public:
  using node = mig_network::node;
  using signal = mig_network::signal;
  using stats = mig_resub_stats;

public:
  explicit mig_feasible_resub_functor( Ntk& ntk, Simulator const& sim, std::vector<node> const& divs, uint32_t num_divs, stats& st )
      : ntk( ntk ), sim( sim ), divs( divs ), num_divs( num_divs ), st( st )
  {
  }

  std::optional<signal> operator()( node const& root, TT care, uint32_t required, uint32_t max_inserts )
  {
    (void)care;
    assert( is_const0( ~care ) );

    /* consider constants */
    auto g = call_with_stopwatch( st.time_resubC, [&]() {
      return resub_const( root, required );
    } );
    if ( g )
    {
      return g; /* accepted resub */
    }

    only_divs.clear();

    // put required as my maximum depth that I can go down to my divisors
    for ( auto k = 0u; k < divs.size() - 1; k++ )
    {
      only_divs.emplace_back( divs[k] );
    }

    std::sort( only_divs.begin(), only_divs.end(), [&]( node& n1, node& n2 ) {
      return ( ntk.level( n1 ) > ntk.level( n2 ) );
    } );

    /* consider constants */
    g = call_with_stopwatch( st.time_resubC, [&]() {
      return resub_buffers( root, required );
    } );
    /* consider gain in buffer */
    if ( g )
    {
      return g; /* accepted resub */
    }

    return std::nullopt;
  }

  std::optional<signal> resub_const( node const& root, uint32_t required ) const
  {
    (void)required;
    auto const tt = sim.get_tt( ntk.make_signal( root ) );
    if ( tt == sim.get_tt( ntk.get_constant( false ) ) )
    {
      return sim.get_phase( root ) ? ntk.get_constant( true ) : ntk.get_constant( false );
    }
    return std::nullopt;
  }

  std::optional<signal> resub_buffers( node const& root, uint32_t required ) const
  {
    (void)required;
    auto const tt = sim.get_tt( ntk.make_signal( root ) );
    std::vector<signal> children;

    ntk.foreach_fanin( root, [&]( auto const& s ) {
      children.emplace_back( s );
    } );
    std::sort( children.begin(), children.end(), [&]( signal& n1, signal& n2 ) {
      return ( ntk.level( ntk.get_node( n1 ) ) < ntk.level( ntk.get_node( n2 ) ) );
    } );

    if ( ntk.node_to_index( ntk.get_node( children[0] ) ) == 0 )
      return std::nullopt;

    auto flag = false;
    for ( auto i = 0u; i < only_divs.size(); ++i )
    {
      auto const d = only_divs.at( i );
      for ( auto j = 0u; j < children.size(); j++ )
      {
        if ( ntk.get_node( children[j] ) == d )
          flag = true;
      }
      if ( flag == true )
        continue;

      if ( ntk.level( d ) >= ntk.level( root ) )
        continue;

      if ( int( ntk.level( d ) ) <= int( ntk.level( ntk.get_node( children[0] ) ) ) )
        break;

      auto const tt_s0 = sim.get_tt( ntk.make_signal( d ) );
      auto const tt_s1 = sim.get_tt( children[1] );
      auto const tt_s2 = sim.get_tt( children[2] );

      auto const s0 = ntk.make_signal( d );
      auto const s1 = children[1];
      auto const s2 = children[2];

      if ( kitty::ternary_majority( tt_s0, tt_s1, tt_s2 ) == tt )
      {
        auto const a = sim.get_phase( ntk.get_node( s0 ) ) ? !s0 : s0;
        auto const b = sim.get_phase( ntk.get_node( s1 ) ) ? !s1 : s1;
        auto const c = sim.get_phase( ntk.get_node( s2 ) ) ? !s2 : s2;
        return sim.get_phase( root ) ? !ntk.create_maj( a, b, c ) : ntk.create_maj( a, b, c );
      }
    }

    return std::nullopt;
  }

private:
  Ntk& ntk;
  Simulator const& sim;
  std::vector<node> const& divs;
  std::vector<node> only_divs;
  uint32_t const num_divs;
  stats& st;
}; // namespace mockturtle

template<class Ntk>
void mig_feasible_resubstitution( Ntk& ntk, resubstitution_params const& ps = {}, resubstitution_stats_feasible* pst = nullptr )
{
  /* TODO: check if basetype of ntk is aig */
  static_assert( is_network_type_v<Ntk>, "Ntk is not a network type" );
  static_assert( has_clear_values_v<Ntk>, "Ntk does not implement the clear_values method" );
  static_assert( has_fanout_size_v<Ntk>, "Ntk does not implement the fanout_size method" );
  static_assert( has_foreach_fanin_v<Ntk>, "Ntk does not implement the foreach_fanin method" );
  static_assert( has_foreach_gate_v<Ntk>, "Ntk does not implement the foreach_gate method" );
  static_assert( has_foreach_node_v<Ntk>, "Ntk does not implement the foreach_node method" );
  static_assert( has_get_constant_v<Ntk>, "Ntk does not implement the get_constant method" );
  static_assert( has_get_node_v<Ntk>, "Ntk does not implement the get_node method" );
  static_assert( has_is_complemented_v<Ntk>, "Ntk does not implement the is_complemented method" );
  static_assert( has_is_pi_v<Ntk>, "Ntk does not implement the is_pi method" );
  static_assert( has_make_signal_v<Ntk>, "Ntk does not implement the make_signal method" );
  static_assert( has_set_value_v<Ntk>, "Ntk does not implement the set_value method" );
  static_assert( has_set_visited_v<Ntk>, "Ntk does not implement the set_visited method" );
  static_assert( has_size_v<Ntk>, "Ntk does not implement the has_size method" );
  static_assert( has_substitute_node_v<Ntk>, "Ntk does not implement the has substitute_node method" );
  static_assert( has_value_v<Ntk>, "Ntk does not implement the has_value method" );
  static_assert( has_visited_v<Ntk>, "Ntk does not implement the has_visited method" );

  using resub_view_t = fanout_view<depth_view<Ntk>>;
  depth_view<Ntk> depth_view{ntk};
  resub_view_t resub_view{depth_view};

  resubstitution_stats_feasible st;
  if ( ps.max_pis == 8 )
  {
    using truthtable_t = kitty::static_truth_table<8>;
    using truthtable_dc_t = kitty::dynamic_truth_table;
    using simulator_t = detail::simulator<resub_view_t, truthtable_t>;
    using node_mffc_t = detail::node_mffc_inside<Ntk>;
    using resubstitution_functor_t = mig_feasible_resub_functor<resub_view_t, simulator_t, truthtable_dc_t>;
    typename resubstitution_functor_t::stats resub_st;
    detail::resubstitution_buffers_impl<resub_view_t, simulator_t, resubstitution_functor_t, truthtable_dc_t, node_mffc_t> p( resub_view, ps, st, resub_st );
    p.run();
    if ( ps.verbose )
    {
      st.report();
      resub_st.report();
    }
  }
  else
  {
    using truthtable_t = kitty::dynamic_truth_table;
    using simulator_t = detail::simulator<resub_view_t, truthtable_t>;
    using node_mffc_t = detail::node_mffc_inside<Ntk>;
    using resubstitution_functor_t = mig_feasible_resub_functor<resub_view_t, simulator_t, truthtable_t>;
    typename resubstitution_functor_t::stats resub_st;
    detail::resubstitution_buffers_impl<resub_view_t, simulator_t, resubstitution_functor_t, truthtable_t, node_mffc_t> p( resub_view, ps, st, resub_st );
    p.run();
    if ( ps.verbose )
    {
      st.report();
      resub_st.report();
    }
  }

  if ( pst )
  {
    *pst = st;
  }
}

} // namespace mockturtle
