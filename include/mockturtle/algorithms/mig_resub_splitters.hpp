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

#include <mockturtle/algorithms/mig_resub.hpp>
#include <mockturtle/algorithms/resubstitution.hpp>
#include <mockturtle/networks/mig.hpp>

namespace mockturtle
{

template<typename Ntk, typename Simulator, typename TT>
struct mig_resub_splitters_functor
{
public:
  using node = mig_network::node;
  using signal = mig_network::signal;
  using stats = mig_resub_stats;

  struct unate_divisors
  {
    std::vector<signal> positive_divisors0;
    std::vector<signal> positive_divisors1;
    std::vector<signal> negative_divisors0;
    std::vector<signal> negative_divisors1;
    std::vector<signal> next_candidates;

    void clear()
    {
      positive_divisors0.clear();
      positive_divisors1.clear();
      negative_divisors0.clear();
      negative_divisors1.clear();
      next_candidates.clear();
    }
  };

public:
  explicit mig_resub_splitters_functor( Ntk& ntk, Simulator const& sim, std::vector<node> const& divs, uint32_t num_divs, stats& st )
      : ntk( ntk ), sim( sim ), divs( divs ), num_divs( num_divs ), st( st )
  {
  }

  std::optional<signal> operator()( node const& root, TT care, uint32_t required, uint32_t max_inserts, uint32_t num_mffc, uint32_t& last_gain )
  {
    (void)care;
    assert( is_const0( ~care ) );

    /* consider constants */
    auto g = call_with_stopwatch( st.time_resubC, [&]() {
      return resub_const( root, required );
    } );
    if ( g )
    {
      ++st.num_const_accepts;
      last_gain = num_mffc;
      return g; /* accepted resub */
    }

    /* consider equal nodes */
    g = call_with_stopwatch( st.time_resub0, [&]() {
      return resub_div0( root, required );
    } );
    if ( g )
    {
      ++st.num_div0_accepts;
      last_gain = num_mffc;
      return g; /* accepted resub */
    }

    /* consider relevance optimization */
    g = call_with_stopwatch( st.time_resubR, [&]() {
      return resub_divR( root, required );
    } );
    if ( g )
    {
      ++st.num_divR_accepts;
      last_gain = num_mffc;
      return g; /* accepted resub */
    }

    if ( max_inserts == 0 || num_mffc == 1 )
      return std::nullopt;

    /* collect level one divisors */
    call_with_stopwatch( st.time_collect_unate_divisors, [&]() {
      collect_unate_divisors( root, required );
    } );

    /* consider equal nodes */
    g = call_with_stopwatch( st.time_resub1, [&]() {
      return resub_div1( root, required );
    } );
    if ( g )
    {
      ++st.num_div1_accepts;
      last_gain = num_mffc - 1;
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

  std::optional<signal> resub_div0( node const& root, uint32_t required ) const
  {
    (void)required;
    auto const tt = sim.get_tt( ntk.make_signal( root ) );
    for ( auto i = 0u; i < num_divs; ++i )
    {
      auto const d = divs.at( i );
      if ( !ntk.is_pi( d ) )
      {
        if ( (  ntk.fanout_size( d ) == 4 ) || (  ntk.fanout_size( d )  >= 16 ) || (  ntk.fanout_size( d )  == 1 ) ) // it would mean the depth is actually increased
          continue;
        auto fanout = ntk.fanout_size( root ) ;
        if ( ( ntk.fanout_size( d ) < 4 ) && (  ntk.fanout_size( d ) + fanout  > 4 ) )
          continue;
        else if ( (  ntk.fanout_size( d )  < 16 ) && (  ntk.fanout_size( d )  > 4 ) && (  ntk.fanout_size( d ) + fanout  > 16 ) )
          continue;
      }

      if ( tt != sim.get_tt( ntk.make_signal( d ) ) )
        continue; /* next */

      return ( sim.get_phase( d ) ^ sim.get_phase( root ) ) ? !ntk.make_signal( d ) : ntk.make_signal( d );
    }

    return std::nullopt;
  }

  std::optional<signal> resub_divR( node const& root, uint32_t required )
  {
    (void)required;

    std::vector<signal> fs;
    ntk.foreach_fanin( root, [&]( const auto& f ) {
      fs.emplace_back( f );
    } );

    for ( auto i = 0u; i < divs.size(); ++i )
    {
      auto const& d0 = divs.at( i );

      if ( !ntk.is_pi( d0 ) )
      {
        if ( (  ntk.fanout_size( d0 ) == 4 ) || (  ntk.fanout_size( d0 ) >= 16 ) || (  ntk.fanout_size( d0 )  == 1 ) ) // it would mean the depth is actually increased
          continue;
      }

      auto const& s = ntk.make_signal( d0 );
      auto const& tt = sim.get_tt( s );

      if ( d0 == root )
        break;

      auto const tt0 = sim.get_tt( fs[0] );
      auto const tt1 = sim.get_tt( fs[1] );
      auto const tt2 = sim.get_tt( fs[2] );

      if ( ntk.get_node( fs[0] ) != d0 && ntk.fanout_size( ntk.get_node( fs[0] ) ) == 1 && relevance( tt0, tt1, tt2, tt ) )
      {
        auto const b = sim.get_phase( ntk.get_node( fs[1] ) ) ? !fs[1] : fs[1];
        auto const c = sim.get_phase( ntk.get_node( fs[2] ) ) ? !fs[2] : fs[2];

        return sim.get_phase( root ) ? !ntk.create_maj( sim.get_phase( d0 ) ? !s : s, b, c ) : ntk.create_maj( sim.get_phase( d0 ) ? !s : s, b, c );
      }
      else if ( ntk.get_node( fs[1] ) != d0 && ntk.fanout_size( ntk.get_node( fs[1] ) ) == 1 && relevance( tt1, tt0, tt2, tt ) )
      {
        auto const a = sim.get_phase( ntk.get_node( fs[0] ) ) ? !fs[0] : fs[0];
        auto const c = sim.get_phase( ntk.get_node( fs[2] ) ) ? !fs[2] : fs[2];

        return sim.get_phase( root ) ? !ntk.create_maj( sim.get_phase( d0 ) ? !s : s, a, c ) : ntk.create_maj( sim.get_phase( d0 ) ? !s : s, a, c );
      }
      else if ( ntk.get_node( fs[2] ) != d0 && ntk.fanout_size( ntk.get_node( fs[2] ) ) == 1 && relevance( tt2, tt0, tt1, tt ) )
      {
        auto const a = sim.get_phase( ntk.get_node( fs[0] ) ) ? !fs[0] : fs[0];
        auto const b = sim.get_phase( ntk.get_node( fs[1] ) ) ? !fs[1] : fs[1];

        return sim.get_phase( root ) ? !ntk.create_maj( sim.get_phase( d0 ) ? !s : s, a, b ) : ntk.create_maj( sim.get_phase( d0 ) ? !s : s, a, b );
      }
      else if ( ntk.get_node( fs[0] ) != d0 && ntk.fanout_size( ntk.get_node( fs[0] ) ) == 1 && relevance( ~tt0, tt1, tt2, tt ) )
      {
        auto const b = sim.get_phase( ntk.get_node( fs[1] ) ) ? !fs[1] : fs[1];
        auto const c = sim.get_phase( ntk.get_node( fs[2] ) ) ? !fs[2] : fs[2];

        return sim.get_phase( root ) ? !ntk.create_maj( sim.get_phase( d0 ) ? s : !s, b, c ) : ntk.create_maj( sim.get_phase( d0 ) ? s : !s, b, c );
      }
      else if ( ntk.get_node( fs[1] ) != d0 && ntk.fanout_size( ntk.get_node( fs[1] ) ) == 1 && relevance( ~tt1, tt0, tt2, tt ) )
      {
        auto const a = sim.get_phase( ntk.get_node( fs[0] ) ) ? !fs[0] : fs[0];
        auto const c = sim.get_phase( ntk.get_node( fs[2] ) ) ? !fs[2] : fs[2];

        return sim.get_phase( root ) ? !ntk.create_maj( sim.get_phase( d0 ) ? s : !s, a, c ) : ntk.create_maj( sim.get_phase( d0 ) ? s : !s, a, c );
      }
      else if ( ntk.get_node( fs[2] ) != d0 && ntk.fanout_size( ntk.get_node( fs[2] ) ) == 1 && relevance( ~tt2, tt0, tt1, tt ) )
      {
        auto const a = sim.get_phase( ntk.get_node( fs[0] ) ) ? !fs[0] : fs[0];
        auto const b = sim.get_phase( ntk.get_node( fs[1] ) ) ? !fs[1] : fs[1];

        return sim.get_phase( root ) ? !ntk.create_maj( sim.get_phase( d0 ) ? s : !s, a, b ) : ntk.create_maj( sim.get_phase( d0 ) ? s : !s, a, b );
      }
    }

    return std::nullopt;
  }

  void collect_unate_divisors( node const& root, uint32_t required )
  {
    udivs.clear();

    auto const& tt = sim.get_tt( ntk.make_signal( root ) );
    for ( auto i = 0u; i < num_divs; ++i )
    {
      auto const d0 = divs.at( i );
      if ( ntk.level( d0 ) > required - 1 )
        continue;

      for ( auto j = i + 1; j < num_divs; ++j )
      {
        auto const d1 = divs.at( j );
        if ( ntk.level( d1 ) > required - 1 )
          continue;

        auto const& tt_s0 = sim.get_tt( ntk.make_signal( d0 ) );
        auto const& tt_s1 = sim.get_tt( ntk.make_signal( d1 ) );

        /* Boolean filtering rule for MAJ-3 */
        if ( kitty::ternary_majority( tt_s0, tt_s1, tt ) == tt )
        {
          udivs.positive_divisors0.emplace_back( ntk.make_signal( d0 ) );
          udivs.positive_divisors1.emplace_back( ntk.make_signal( d1 ) );
          continue;
        }

        if ( kitty::ternary_majority( ~tt_s0, tt_s1, tt ) == tt )
        {
          udivs.negative_divisors0.emplace_back( ntk.make_signal( d0 ) );
          udivs.negative_divisors1.emplace_back( ntk.make_signal( d1 ) );
          continue;
        }

        if ( std::find( udivs.next_candidates.begin(), udivs.next_candidates.end(), ntk.make_signal( d1 ) ) == udivs.next_candidates.end() )
          udivs.next_candidates.emplace_back( ntk.make_signal( d1 ) );
      }

      if ( std::find( udivs.next_candidates.begin(), udivs.next_candidates.end(), ntk.make_signal( d0 ) ) == udivs.next_candidates.end() )
        udivs.next_candidates.emplace_back( ntk.make_signal( d0 ) );
    }
  }

  std::optional<signal> resub_div1( node const& root, uint32_t required )
  {
    (void)required;
    auto const& tt = sim.get_tt( ntk.make_signal( root ) );

    /* check for positive unate divisors */
    for ( auto i = 0u; i < udivs.positive_divisors0.size(); ++i )
    {
      auto const s0 = udivs.positive_divisors0.at( i );
      auto const s1 = udivs.positive_divisors1.at( i );

      if ( !ntk.is_pi( ntk.get_node( s0 ) ) )
      {
        if ( (  ntk.fanout_size( ntk.get_node( s0 ) )  == 4 ) || ( ntk.fanout_size( ntk.get_node( s0 ) )  >= 16 ) || (  ntk.fanout_size( ntk.get_node( s0 ) )  == 1 ) ) // it would mean the depth is actually increased
          continue;
      }
      if ( !ntk.is_pi( ntk.get_node( s1 ) ) )
      {
        if ( (  ntk.fanout_size( ntk.get_node( s1 ) ) == 4 ) || (  ntk.fanout_size( ntk.get_node( s1 ) )  >= 16 ) || (  ntk.fanout_size( ntk.get_node( s1 ) )  == 1 ) ) // it would mean the depth is actually increased
          continue;
      }

      for ( auto j = i + 1; j < udivs.positive_divisors0.size(); ++j )
      {
        auto s2 = udivs.positive_divisors0.at( j );
        if ( !ntk.is_pi( ntk.get_node( s2 ) ) )
        {
          if ( (  ntk.fanout_size( ntk.get_node( s2 ) )  == 4 ) || (  ntk.fanout_size( ntk.get_node( s2 ) )  >= 16 ) || (  ntk.fanout_size( ntk.get_node( s2 ) )  == 1 ) ) // it would mean the depth is actually increased
            continue;
        }

        auto const& tt_s0 = sim.get_tt( s0 );
        auto const& tt_s1 = sim.get_tt( s1 );
        auto tt_s2 = sim.get_tt( s2 );

        if ( kitty::ternary_majority( tt_s0, tt_s1, tt_s2 ) == tt )
        {
          // ++st.num_div1_maj_accepts;
          auto const a = sim.get_phase( ntk.get_node( s0 ) ) ? !s0 : s0;
          auto const b = sim.get_phase( ntk.get_node( s1 ) ) ? !s1 : s1;
          auto const c = sim.get_phase( ntk.get_node( s2 ) ) ? !s2 : s2;
          auto e = ntk.create_maj( a, b, c );
          if ( (  ntk.fanout_size( ntk.get_node( e ) )  == 2 ) || (  ntk.fanout_size( ntk.get_node( e ) )  == 5 ) || (  ntk.fanout_size( ntk.get_node( e ) )  > 16 ) )
          {
            continue;
          }
          else
            return sim.get_phase( root ) ? !e : e;
        }

        s2 = udivs.positive_divisors1.at( j );
        if ( !ntk.is_pi( ntk.get_node( s2 ) ) )
        {
          if ( (  ntk.fanout_size( ntk.get_node( s2 ) )  == 4 ) || (  ntk.fanout_size( ntk.get_node( s2 ) ) >= 16 ) || (  ntk.fanout_size( ntk.get_node( s2 ) )  == 1 ) )
            continue;
        }
        tt_s2 = sim.get_tt( s2 );

        if ( kitty::ternary_majority( tt_s0, tt_s1, tt_s2 ) == tt )
        {
          // ++st.num_div1_maj_accepts;
          auto const a = sim.get_phase( ntk.get_node( s0 ) ) ? !s0 : s0;
          auto const b = sim.get_phase( ntk.get_node( s1 ) ) ? !s1 : s1;
          auto const c = sim.get_phase( ntk.get_node( s2 ) ) ? !s2 : s2;
          auto e = ntk.create_maj( a, b, c );
          if ( ( ntk.fanout_size( ntk.get_node( e ) )  == 2 ) || (  ntk.fanout_size( ntk.get_node( e ) )  == 5 ) || ( ntk.fanout_size( ntk.get_node( e ) )  > 16 ) )
            continue;
          else
            return sim.get_phase( root ) ? !e : e;
        }
      }
    }

    /* check for negative unate divisors */
    for ( auto i = 0u; i < udivs.negative_divisors0.size(); ++i )
    {
      auto const s0 = udivs.negative_divisors0.at( i );
      if ( !ntk.is_pi( ntk.get_node( s0 ) ) )
      {
        if ( (  ntk.fanout_size( ntk.get_node( s0 ) )  == 4 ) || ( ntk.fanout_size( ntk.get_node( s0 ) )  >= 16 ) || (  ntk.fanout_size( ntk.get_node( s0 ) )  == 1 ) ) // it would mean the depth is actually increased
          continue;
      }
      auto const s1 = udivs.negative_divisors1.at( i );
      if ( !ntk.is_pi( ntk.get_node( s1 ) ) )
      {
        if ( (  ntk.fanout_size( ntk.get_node( s1 ) ) == 4 ) || (  ntk.fanout_size( ntk.get_node( s1 ) )  >= 16 ) || (  ntk.fanout_size( ntk.get_node( s1 ) )  == 1 ) ) // it would mean the depth is actually increased
          continue;
      }

      for ( auto j = i + 1; j < udivs.negative_divisors0.size(); ++j )
      {
        auto s2 = udivs.negative_divisors0.at( j );
        if ( !ntk.is_pi( ntk.get_node( s2 ) ) )
        {
          if ( (  ntk.fanout_size( ntk.get_node( s2 ) )  == 4 ) || (  ntk.fanout_size( ntk.get_node( s2 ) ) >= 16 ) || (  ntk.fanout_size( ntk.get_node( s2 ) )  == 1 ) )
            continue;
        }

        auto const& tt_s0 = sim.get_tt( s0 );
        auto const& tt_s1 = sim.get_tt( s1 );
        auto tt_s2 = sim.get_tt( s2 );

        if ( kitty::ternary_majority( ~tt_s0, tt_s1, tt_s2 ) == tt )
        {
          // ++st.num_div1_maj_accepts;
          auto const a = sim.get_phase( ntk.get_node( s0 ) ) ? !s0 : s0;
          auto const b = sim.get_phase( ntk.get_node( s1 ) ) ? !s1 : s1;
          auto const c = sim.get_phase( ntk.get_node( s2 ) ) ? !s2 : s2;
          auto e = ntk.create_maj( !a, b, c );
          if ( ( ntk.fanout_size( ntk.get_node( e ) )  == 2 ) || (  ntk.fanout_size( ntk.get_node( e ) )  == 5 ) || ( ntk.fanout_size( ntk.get_node( e ) )  > 16 ) )
            continue;
          else
            return sim.get_phase( root ) ? !e : e;
        }

        s2 = udivs.negative_divisors1.at( j );
        if ( !ntk.is_pi( ntk.get_node( s2 ) ) )
        {
          if ( (  ntk.fanout_size( ntk.get_node( s2 ) )  == 4 ) || (  ntk.fanout_size( ntk.get_node( s2 ) ) >= 16 ) || (  ntk.fanout_size( ntk.get_node( s2 ) )  == 1 ) )
            continue;
        }
        tt_s2 = sim.get_tt( s2 );

        if ( kitty::ternary_majority( ~tt_s0, tt_s1, tt_s2 ) == tt )
        {
          // ++st.num_div1_maj_accepts;
          auto const a = sim.get_phase( ntk.get_node( s0 ) ) ? !s0 : s0;
          auto const b = sim.get_phase( ntk.get_node( s1 ) ) ? !s1 : s1;
          auto const c = sim.get_phase( ntk.get_node( s2 ) ) ? !s2 : s2;
          auto e = ntk.create_maj( !a, b, c );
          if ( ( ntk.fanout_size( ntk.get_node( e ) )  == 2 ) || (  ntk.fanout_size( ntk.get_node( e ) )  == 5 ) || ( ntk.fanout_size( ntk.get_node( e ) )  > 16 ) )
            continue;
          else
            return sim.get_phase( root ) ? !e : e;
        }
      }
    }

    return std::nullopt;
  }

private:
  Ntk& ntk;
  Simulator const& sim;
  std::vector<node> const& divs;
  uint32_t const num_divs;
  stats& st;

  unate_divisors udivs;
}; /* mig_resub_functor */

template<class Ntk, class NodeCostFn>
void mig_resubstitution_splitters( depth_view<Ntk, NodeCostFn>& ntk, resubstitution_params const& ps = {}, resubstitution_stats* pst = nullptr )
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

  using resub_view_t = fanout_view<depth_view<Ntk, NodeCostFn>>;
  //depth_view_params ps_d;
  //depth_view<Ntk> depth_view{ntk, ::detail::fanout_cost_depth<Ntk>(), ps_d};
  resub_view_t resub_view{ntk};

  resubstitution_stats st;
  if ( ps.max_pis == 8 )
  {
    using truthtable_t = kitty::static_truth_table<8>;
    using truthtable_dc_t = kitty::dynamic_truth_table;
    using simulator_t = detail::simulator<resub_view_t, truthtable_t>;
    using node_mffc_t = detail::node_mffc_inside<Ntk>;
    using resubstitution_functor_t = mig_resub_splitters_functor<resub_view_t, simulator_t, truthtable_dc_t>;
    typename resubstitution_functor_t::stats resub_st;
    detail::resubstitution_impl<resub_view_t, simulator_t, resubstitution_functor_t, truthtable_dc_t, node_mffc_t> p( resub_view, ps, st, resub_st );
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
    using resubstitution_functor_t = mig_resub_splitters_functor<resub_view_t, simulator_t, truthtable_t>;
    typename resubstitution_functor_t::stats resub_st;
    detail::resubstitution_impl<resub_view_t, simulator_t, resubstitution_functor_t, truthtable_t, node_mffc_t> p( resub_view, ps, st, resub_st );
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

} /* namespace mockturtle */