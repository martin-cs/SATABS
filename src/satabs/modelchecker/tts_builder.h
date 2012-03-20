/*******************************************************************\

Module: Thread Transition System Output

Author: Michael Tautschnig

  Date: January 2012

\*******************************************************************/

#ifndef CPROVER_CEGAR_TTS_BUILDER_H
#define CPROVER_CEGAR_TTS_BUILDER_H

#include <string>
#include <map>
#include <vector>
#include <fstream>
#include <list>

#include <mp_arith.h>

#include <solvers/prop/literal.h>

#include "satabs/abstractor/abstract_program.h"

class tts_buildert
{
  public:
  tts_buildert(
      const bool _build_tts,
      const std::string &file_name);

  void add_local_var(unsigned var);
  void add_shared_var(unsigned var);

  void build_prologue(
      abstract_programt const& abstract_program);

  void build_instruction(
    const abstract_programt::instructionst::const_iterator &it,
    const unsigned BP_PC);

  private:
  std::vector<unsigned> sdim;
  std::vector<unsigned> ldim;
  std::vector<unsigned> state_offset;
  bool in_atomic_sect;
  std::ofstream out_tts;
  std::map< abstract_programt::instructionst::const_iterator,
    unsigned > PC_map;
  mp_integer shared_error_num;
  mp_integer local_error_num;
  mp_integer pc_multiplier;

  static void inc_state(std::vector<bool> &states);
  static void inc_state_symmetric(std::vector<bool> &states);
  void get_shared_state_num(
      const bool m,
      const bool ts,
      const std::vector<bool> &state,
      const bool post_state,
      mp_integer &dest) const;
  void get_local_state_num(
      const unsigned PC,
      const std::vector<bool> &state,
      const bool post_state,
      mp_integer &dest) const;
  void to_cnf(
      const std::list<exprt> &constraints,
      std::list<bvt> &cnf);
  void to_cnf(
      const exprt &guard,
      bvt &clause,
      const bool negate);
  bool cnf_sat(
      const std::vector<bool> &state,
      const std::list<bvt> &cnf,
      bool &is_nondet) const;
  bool clause_sat(
      const std::vector<bool> &state,
      const bvt &clause,
      bool &is_nondet) const;
  void print_shared_state(
      const bool m,
      const bool ts,
      const std::vector<bool> &state,
      const bool is_post);
  void print_local_state(
      const unsigned PC,
      const std::vector<bool> &state,
      const bool is_post);
  void print_tuples(
      const std::vector<bool> &state,
      const bool m1,
      const bool ts1,
      const unsigned PC1,
      const bool m2,
      const bool ts2,
      const unsigned PC2);

  bool skip_make_assign(
      const std::vector<bool> &state,
      const std::vector<bool> &assigned) const;

  void make_skip(
      const unsigned PC);
  void make_atomic(
      const unsigned PC,
      const bool is_end);
  void make_assert(
      const unsigned PC,
      const std::list<exprt> &constraints);
  void make_assume(
      const unsigned PC,
      const std::list<exprt> &constraints);
  void make_goto(
      const unsigned PC,
      const std::list<exprt> &constraints,
      const unsigned target);
  void make_start_thread(
      const unsigned PC,
      const unsigned target);
  void make_assign(
      const unsigned PC,
      const std::vector<bool> &assigned,
      const std::list<exprt> &constraints);
};

#endif
