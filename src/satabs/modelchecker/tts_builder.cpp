/*******************************************************************\

Module: Thread Transition System Output

Author: Michael Tautschnig

Date: January 2012

\*******************************************************************/

#include "tts_builder.h"

#include <iostream>
#include <fstream>

#include <string2int.h>
#include <arith_tools.h>
#include <std_expr.h>

#include "../abstractor/concurrency_aware_abstract_transition_relation.h"

#define COMMENTS
#define DEBUG
// #define SKIPS

/*******************************************************************\

Function: tts_buildert::tts_buildert

Inputs:

Outputs:

Purpose:

\*******************************************************************/

tts_buildert::tts_buildert(
    const bool _build_tts,
    const std::string &_file_name) :
  sdim(),
  ldim(),
  in_atomic_sect(false),
  build_tts(_build_tts),
  file_name(_file_name)
{
}

/*******************************************************************\

Function: tts_buildert::add_local_var

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void tts_buildert::add_local_var(unsigned var)
{
  assert(state_offset.empty());
  ldim.push_back(var);
}

/*******************************************************************\

Function: tts_buildert::add_shared_var

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void tts_buildert::add_shared_var(unsigned var)
{
  assert(state_offset.empty());
  sdim.push_back(var);
}

/*******************************************************************\

Function: tts_buildert::build_prologue

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void tts_buildert::build_prologue(
    abstract_programt const& abstract_program)
{
  if(!build_tts)
    return;

  const unsigned offset=sdim.size()+ldim.size();
  unsigned num_passive=0;

  for(abstract_programt::instructionst::const_iterator
      it=abstract_program.instructions.begin();
      it!=abstract_program.instructions.end();
      it++)
  {
    switch(it->type)
    {
      case GOTO:
      case START_THREAD:
      case ASSERT:
      case ASSUME:
      case ATOMIC_BEGIN:
      case ATOMIC_END:
      case END_THREAD:
      case END_FUNCTION:
      case DEAD:
      case FUNCTION_CALL:
      case RETURN:
      case CATCH:
      case THROW:
      case NO_INSTRUCTION_TYPE:
        PC_map.insert(std::make_pair(it, PC_map.size()+offset));
        break;
      case ASSIGN:
      case DECL:
      case OTHER:
        {
          concurrency_aware_abstract_transition_relationt* ct=
            dynamic_cast<concurrency_aware_abstract_transition_relationt*>(
                &(it->code.get_transition_relation()));
          if(!it->code.get_transition_relation().values.empty() ||
              (ct && !ct->passive_values.empty()) ||
              it->is_target())
            PC_map.insert(std::make_pair(it, PC_map.size()+offset));

          if(ct && !ct->passive_values.empty()) ++num_passive;
        }
        break;
      case SKIP:
      case LOCATION:
        if(it->is_target())
          PC_map.insert(std::make_pair(it, PC_map.size()+offset));
        break;
    }
#ifdef SKIPS
    if(PC_map.find(it)==PC_map.end())
      PC_map.insert(std::make_pair(it, PC_map.size()+offset));
#endif
  }

  PC_min=offset;
  PC_max=PC_map.size()+offset-1;

  mp_integer n_local=PC_max+1;
  pc_multiplier=power(2, ldim.size());
  n_local*=pc_multiplier;
  local_error_num=n_local;
  ++n_local; // error state
  shared_error_num=power(2, sdim.size()+2); // in-atomic-sect, thread-spawn

#ifdef COMMENTS
  out_tts << "# error state is shared num $#E"
    << " local num " << local_error_num << std::endl;
  out_tts << "# local state num is pc*" << pc_multiplier << "+localstate" << std::endl;
  out_tts << "# maximum pc is " << PC_max << std::endl;
  std::set<mp_integer> locals_seen, shared_seen;
  for(std::vector<bool> states((2*sdim.size())+(2*ldim.size())+1, false);
      !*states.rbegin();
      inc_state_symmetric(states))
  {
    mp_integer num;

    get_shared_state_num(false, false, states, false, num);
    if(shared_seen.insert(num).second)
    {
      out_tts << "# shared state " << num << ":";
      print_shared_state(false, false, states, false);
      out_tts << std::endl;
    }
    get_shared_state_num(true, false, states, false, num);
    if(shared_seen.insert(num).second)
    {
      out_tts << "# shared state " << num << ":";
      print_shared_state(true, false, states, false);
      out_tts << std::endl;
    }

    get_local_state_num(0, states, false, num);
    if(locals_seen.insert(num).second)
    {
      out_tts << "# local state " << num << ":";
      print_local_state(0, states, false);
      out_tts << std::endl;
    }
  }
#endif

  out_tts << "$#S" << " " << n_local << std::endl;

  state_offset.resize(sdim.size()+ldim.size(), (unsigned)-1);
  unsigned PC=0;
  for(std::vector<unsigned>::const_iterator s_it=sdim.begin();
      s_it!=sdim.end(); ++s_it)
  {
#ifdef COMMENTS
    out_tts << "# nondet init shared var " << *s_it << std::endl;
#endif
    assert(*s_it<state_offset.size());
    state_offset[*s_it]=PC;

    std::vector<bool> assigned(state_offset.size(), false);
    assigned[*s_it]=true;
    std::list<exprt> constraints;
    make_assign(PC++, assigned, constraints);
  }

  for(std::vector<unsigned>::const_iterator s_it=ldim.begin();
      s_it!=ldim.end(); ++s_it)
  {
#ifdef COMMENTS
    out_tts << "# nondet init local var " << *s_it << std::endl;
#endif
    assert(*s_it<state_offset.size());
    state_offset[*s_it]=PC;

    std::vector<bool> assigned(state_offset.size(), false);
    assigned[*s_it]=true;
    std::list<exprt> constraints;
    make_assign(PC++, assigned, constraints);
  }
}

/*******************************************************************\

Function: tts_buildert::finalize

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void tts_buildert::finalize()
{
  if(!build_tts)
    return;

  std::ofstream ofs(file_name.c_str());
  const std::string str=out_tts.str();
  out_tts.clear();

  for(std::string::const_iterator c=str.begin();
      c!=str.end();
      ++c)
  {
    if(*c=='$' && c+1!=str.end() && c+2!=str.end() &&
        *(c+1)=='#' && (*(c+2)=='E' || *(c+2)=='S'))
    {
      if(*(c+2)=='E')
        ofs << shared_error_num; // shared error state
      else
        ofs << (shared_error_num+1);

      c+=2;
      continue;
    }

    ofs << *c;
  }
}

/*******************************************************************\

Function: tts_buildert::build_instruction

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void tts_buildert::build_instruction(
    const abstract_programt::instructionst::const_iterator &it,
    const unsigned BP_PC)
{
  if(!build_tts)
    return;

  std::map< abstract_programt::instructionst::const_iterator,
    unsigned >::const_iterator PC_map_entry=PC_map.find(it);
  if(PC_map_entry==PC_map.end()) // maybe a skip
    return;

#ifdef COMMENTS
  out_tts << "# BP-PC" << BP_PC << ": "
    << it->type << " at " << it->location << std::endl;
#endif

  const unsigned PC=PC_map_entry->second;
  std::list<exprt> constraints=
    it->code.get_transition_relation().constraints;

  switch(it->type)
  {
    case GOTO:
      assert(it->targets.size()==1);
      assert(PC_map.find(it->targets.front())!=PC_map.end());
      assert(constraints.size()<=1);
      if(constraints.empty()) // ignore guard if non-empty
        constraints.push_front(it->guard);
      make_goto(PC, constraints, PC_map[it->targets.front()]);
      break;
    case START_THREAD:
      assert(constraints.empty());
      assert(it->targets.size()==1);
      assert(PC_map.find(it->targets.front())!=PC_map.end());
      make_start_thread(PC, PC_map[it->targets.front()]);
      break;
    case ASSUME:
      constraints.push_front(it->guard);
      make_assume(PC, constraints);
      break;
    case ASSERT:
      assert(constraints.empty());
      constraints.push_front(it->guard);
      make_assert(PC, constraints);
      break;
    case ATOMIC_BEGIN:
      assert(constraints.empty());
      make_atomic(PC, false);
      break;
    case ATOMIC_END:
      assert(constraints.empty());
      make_atomic(PC, true);
      break;
    case ASSIGN:
    case DECL:
    case OTHER:
      {
        concurrency_aware_abstract_transition_relationt* ct=
          dynamic_cast<concurrency_aware_abstract_transition_relationt*>(
              &(it->code.get_transition_relation()));

        if(it->code.get_transition_relation().values.empty() &&
            (!ct || ct->passive_values.empty()))
          make_skip(PC);
        else
        {
          std::vector<bool> assigned(state_offset.size(), false);

          for(abstract_transition_relationt::valuest::const_iterator
              v_it=it->code.get_transition_relation().values.begin();
              v_it!=it->code.get_transition_relation().values.end();
              ++v_it)
          {
            assigned[v_it->first]=true;
            const exprt &value=v_it->second;
            if(!value.is_nil() && value.id()!=ID_nondet_bool)
            {
              if(value.is_constant())
              {
                exprt pns=exprt(ID_predicate_next_symbol, bool_typet());
                pns.set(ID_identifier, v_it->first);
                constraints.push_back(pns);
                if(value.is_false())
                  constraints.back().make_not();
              }
              else if(value.id()==ID_predicate_symbol ||
                  value.id()==ID_or || value.id()==ID_not ||
                  value.id()==ID_and)
              {
                // !value | pns(v_it->first)
                // & value | !pns(v_it->first)
                exprt pns=exprt(ID_predicate_next_symbol, bool_typet());
                pns.set(ID_identifier, v_it->first);
                constraints.push_back(or_exprt(value, pns));
                constraints.back().op0().make_not();
                constraints.push_back(or_exprt(value, pns));
                constraints.back().op1().make_not();
              }
              else
              {
                std::cerr << v_it->second.pretty() << std::endl;
                assert(false); // not yet implemented
              }
            }
          }

          if(!ct || ct->passive_values.empty())
          {
            make_assign(PC, assigned, constraints);
          }
          else
          {
            assert(!it->code.get_transition_relation().values.empty());

            std::vector<bool> assigned_passive(state_offset.size(), false);
            std::list<exprt> constraints_passive=
              it->code.get_transition_relation().constraints;

            for(abstract_transition_relationt::valuest::const_iterator
                v_it=ct->passive_values.begin();
                v_it!=ct->passive_values.end();
                ++v_it)
            {
              assigned_passive[v_it->first]=true;
              const exprt &value=v_it->second;
              if(!value.is_nil() && value.id()!=ID_nondet_bool)
              {
                if(value.is_constant())
                {
                  exprt pns=exprt(ID_next_symbol, bool_typet());
                  pns.copy_to_operands(exprt(ID_predicate_passive_symbol,
                        bool_typet()));
                  pns.op0().set(ID_identifier, v_it->first);
                  constraints_passive.push_back(pns);
                  if(value.is_false())
                    constraints_passive.back().make_not();
                }
                else if(value.id()==ID_predicate_passive_symbol ||
                    value.id()==ID_or || value.id()==ID_not ||
                    value.id()==ID_and)
                {
                  // !value | pns(v_it->first)
                  // & value | !pns(v_it->first)
                  exprt pns=exprt(ID_next_symbol, bool_typet());
                  pns.copy_to_operands(exprt(ID_predicate_passive_symbol,
                        bool_typet()));
                  pns.op0().set(ID_identifier, v_it->first);
                  constraints_passive.push_back(or_exprt(value, pns));
                  constraints_passive.back().op0().make_not();
                  constraints_passive.push_back(or_exprt(value, pns));
                  constraints_passive.back().op1().make_not();
                }
                else
                {
                  std::cerr << v_it->second.pretty() << std::endl;
                  assert(false); // not yet implemented
                }
              }
            }

            make_active_passive_assign(PC, assigned, constraints,
                true, assigned_passive, constraints_passive);
          }
        }
      }
      break;
    case SKIP:
    case LOCATION:
      make_skip(PC);
      break;
    case END_FUNCTION:
    case END_THREAD:
      // no transitions
      break;
    case DEAD:
    case FUNCTION_CALL:
    case RETURN:
    case CATCH:
    case THROW:
    case NO_INSTRUCTION_TYPE:
      assert(0); // not supported
      break;
  }
}

/*******************************************************************\

Function: tts_buildert::inc_state

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void tts_buildert::inc_state(std::vector<bool> &states)
{
  for(std::vector<bool>::iterator it=states.begin();
      it!=states.end();
      ++it)
  {
    *it=!*it;
    if(*it)
      return;
  }
}

/*******************************************************************\

Function: tts_buildert::inc_state_symmetric

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void tts_buildert::inc_state_symmetric(std::vector<bool> &states)
{
  assert(states.size()%2==1);
  const unsigned middle=states.size()/2;
  for(std::vector<bool>::iterator
      it=states.begin(), it2=states.begin()+middle;
      it2!=states.end();
      ++it, ++it2)
  {
    *it2=!*it2;
    *it=*it2;
    if(*it)
      return;
  }
}

/*******************************************************************\

Function: tts_buildert::get_shared_state_num

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void tts_buildert::get_shared_state_num(
    const bool m,
    const bool ts,
    const std::vector<bool> &state,
    const bool post_state,
    mp_integer &dest) const
{
  std::vector<bool>::const_iterator st_it=state.begin();
  if(post_state)
    st_it+=sdim.size()+ldim.size();

  dest=m?2:0;
  dest+=ts?1:0;
  for(std::vector<unsigned>::const_iterator s_it=sdim.begin();
      s_it!=sdim.end(); ++s_it, ++st_it)
  {
    dest*=2;
    if(*st_it) dest+=1;
  }
}

/*******************************************************************\

Function: tts_buildert::get_local_state_num

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void tts_buildert::get_local_state_num(
    const unsigned PC,
    const std::vector<bool> &state,
    const bool post_state,
    mp_integer &dest) const
{
  std::vector<bool>::const_iterator st_it=state.begin()+sdim.size();
  if(post_state)
    st_it+=sdim.size()+ldim.size();

  dest=0;
  for(std::vector<unsigned>::const_iterator s_it=ldim.begin();
      s_it!=ldim.end(); ++s_it, ++st_it)
  {
    dest*=2;
    if(*st_it) dest+=1;
  }
  assert(dest<pc_multiplier);
  dest+=pc_multiplier*PC;
}

/*******************************************************************\

Function: tts_buildert::print_shared_state

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void tts_buildert::print_shared_state(
    const bool m,
    const bool ts,
    const std::vector<bool> &state,
    const bool is_post)
{
  std::vector<bool>::const_iterator st_it=state.begin();
  if(is_post)
    st_it+=sdim.size()+ldim.size();

  out_tts << " m=" << (m?1:0) << " ts=" << (ts?1:0);
  for(std::vector<unsigned>::const_iterator s_it=sdim.begin();
      s_it!=sdim.end(); ++s_it, ++st_it)
    out_tts << " b"<< *s_it << "=" << *st_it;
}

/*******************************************************************\

Function: tts_buildert::local_state_string

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void tts_buildert::local_state_string(
    const unsigned PC,
    const std::vector<bool> &state,
    const bool is_post,
    std::ostream &os)
{
  std::vector<bool>::const_iterator st_it=state.begin()+sdim.size();
  if(is_post)
    st_it+=sdim.size()+ldim.size();

  os << " tts-pc=" << PC;
  for(std::vector<unsigned>::const_iterator s_it=ldim.begin();
      s_it!=ldim.end(); ++s_it, ++st_it)
    os << " b"<< *s_it << "=" << *st_it;
}

/*******************************************************************\

Function: tts_buildert::print_local_state

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void tts_buildert::print_local_state(
    const unsigned PC,
    const std::vector<bool> &state,
    const bool is_post)
{
  local_state_string(PC, state, is_post, out_tts);
}

/*******************************************************************\

Function: tts_buildert::print_tuples

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void tts_buildert::print_tuples(
    const std::vector<bool> &state,
    const bool m1,
    const bool ts1,
    const unsigned PC1,
    const bool m2,
    const bool ts2,
    const unsigned PC2)
{
  out_tts << "#";
  print_shared_state(m1, ts1, state, false);
  print_local_state(PC1, state, false);
  out_tts << " -->";
  print_shared_state(m2, ts2, state, true);
  print_local_state(PC2, state, true);
  out_tts << std::endl;
}

/*******************************************************************\

Function: tts_buildert::make_skip

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void tts_buildert::make_skip(
    const unsigned PC)
{
#ifdef DEBUG
  ::std::cerr << "make_skip" << std::endl;
#endif
  for(std::vector<bool> states((2*sdim.size())+(2*ldim.size())+1, false);
      !*states.rbegin();
      inc_state_symmetric(states))
  {
#ifdef COMMENTS
    print_tuples(states, in_atomic_sect, false,
        PC, in_atomic_sect, false, PC+1);
#endif
    mp_integer num_s, num_l1, num_l2;
    get_shared_state_num(in_atomic_sect, false, states, false, num_s);
    get_local_state_num(PC, states, false, num_l1);
    get_local_state_num(PC+1, states, true, num_l2);
    out_tts << num_s << " " << num_l1 << " -> "
      << num_s << " " << num_l2 << std::endl;
  }
#ifdef DEBUG
  ::std::cerr << "make_skip done" << std::endl;
#endif
}

/*******************************************************************\

Function: tts_buildert::make_atomic

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void tts_buildert::make_atomic(
    const unsigned PC,
    const bool is_end)
{
#ifdef DEBUG
  ::std::cerr << "make_atomic" << std::endl;
#endif
  assert(in_atomic_sect==is_end);
  in_atomic_sect=!is_end;

  for(std::vector<bool> states((2*sdim.size())+(2*ldim.size())+1, false);
      !*states.rbegin();
      inc_state_symmetric(states))
  {
#ifdef COMMENTS
    print_tuples(states, is_end, false,
        PC, !is_end, false, PC+1);
#endif
    mp_integer num_s1, num_s2, num_l1, num_l2;
    get_shared_state_num(is_end, false, states, false, num_s1);
    get_local_state_num(PC, states, false, num_l1);
    get_shared_state_num(!is_end, false, states, true, num_s2);
    get_local_state_num(PC+1, states, true, num_l2);
    out_tts << num_s1 << " " << num_l1 << " -> "
      << num_s2 << " " << num_l2 << std::endl;
  }
#ifdef DEBUG
  ::std::cerr << "make_atomic done" << std::endl;
#endif
}

/*******************************************************************\

Function: make_nnf

Inputs:

Outputs:

Purpose:

\*******************************************************************/

static void make_nnf(exprt &expr)
{
  bool mod=false;
  if(expr.id()==ID_not)
  {
    assert(expr.operands().size()==1);
    exprt &op=expr.op0();
    if(op.id()==ID_not)
    {
      mod=true;
      assert(op.operands().size()==1);
      exprt tmp;
      tmp.swap(op.op0());
      expr.swap(tmp);
    }
    else if(op.id()==ID_and)
    {
      mod=true;
      exprt tmp;
      tmp.swap(op);
      expr.swap(tmp);
      expr.id(ID_or);
      Forall_operands(it, expr)
        it->make_not();
    }
    else if(op.id()==ID_or)
    {
      mod=true;
      exprt tmp;
      tmp.swap(op);
      expr.swap(tmp);
      expr.id(ID_and);
      Forall_operands(it, expr)
        it->make_not();
    }
  }

  if(mod)
    make_nnf(expr);
  else
    Forall_operands(it, expr)
      make_nnf(*it);
}

/*******************************************************************\

Function: lift_and

Inputs:

Outputs:

Purpose:

\*******************************************************************/

static void lift_and(exprt &expr)
{
  Forall_operands(it, expr)
    lift_and(*it);

  exprt::operandst::iterator and_it=expr.operands().end();
  Forall_operands(it, expr)
    if(it->id()==ID_and)
    {
      and_it=it;
      break;
    }

  if(and_it!=expr.operands().end())
  {
    if(expr.id()==ID_and)
    {
      // flatten
      and_exprt a;
      Forall_operands(it, expr)
      {
        if(it->id()==ID_and)
        {
          Forall_operands(it2, *it)
            a.move_to_operands(*it2);
        }
        else
          a.move_to_operands(*it);
      }
      expr.swap(a);
    }
    else if(expr.id()==ID_or)
    {
      unsigned offset=and_it-expr.operands().begin();
      // lift 1 ID_and and re-run
      exprt tmp;
      tmp.swap(*and_it);
      and_exprt a;
      Forall_operands(it, tmp)
      {
        (expr.operands().begin()+offset)->swap(*it);
        a.copy_to_operands(expr);
      }
      expr.swap(a);

      lift_and(expr);
    }
  }
}

/*******************************************************************\

Function: tts_buildert::to_cnf

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void tts_buildert::to_cnf(
    const std::list<exprt> &constraints,
    std::list<bvt> &cnf)
{
  std::list<exprt> c(constraints);

  for(std::list<exprt>::iterator
      it=c.begin();
      it!=c.end();
      ++it)
  {
    if(it->id()=="bp_schoose")
    {
      // schoose[a,b] is like (* and !b) | a
      // we do *|a and !b|a
      c.push_back(or_exprt(
            exprt(ID_nondet_symbol, bool_typet()),
            it->op0()));
      c.push_back(or_exprt(
            it->op1(),
            it->op0()));
      c.back().op0().make_not();

      it->make_true();
      continue;
    }
    else if(it->id()==ID_equal)
    {
      c.push_back(or_exprt(
            it->op0(),
            it->op1()));
      c.back().op0().make_not();
      c.push_back(or_exprt(
            it->op0(),
            it->op1()));
      c.back().op1().make_not();

      it->make_true();
      continue;
    }

    make_nnf(*it);
    if(it->id()==ID_and)
    {
      Forall_operands(it2, *it)
      {
        c.push_back(exprt());
        c.back().swap(*it2);
      }

      it->make_true();
      continue;
    }

    lift_and(*it);
    if(it->id()==ID_and)
    {
      Forall_operands(it2, *it)
      {
        c.push_front(exprt());
        c.front().swap(*it2);
      }

      it->make_true();
    }
  }

  for(std::list<exprt>::const_iterator
      it=c.begin();
      it!=c.end();
      ++it)
  {
    if(!it->is_true()) // skip "true"
    {
      cnf.push_back(bvt());
#ifdef DEBUG
      // std::cerr << "TO CNF: " << std::endl << it->pretty() << std::endl;
#endif
      to_cnf(*it, cnf.back(), false);
    }
  }
}

/*******************************************************************\

Function: tts_buildert::to_cnf

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void tts_buildert::to_cnf(
    const exprt &guard,
    bvt &clause,
    const bool negate)
{
  if(guard.id()==ID_not)
  {
    forall_operands(it, guard)
      to_cnf(*it, clause, !negate);
  }
  else if(guard.is_constant())
  {
    if(guard.is_false()==negate)
      clause.push_back(const_literal(true));
  }
  else if(guard.id()==ID_nondet_symbol ||
      guard.id()==ID_nondet_bool)
  {
    clause.push_back(literalt()); // intentional use of unused_var_no
  }
  else if(guard.id()==ID_or)
  {
    forall_operands(it, guard)
      to_cnf(*it, clause, negate);
  }
  else if(guard.id()==ID_predicate_symbol ||
      guard.id()==ID_predicate_next_symbol ||
      guard.id()==ID_predicate_passive_symbol ||
      (guard.id()==ID_next_symbol &&
       guard.op0().id()==ID_predicate_passive_symbol))
  {
    unsigned p=safe_str2unsigned((guard.id()==ID_next_symbol?
          guard.op0():guard).get(ID_identifier).c_str());
    const bool is_post=guard.id()==ID_predicate_next_symbol ||
      guard.id()==ID_next_symbol;
    const bool sym_passive=
      guard.id()==ID_predicate_passive_symbol ||
      (guard.id()==ID_next_symbol &&
       guard.op0().id()==ID_predicate_passive_symbol);
    assert(!sym_passive || state_offset[p]>=sdim.size());
    if(sym_passive)
      p+=2*state_offset.size();
    if(is_post)
      p+=state_offset.size();
    clause.push_back(literalt(p, !negate));
  }
  else
  {
    std::cerr << guard.pretty() << std::endl;
    assert(false); // not yet implemented
  }
}

/*******************************************************************\

Function: tts_buildert::cnf_sat

Inputs:

Outputs:

Purpose:

\*******************************************************************/

bool tts_buildert::cnf_sat(
    const std::vector<bool> &act_state,
    const std::list<bvt> &cnf,
    bool &is_nondet) const
{
  return cnf_sat(act_state, std::vector<bool>(), cnf, is_nondet);
}

/*******************************************************************\

Function: tts_buildert::cnf_sat

Inputs:

Outputs:

Purpose:

\*******************************************************************/

bool tts_buildert::cnf_sat(
    const std::vector<bool> &act_state,
    const std::vector<bool> &psv_state,
    const std::list<bvt> &cnf,
    bool &is_nondet) const
{
  is_nondet=false;
  bool sat=true;

  for(std::list<bvt>::const_iterator
      it=cnf.begin();
      sat && it!=cnf.end();
      ++it)
    sat=clause_sat(act_state, psv_state, *it, is_nondet);

  if(!sat)
    is_nondet=false;
  return sat;
}

/*******************************************************************\

Function: tts_buildert::clause_sat

Inputs:

Outputs:

Purpose:

\*******************************************************************/

bool tts_buildert::clause_sat(
    const std::vector<bool> &act_state,
    const std::vector<bool> &psv_state,
    const bvt &clause,
    bool &is_nondet) const
{
  bool sat=false;
  bool has_nondet=false;

  for(bvt::const_iterator
      it=clause.begin();
      !sat && it!=clause.end();
      ++it)
  {
    if(it->is_true())
      return true;

    if(it->is_false())
      continue;

    unsigned var_no=it->var_no();
    const bool is_psv=var_no>=2*state_offset.size();
    if(var_no==literalt::unused_var_no() ||
        (is_psv && psv_state.empty()))
    {
      has_nondet=true;
      continue;
    }

    const std::vector<bool> &state=is_psv ? psv_state : act_state;
    if(is_psv)
      var_no-=2*state_offset.size();

    unsigned post_offset=0;
    if(var_no>=state_offset.size())
    {
      var_no-=state_offset.size();
      post_offset=sdim.size()+ldim.size();
    }
    assert(state_offset[var_no]<state.size());
    assert(state_offset[var_no]+post_offset<state.size());
    sat=(state[state_offset[var_no]+post_offset]==it->sign());
  }

  if(!sat && has_nondet)
  {
    is_nondet=true;
    return true;
  }

  return sat;
}

/*******************************************************************\

Function: tts_buildert::make_assert

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void tts_buildert::make_assert(
    const unsigned PC,
    const std::list<exprt> &constraints)
{
#ifdef DEBUG
  ::std::cerr << "make_assert" << std::endl;
#endif
  std::list<bvt> cnf;
  to_cnf(constraints, cnf);

  for(std::vector<bool> states((2*sdim.size())+(2*ldim.size())+1, false);
      !*states.rbegin();
      inc_state_symmetric(states))
  {
    bool nondet;
    const bool sat=cnf_sat(states, cnf, nondet);

#ifdef COMMENTS
    if(!sat)
    {
      out_tts << "#";
      print_shared_state(in_atomic_sect, false, states, false);
      print_local_state(PC, states, false);
      out_tts << " --> error error";
      out_tts << std::endl;
    }
    else
      print_tuples(states, in_atomic_sect, false,
          PC, in_atomic_sect, false, PC+1);
#endif
    mp_integer num_s, num_l;
    get_shared_state_num(in_atomic_sect, false, states, false, num_s);
    get_local_state_num(PC, states, false, num_l);
    out_tts << num_s << " " << num_l << " -> ";
    if(!sat)
    {
      out_tts << "$#E" << " ";
      out_tts << local_error_num << std::endl;
    }
    else
    {
      mp_integer num_l2;
      get_local_state_num(PC+1, states, true, num_l2);
      out_tts << num_s << " " << num_l2 << std::endl;
    }

    if(nondet)
    {
#ifdef COMMENTS
      {
        out_tts << "#";
        print_shared_state(in_atomic_sect, false, states, false);
        print_local_state(PC, states, false);
        out_tts << " --> error error";
        out_tts << std::endl;
      }
#endif
      out_tts << num_s << " " << num_l << " -> ";
      out_tts << "$#E" << " ";
      out_tts << local_error_num << std::endl;
    }
  }
#ifdef DEBUG
  ::std::cerr << "make_assert done" << std::endl;
#endif
}

/*******************************************************************\

Function: tts_buildert::make_assume

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void tts_buildert::make_assume(
    const unsigned PC,
    const std::list<exprt> &constraints)
{
#ifdef DEBUG
  ::std::cerr << "make_assume" << std::endl;
#endif
  std::list<bvt> cnf;
  to_cnf(constraints, cnf);

  for(std::vector<bool> states((2*sdim.size())+(2*ldim.size())+1, false);
      !*states.rbegin();
      inc_state_symmetric(states))
  {
    // skip if conjunction not satisfied
    bool nondet;
    if(!cnf_sat(states, cnf, nondet))
      continue;

#ifdef COMMENTS
    print_tuples(states, in_atomic_sect, false,
        PC, in_atomic_sect, false, PC+1);
#endif
    mp_integer num_s, num_l1, num_l2;
    get_shared_state_num(in_atomic_sect, false, states, false, num_s);
    get_local_state_num(PC, states, false, num_l1);
    get_local_state_num(PC+1, states, true, num_l2);
    out_tts << num_s << " " << num_l1 << " -> "
      << num_s << " " << num_l2 << std::endl;

    if(nondet)
    {
      // stay in this state
#ifdef COMMENTS
      print_tuples(states, in_atomic_sect, false,
          PC, in_atomic_sect, false, PC);
#endif
      out_tts << num_s << " " << num_l1 << " -> "
        << num_s << " " << num_l1 << std::endl;
    }
  }
#ifdef DEBUG
  ::std::cerr << "make_assume done" << std::endl;
#endif
}

/*******************************************************************\

Function: tts_buildert::make_goto

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void tts_buildert::make_goto(
    const unsigned PC,
    const std::list<exprt> &constraints,
    const unsigned target)
{
#ifdef DEBUG
  ::std::cerr << "make_goto" << std::endl;
#endif
  std::list<bvt> cnf;
  to_cnf(constraints, cnf);

  for(std::vector<bool> states((2*sdim.size())+(2*ldim.size())+1, false);
      !*states.rbegin();
      inc_state_symmetric(states))
  {
    bool nondet;
    const bool sat=cnf_sat(states, cnf, nondet);

#ifdef COMMENTS
    if(sat)
      print_tuples(states, in_atomic_sect, false,
          PC, in_atomic_sect, false, target);
    else
      print_tuples(states, in_atomic_sect, false,
          PC, in_atomic_sect, false, PC+1);
#endif
    mp_integer num_s, num_l1, num_l2;
    get_shared_state_num(in_atomic_sect, false, states, false, num_s);
    get_local_state_num(PC, states, false, num_l1);
    get_local_state_num(PC+1, states, true, num_l2);
    out_tts << num_s << " " << num_l1 << " -> "
      << num_s << " ";
    if(sat)
      get_local_state_num(target, states, true, num_l2);
    else
      get_local_state_num(PC+1, states, true, num_l2);
    out_tts << num_l2 << std::endl;

    if(nondet)
    {
#ifdef COMMENTS
      print_tuples(states, in_atomic_sect, false,
          PC, in_atomic_sect, false, PC+1);
#endif
      get_local_state_num(PC+1, states, true, num_l2);
      out_tts << num_s << " " << num_l1 << " -> "
        << num_s << " " << num_l2 << std::endl;
    }
  }
#ifdef DEBUG
  ::std::cerr << "make_goto done" << std::endl;
#endif
}

/*******************************************************************\

Function: tts_buildert::make_start_thread

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void tts_buildert::make_start_thread(
    const unsigned PC,
    const unsigned target)
{
#ifdef DEBUG
  ::std::cerr << "make_start_thread" << std::endl;
#endif
  for(std::vector<bool> states((2*sdim.size())+(2*ldim.size())+1, false);
      !*states.rbegin();
      inc_state_symmetric(states))
  {
#ifdef COMMENTS
    print_tuples(states, in_atomic_sect, false,
        PC, in_atomic_sect, true, PC+1);
#endif
    mp_integer num_s1, num_s2, num_l1, num_l2;
    get_shared_state_num(in_atomic_sect, false, states, false, num_s1);
    get_local_state_num(PC, states, false, num_l1);
    get_shared_state_num(in_atomic_sect, true, states, true, num_s2);
    get_local_state_num(PC+1, states, true, num_l2);
    out_tts << num_s1 << " " << num_l1 << " +> "
      << num_s2 << " " << num_l2 << std::endl;

#ifdef COMMENTS
    print_tuples(states, in_atomic_sect, true,
        PC, in_atomic_sect, false, target);
#endif
    get_local_state_num(target, states, true, num_l2);
    out_tts << num_s2 << " " << num_l1 << " -> "
      << num_s1 << " " << num_l2 << std::endl;
  }
#ifdef DEBUG
  ::std::cerr << "make_start_thread done" << std::endl;
#endif
}

/*******************************************************************\

Function: tts_buildert::skip_make_assign

Inputs:

Outputs:

Purpose:

\*******************************************************************/

bool tts_buildert::skip_make_assign(
    const std::vector<bool> &state,
    const std::vector<bool> &assigned) const
{
  // skip all changes to state unless assigned
  bool same=true;
  for(unsigned i=0; same && i<state.size()/2; ++i)
    if((i<sdim.size() && !assigned[sdim[i]]) ||
        (i>=sdim.size() && !assigned[ldim[i-sdim.size()]]))
      same=(state[i]==state[(state.size()/2)+i]);

  return !same;
}

/*******************************************************************\

Function: tts_buildert::make_assign

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void tts_buildert::make_assign(
    const unsigned PC,
    const std::vector<bool> &assigned,
    const std::list<exprt> &constraints)
{
  make_active_passive_assign(PC, assigned, constraints,
      false, std::vector<bool>(), std::list<exprt>());
}

/*******************************************************************\

Function: tts_buildert::make_active_passive_assign

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void tts_buildert::make_active_passive_assign(
    const unsigned PC,
    const std::vector<bool> &assigned,
    const std::list<exprt> &constraints,
    const bool with_passive,
    const std::vector<bool> &assigned_passive,
    const std::list<exprt> &constraints_passive)
{
#ifdef DEBUG
  ::std::cerr << "make_assign" << std::endl;
#endif
  std::list<bvt> cnf;
  to_cnf(constraints, cnf);

  for(std::vector<bool> states((2*sdim.size())+(2*ldim.size())+1, false);
      !*states.rbegin();
      inc_state(states))
  {
    if(skip_make_assign(states, assigned))
      continue;

    // skip if conjunction not satisfied
    bool nondet;
    if(!cnf_sat(states, cnf, nondet) && !nondet)
      continue;

    mp_integer num_s1, num_s2, num_l1, num_l2;
    get_shared_state_num(in_atomic_sect, false, states, false, num_s1);
    get_local_state_num(PC, states, false, num_l1);
    get_shared_state_num(in_atomic_sect, false, states, true, num_s2);
    get_local_state_num(PC+1, states, true, num_l2);
#ifdef COMMENTS
    print_tuples(states, in_atomic_sect, false,
        PC, in_atomic_sect, false, PC+1);
#endif

    std::ostringstream passive_trans_string;
    if(with_passive)
      make_passive_assign(PC, states,
          assigned_passive, constraints_passive,
          passive_trans_string);

    out_tts << num_s1 << " " << num_l1 << " -> "
      << num_s2 << " " << num_l2 << passive_trans_string.str() << std::endl;
  }
#ifdef DEBUG
  ::std::cerr << "make_assign done" << std::endl;
#endif
}

/*******************************************************************\

Function: tts_buildert::skip_make_passive_assign

Inputs:

Outputs:

Purpose:

\*******************************************************************/

bool tts_buildert::skip_make_passive_assign(
    const std::vector<bool> &state,
    const std::vector<bool> &assigned) const
{
  if(skip_make_assign(state, assigned))
    return true;

  bool shared_false=true;
  for(unsigned i=0; shared_false && i<sdim.size(); ++i)
    shared_false=!state[i] && !state[(state.size()/2)+i];

  return !shared_false;
}

/*******************************************************************\

Function: tts_buildert::make_passive_assign

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void tts_buildert::make_passive_assign(
    const unsigned PC,
    const std::vector<bool> &act_states,
    const std::vector<bool> &assigned_passive,
    const std::list<exprt> &constraints_passive,
    std::ostringstream &trans_os)
{
#ifdef DEBUG
  ::std::cerr << "make_passive_assign" << std::endl;
#endif
  std::list<bvt> cnf;
  to_cnf(constraints_passive, cnf);

  std::map<mp_integer, std::set<mp_integer> > p_P;
#ifdef COMMENTS
  std::map<mp_integer, std::string> state_text;
#endif

  for(std::vector<bool> states((2*sdim.size())+(2*ldim.size())+1, false);
      !*states.rbegin();
      inc_state(states))
  {
    if(skip_make_passive_assign(states, assigned_passive))
      continue;

    // skip if conjunction not satisfied
    bool nondet;
    if(!cnf_sat(act_states, states, cnf, nondet) && !nondet)
      continue;

    for(unsigned PC=PC_min; PC<=PC_max; ++PC)
    {
      mp_integer num_l1, num_l2;
      get_local_state_num(PC, states, false, num_l1);
      get_local_state_num(PC, states, true, num_l2);
#ifdef COMMENTS
      std::pair<std::map<mp_integer, std::string>::iterator, bool> entry=
        state_text.insert(std::make_pair(num_l1, ""));
      if(entry.second)
      {
        std::ostringstream oss;
        local_state_string(PC, states, false, oss);
        entry.first->second=oss.str();
      }
      entry=state_text.insert(std::make_pair(num_l2, ""));
      if(entry.second)
      {
        std::ostringstream oss;
        local_state_string(PC, states, true, oss);
        entry.first->second=oss.str();
      }
#endif

      p_P[num_l1].insert(num_l2);
    }
  }

  for(std::map<mp_integer, std::set<mp_integer> >::const_iterator iter=p_P.begin();
      iter!=p_P.end();
      ++iter)
  {
    const mp_integer &p=iter->first;
    assert(!iter->second.empty());
    // skip no-op only
    if(iter->second.size()==1 && p==*(iter->second.begin()))
      continue;

    for(std::set<mp_integer>::const_iterator pp=iter->second.begin();
        pp!=iter->second.end();
        ++pp)
    {
#ifdef COMMENTS
      out_tts << "#";
      out_tts << " *";
      out_tts << " " << state_text[p];
      out_tts << " ~>";
      out_tts << " *";
      out_tts << " " << state_text[*pp];
      out_tts << std::endl;
#endif
      trans_os << " " << p << " ~> " << *pp;
    }
  }

#ifdef DEBUG
  ::std::cerr << "make_passive_assign done" << std::endl;
#endif
}

