/*******************************************************************\

Module: Binary Reachability Engine

Author: CM Wintersteiger

\*******************************************************************/

#ifndef _CPROVER_TERMINATION_BRE_H_
#define _CPROVER_TERMINATION_BRE_H_

#include "termination_base.h"

class termination_bret: public termination_baset
{
public:
  termination_bret(const cmdlinet &_cmd,
                   const goto_functionst &_gf,
                   const symbol_tablet &_ctxt,
                   class symbol_tablet &_sctxt,
                   class value_set_analysist &_vsa,
                   class invariant_propagationt &_ip,
                   message_handlert &_mh,
                   ui_message_handlert::uit _ui) :
                     termination_baset(_cmd, _gf, _ctxt, _sctxt, 
                                       _vsa, _ip, _mh, _ui),
                     pointer_analysis_time(0),
                     slicing_time(0) {}
  
  virtual termination_resultt operator()();
  
  time_periodt pointer_analysis_time;
  time_periodt slicing_time;
  
  virtual void show_stats(void);
  
protected:
  termination_resultt
      terminates(
        const irep_idt &main,
        const goto_functionst &goto_functions,
        goto_programt::const_targett assertion);
    
  termination_resultt
    terminates(const goto_functionst &goto_functions);
    
  bool process_counterexample(goto_tracet &trace);      
  bodyt get_body(goto_tracet &trace);
    
  bool path_revisited(
    const goto_tracet &goto_trace,
    goto_tracet::stepst::const_iterator &loop_begin);
    
  termination_resultt bre_loop(
    const goto_functionst &goto_functions);
};

#endif
