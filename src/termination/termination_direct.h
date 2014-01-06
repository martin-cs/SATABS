/*******************************************************************\

Module: Direct termination engine (Biere et al.)

Author: CM Wintersteiger

\*******************************************************************/

#ifndef _CPROVER_TERMINATION_DIRECT_H_
#define _CPROVER_TERMINATION_DIRECT_H_

#include "termination_base.h"

class termination_directt : public termination_baset
{
public:
  termination_directt(const cmdlinet &_cmd,
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
                        slicing_time(0){}
  
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
};

#endif
