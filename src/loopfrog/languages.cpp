/*******************************************************************\

Module: Language Registration

Author: CM Wintersteiger

\*******************************************************************/

#include <langapi/mode.h>

#include <ansi-c/ansi_c_language.h>

#ifdef HAVE_CPP
#include <cpp/cpp_language.h>
#endif

#ifdef HAVE_SPECC
#include <specc/specc_language.h>
#endif

/*******************************************************************\

Function: cmdline_optionst::register_languages

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void register_languages()
{
  register_language(new_ansi_c_language);

  #ifdef HAVE_CPP
  register_language(new_cpp_language);
  #endif

  #ifdef HAVE_SPECC
  register_language(new_specc_language);
  #endif
}
