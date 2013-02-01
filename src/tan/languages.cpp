/*******************************************************************\

Module: Language Registration

Author: CM Wintersteiger

\*******************************************************************/

#include <langapi/mode.h>

#include <ansi-c/ansi_c_language.h>

#ifdef HAVE_CPP
#include <cpp/cpp_language.h>
#endif

/*******************************************************************\

Function: register_languages

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
}
