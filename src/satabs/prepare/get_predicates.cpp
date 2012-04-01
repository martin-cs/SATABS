/*******************************************************************\

Module: Get user-provided predicates

Author: Daniel Kroening

Date: March 2011

Purpose: 

\*******************************************************************/

#include <fstream>
#include <memory>

#include <ansi-c/ansi_c_language.h>

/*******************************************************************\

Function: get_predicates

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void get_predicates(
    const std::string &file,
    message_handlert &message_handler,
    const namespacet &ns,
    std::vector<exprt> &predicates)
{
  std::ifstream infile(file.c_str());

  if(!infile)
    throw std::string("failed to open ")+file;

  // we only do C expressions right now

  languaget *l=new ansi_c_languaget;

  // use auto_ptr because of the exceptions
  std::auto_ptr<languaget> language(l);

  std::string line;

  while(infile)
  {
    std::getline(infile, line);

    if(line!="" && line[0]!='#' &&
        std::string(line, 0, 2)!="//")
    {
      exprt expr;

      if(language->to_expr(line, "", expr, message_handler, ns))
        throw "failed to parse `"+line+"'";

      if(expr.type().id()!=ID_bool)
      {
        std::string type_string;
        language->from_type(expr.type(), type_string, ns);
        throw "expected boolean expression as predicate, but got `"+type_string+"'";
      }

      predicates.push_back(expr);
    }
  }
}

