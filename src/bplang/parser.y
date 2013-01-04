%{
#include <i2string.h>

#include "bp_parser.h"
#include "bp_typecheck.h"

#define YYSTYPE unsigned
#define PARSER bp_parser

#include "y.tab.h"

#define YYMAXDEPTH 200000
#define YYSTYPE_IS_TRIVIAL 1

/*------------------------------------------------------------------------*/

#define yylineno yybplineno
#define yytext yybptext

#define yyerror yybperror
int yybperror(const std::string &error);
int yylex();
extern char *yytext;

/*------------------------------------------------------------------------*/

#define mto(x, y) stack(x).move_to_operands(stack(y))
#define binary(x, y, id, z) { init(x, id); \
  stack(x).reserve_operands(2); mto(x, y); mto(x, z); }

/*******************************************************************\

Function: init

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void init(exprt &expr)
{
  expr.clear();

  locationt &location=expr.location();
  location.set_line(PARSER.line_no);

  if(PARSER.filename!=irep_idt())
    location.set_file(PARSER.filename);

  if(PARSER.function!=irep_idt())
    location.set_function(PARSER.function);
}

/*******************************************************************\

Function: init

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void init(YYSTYPE &expr)
{
  newstack(expr);
  init(stack(expr));
}

/*******************************************************************\

Function: init

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void init(YYSTYPE &expr, const irep_idt &id)
{
  init(expr);
  stack(expr).id(id);
}

/*******************************************************************\

Function: j_binary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void j_binary(YYSTYPE &dest, YYSTYPE &op1,
                     const irep_idt &id, YYSTYPE &op2)
{
  if(stack(op1).id()==id)
  {
    dest=op1;
    mto(dest, op2);
  }
  else if(stack(op2).id()==id)
  {
    dest=op2;
    mto(dest, op1);
  }
  else
    binary(dest, op1, id, op2);
}

/*******************************************************************\

Function: statement

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void statement(YYSTYPE &dest, const irep_idt &statement)
{
  init(dest, ID_code);
  stack(dest).set(ID_statement, statement);
}

/*******************************************************************\

Function: new_declaration

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void new_declaration(YYSTYPE &decl)
{
  PARSER.parse_tree.declarations.push_back(exprt());
  PARSER.parse_tree.declarations.back().swap(stack(decl));
}

/*------------------------------------------------------------------------*/

%}

%token BEGIN_Token        "begin"
%token END_Token          "end"
%token DECL_Token         "decl"
%token VOID_Token         "void"
%token BOOL_Token         "bool"
%token GOTO_Token         "goto"
%token ENFORCE_Token      "enforce"
%token IF_Token           "if"
%token THEN_Token         "then"
%token ELSE_Token         "else"
%token ELSIF_Token        "elsif"
%token FI_Token           "fi"
%token SKIP_Token         "skip"
%token WHILE_Token        "while"
%token DO_Token           "do"
%token OD_Token           "od"
%token ABORTIF_Token      "abortif"
%token START_THREAD_Token "start_thread"
%token END_THREAD_Token   "end_thread"
%token THREAD_LOCAL_Token "thread_local"
%token SYNC_Token         "sync"
%token ATOMIC_BEGIN_Token "atomic_begin"
%token ATOMIC_END_Token   "atomic_end"
%token DEAD_Token         "dead"
%token RETURN_Token       "return"
%token SCHOOSE_Token      "schoose"
%token IDENTIFIER_Token
%token NUMBER_Token
%token DFS_Token          "dfs"

%token ASSIGN_Token       ":="
%token CONSTRAIN_Token    "constrain"

%token NEQ_Token          "!="
%token EQ_Token           "="

/* Precedences */

%right IMPLIES_Token EQ_Token NEQ_Token
%left  EQUIV_Token
%left  XOR_Token
%left  OR_Token
%left  AND_Token
%left  TICK_Token

%%

start      : declarations
           ;

declarations: declaration { new_declaration($1); }
           | declarations declaration { new_declaration($2); }
           ;

declaration: variable_declaration ';'
           | function_definition
           ;

variable_declaration: DECL_Token variable_list
             { init($$, "variable");
               stack($$).operands().swap(stack($2).operands());
             }
           ;

variable_list: variable_name 
              { init($$); mto($$, $1); }
           | variable_list ',' variable_name 
              { $$=$1; mto($$, $3); }
           ;

expression_list: expression
              { init($$); mto($$, $1); }
           | expression_list ',' expression
              { $$=$1; mto($$, $3); }
           ;

variable_list_opt: { init($$); }
	   | variable_list
	   ;

expression_list_opt: { init($$); }
	   | expression_list
	   ;

argument_list: '(' variable_list_opt ')' { $$=$2; }
           ;           

type       : VOID_Token { init($$, ID_empty); }
           | BOOL_Token { init($$, ID_bool); }
           | BOOL_Token '<' NUMBER_Token '>'
             {
               init($$, "bool-vector");
               stack($$).set(ID_width, stack($3).id());
             }
           ;
           
function_definition: dfs_opt type function_name
                     { PARSER.function=stack($3).get(ID_identifier); }
                     argument_list function_body
                     { PARSER.function=irep_idt(); }
             { init($$, ID_function);
               stack($$).add(ID_return_type).swap(stack($2));
               stack($$).set(ID_identifier, stack($3).get(ID_identifier));
               stack($$).add(ID_arguments).get_sub().swap(
                 stack($5).add(ID_operands).get_sub());
               stack($$).add(ID_body).swap(stack($6));
             }
           ;

dfs_opt    : /* empty */
           | DFS_Token
           ;

function_body: block_statement
	   ;

block_statement: BEGIN_Token statement_list END_Token { $$=$2; }
           ;
           
statement_list: /* nothing */ { statement($$, ID_block); }
           | statement_list_rec ';' { $$=$1; }
           | statement_list_rec { $$=$1; }
           ;           

statement_list_rec:
             statement_list_rec ';' statement { $$=$1; mto($$, $3); }
           | statement { statement($$, ID_block); mto($$, $1); }
           ;           

if_statement: IF_Token expression THEN_Token statement_list FI_Token
             { statement($$, ID_ifthenelse);
               stack($$).move_to_operands(stack($2), stack($4)); }
           | IF_Token expression THEN_Token statement_list elsif_list FI_Token
             { statement($$, ID_ifthenelse);
               stack($$).move_to_operands(stack($2), stack($4), stack($5));
             }
           ;

elsif_list:  ELSE_Token statement_list
             { $$=$2; }
           | ELSIF_Token expression THEN_Token statement_list elsif_list
             { statement($$, ID_ifthenelse);
               stack($$).move_to_operands(stack($2), stack($4), stack($5));
             }
           | ELSIF_Token expression THEN_Token statement_list
             { statement($$, ID_ifthenelse);
               stack($$).move_to_operands(stack($2), stack($4));
             }
           ;
           
while_statement: WHILE_Token expression DO_Token statement_list OD_Token
             { statement($$, ID_while);
               stack($$).move_to_operands(stack($2), stack($4)); }
           ;           
           
goto_statement: GOTO_Token label_list
             { 
               if(stack($2).operands().size()==1)
               {
                 statement($$, ID_goto);
                 stack($$).set(ID_destination, stack($2).op0().id());
               }
               else
               {
                 statement($$, "non-deterministic-goto");
                 stack($$).add("destinations").get_sub().swap(stack($2).add(ID_operands).get_sub());
               }
             }
	   ;
	   
label_list : label
             {
               init($$); mto($$, $1);
             }
           | label_list ',' label
             {
               $$=$1; mto($$, $3);
             }
           ;	  
           
function_call: function_name '(' expression_list_opt ')'
             { statement($$, ID_function_call);
               stack($$).operands().resize(3);
               stack($$).op0().make_nil();
               stack($$).op1().swap(stack($1));
               stack($$).op2().id(ID_arguments);
               stack($$).op2().operands().swap(stack($3).operands());
             }
	   ;

function_call_statement: function_call
	   ;

return_statement: RETURN_Token expression_list
             { statement($$, ID_return);
               stack($$).operands().swap(stack($2).operands());
             }
           | RETURN_Token { statement($$, ID_return); }
	   ;

enforce_statement: ENFORCE_Token expression
             { statement($$, ID_bp_enforce);
               stack($$).reserve_operands(2); // for code
               mto($$, $2);
               stack($$).operands().resize(2);
             }
	   ;

skip_statement: SKIP_Token
             { statement($$, ID_skip);
               stack($$).set("explicit", true);
             }
	   ;

abortif_statement: ABORTIF_Token expression
             { statement($$, ID_bp_abortif);
               mto($$, $2);
             }
	   ;

start_thread_statement: START_THREAD_Token statement
             { statement($$, ID_start_thread);
               mto($$, $2);
             }
	   ;

end_thread_statement: END_THREAD_Token
             { statement($$, ID_end_thread);
             }
	   ;

sync_statement: SYNC_Token IDENTIFIER_Token
             { statement($$, ID_sync);
               stack($$).set(ID_event, stack($2).id());
             }
	   ;

atomic_begin_statement: ATOMIC_BEGIN_Token
             { statement($$, ID_atomic_begin);
             }
	   ;

atomic_end_statement: ATOMIC_END_Token
             { statement($$, ID_atomic_end);
             }
	   ;

dead_statement: DEAD_Token expression_list
             { statement($$, ID_bp_dead);
               stack($$).operands().swap(stack($2).operands());
             }
	   ;
	   
statement:   enforce_statement
           | abortif_statement
           | skip_statement
           | dead_statement
	   | goto_statement
	   | function_call_statement
	   | return_statement
	   | while_statement
	   | if_statement
	   | labeled_statement
	   | assignment_statement
	   | decl_statement
	   | start_thread_statement
	   | end_thread_statement
	   | sync_statement
	   | atomic_begin_statement
	   | atomic_end_statement
	   ;

decl_statement: variable_declaration
             { statement($$, ID_decl);
               stack($$).operands().swap(stack($1).operands());
             }
           ;

constrain_opt: /* Nothing */
             {
               init($$);
               stack($$).make_nil();
             }
	   | constrain
	   ;
	   
constrain: CONSTRAIN_Token expression
             {
               $$=$2;
             }
	   ;	   

assignment_statement: expression_list ASSIGN_Token expression_list constrain_opt
             {
               statement($$, ID_assign);
               stack($$).reserve_operands(2);
               mto($$, $1);
               mto($$, $3);

               if(stack($4).is_not_nil())
               {
                 exprt tmp;
                 tmp.swap(stack($$));
                 
                 init(stack($$));
                 stack($$).id(ID_code);
                 stack($$).set(ID_statement, ID_bp_constrain);
                 stack($$).move_to_operands(tmp, stack($4));
               }
             }
           | expression_list ASSIGN_Token function_call
             {
               $$=$3;
               stack($$).op0().swap(stack($1));
             }
           ;

labeled_statement: label ':' statement
             {
               statement($$, ID_label);
               stack($$).set(ID_label, stack($1).id());
               mto($$, $3);
             }
	   ;
	   
label: IDENTIFIER_Token
           ;

function_name: IDENTIFIER_Token
             { init($$, ID_symbol);
               stack($$).set(ID_identifier, stack($1).id());
             }
           ;

variable_name: IDENTIFIER_Token
             { init($$, ID_symbol);
               stack($$).set(ID_identifier, stack($1).id());
             }
           ;

expression:
             unary_expression
           | expression IMPLIES_Token expression { binary($$, $1, ID_implies, $3); }
           | expression AND_Token     expression { j_binary($$, $1, ID_and, $3); }
           | expression OR_Token      expression { j_binary($$, $1, ID_or, $3); }
           | expression XOR_Token     expression { binary($$, $1, ID_xor, $3); }
           | expression EQ_Token      expression { binary($$, $1, ID_equal, $3); }
           | expression NEQ_Token     expression { binary($$, $1, ID_notequal, $3); }
           ;
           
primary_expression: '(' expression ')' { $$=$2; }
           | '*' { init($$, ID_nondet_bool); }
           | variable_name
           | SCHOOSE_Token '[' expression_list ']'
             {
               init($$, ID_bp_schoose);
               stack($$).operands().swap(stack($3).operands());
             }
           | NUMBER_Token
             {
               init($$, ID_constant);
               stack($$).set(ID_value, stack($1).id());
             }
	   ;
	   
unary_expression:
             primary_expression
           | '!' unary_expression { init($$, ID_not); mto($$, $2); }
           | '~' unary_expression { init($$, ID_not); mto($$, $2); }
           | TICK_Token unary_expression { init($$, ID_next_symbol); mto($$, $2); }
           ;
	   
%%

int yybperror(const std::string &error)
{
  PARSER.parse_error(error, yytext);
  return 0;
}

#undef yyerror

