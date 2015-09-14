%{
open AST

let mk_exp (e:exp') = Exp (e, None)
%}

%token <int> NUM
%token TRUE FALSE UNIT

%token <string> VAR

%token LPAREN RPAREN

%token LET EQUAL IN FUN DOT FIX APPLY FFI LBRACKET SEMICOLON RBRACKET
%token MATCH WITH BAR RARROW END

%token ASPAR ASSEC UNBOX MKWIRE PROJWIRE CONCATWIRE

%token EOF

%start exp

%type <AST.const> const
%type <AST.exp> exp
%type <AST.pat> pat
%%

const:
| NUM        { C_nat $1     }
| UNIT       { C_unit       }
| TRUE       { C_bool true  }
| FALSE      { C_bool false }
;

pat:
| const        { P_const $1 }

patandexp:
| BAR pat RARROW exp        { ($2, $4) }

patandexplist:
| patandexp                                { [ $1 ]   }
| patandexp patandexplist                  { ($1::$2) }        

exp:
| const                                           { (mk_exp (E_const $1))             }
| VAR                                             { (mk_exp (E_var $1))               }
| LET VAR EQUAL exp IN exp                        { (mk_exp (E_let ($2, $4, $6)))     }
| FUN VAR DOT exp                                 { (mk_exp (E_abs ($2, $4)))         }
| FIX VAR DOT VAR DOT exp                         { (mk_exp (E_fix ($2, $4, $6)))     }
| APPLY exp exp                                   { (mk_exp (E_app ($2, $3)))         }
| FFI VAR LBRACKET explist RBRACKET               { (mk_exp (E_ffi ($2, $4)))         }
| MATCH exp WITH patandexplist END                { (mk_exp (E_match ($2, $4)))       }
| ASPAR exp exp                                   { (mk_exp (E_aspar ($2, $3)))       }
| ASSEC exp exp                                   { (mk_exp (E_assec ($2, $3)))       }
| UNBOX exp                                       { (mk_exp (E_unbox $2))             }
| MKWIRE exp exp                                  { (mk_exp (E_mkwire ($2, $3)))      }
| PROJWIRE exp exp                                { (mk_exp (E_projwire ($2, $3)))    }
| CONCATWIRE exp exp                              { (mk_exp (E_concatwire ($2, $3)))  }
| LPAREN exp RPAREN                               { $2                                }
| EOF                                             { Exp (E_const C_unit, None)        }
;

explist:
|                              { []       }
| exp                          { [ $1 ]   }
| exp SEMICOLON explist        { ($1::$3) }        
