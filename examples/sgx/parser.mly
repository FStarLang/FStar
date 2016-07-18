%{
  open Ast
  open Printf
  open Lexing
%}

%token <int> INTEGER
%token <string> VAR
%token PLUS MINUS TIMES MODULO UNDERSCORE LPAREN RPAREN LCURLY RCURLY COMMA SEQ COLON NEQUALS EQUALS TRUE FALSE CALL
       IF THEN ELSE ENDIF EOF ASSIGN SKIP STORE LOAD
       INT BOOL  STRING LSQBR RSQBR LESSTHAN 

%type <Ast.program> program
%type <Ast.stmt> stmt
%type <Ast.exp> exp

%start program
 
%%

program: stmtlist           		                {(Seq $1 )}

stmtlist : stmt 					{ [$1] }
         | stmt stmtlist				{ [$1] @ $2 }

stmt : IF aexp THEN stmtlist ELSE stmtlist ENDIF SEQ 	{ If($2, $4, $6) }
     | SKIP  SEQ                                        { Skip }
     | exp ASSIGN exp SEQ		    		{ Assign($1, $3)}
     | CALL LPAREN exp RPAREN SEQ	    		{ Call($3) }
     | LOAD exp COMMA exp SEQ                                 { Load($2, $4) }
     | STORE exp COMMA exp SEQ                                { Store($2, $4) }

exp : 
    | aexp 				{ $1 }

aexp: 	VAR                          { Reg $1}
    | INTEGER                        {Constant($1) }
