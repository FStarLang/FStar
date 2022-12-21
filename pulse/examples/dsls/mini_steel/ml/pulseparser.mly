%{
   open Pulse_Syntax 
%}

%token TRUE

%start <term> prog
%%

prog:
  | TRUE    { Pulse_Syntax.Tm_Constant (Pulse_Syntax.Bool (true)) }
;

