%{
(* This is just a simple parser for the arguments
to --warn_error. *)
open Prims
open FStarC_Errors_Codes

%}

%token <Z.t> INT

%token MINUS
%token PLUS
%token AT
%token DOT_DOT
%token EOF

%start warn_error_list
%type <(FStarC_Errors_Codes.error_flag * (Z.t * Z.t)) list> warn_error_list
%%

warn_error_list:
  | e=warn_error EOF { e }

warn_error:
  | l=list(flag range { ($1, $2) })
    { l }

flag:
  | AT    { CAlwaysError }
  | PLUS  { CWarning }
  | MINUS { CSilent }

range:
  | i1=INT DOT_DOT i2=INT
    { (i1, i2) }
  | i=INT
    { (i, i) }
