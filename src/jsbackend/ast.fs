(*
   Copyright 2014 Antoine Delignat-Lavaud and Microsoft Research
   This file is taken from the Defensive Javascript typechecker
   and is also available under the 2-clause BSD licence.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module FStar.Backends.JS.Ast

(* Type of Javascript program *)
type t = list<source_t>

and source_t =
  | JS_Statement of statement_t
  | JS_FunctionDeclaration of function_t 

and statement_t = 
  | JSS_Empty
  | JSS_Debugger
  | JSS_Return of option<expression_t>
  | JSS_Throw of expression_t
  | JSS_Continue of option<identifier_t>
  | JSS_Break of option<identifier_t>
  | JSS_Try of statement_t * option<(identifier_t * statement_t)> * option<statement_t> 
  | JSS_Block of list<statement_t>
  | JSS_Label of identifier_t * statement_t
  | JSS_Expression of expression_t
  | JSS_Declaration of list<(identifier_t * option<expression_t>)>
  | JSS_If of expression_t * statement_t * option<statement_t>
  | JSS_Do of statement_t * expression_t
  | JSS_While of expression_t * statement_t
  | JSS_For of option<forinit_t> * option<expression_t> * option<expression_t> * statement_t
  | JSS_Forin of forinit_t * expression_t * statement_t
  | JSS_With of expression_t * statement_t
  | JSS_Switch of expression_t * option<list<statement_t>> * list<(expression_t * list<statement_t>)>

and forinit_t = 
  | JSF_Expression of expression_t
  | JSF_Declaration of list<(identifier_t * option<expression_t>)>

and identifier_t = string
and function_t = option<identifier_t> * list<identifier_t> * t

and object_prop_t = 
  | JSP_Property of string * expression_t
  | JSP_Getter of string * function_t
  | JSP_Setter of string * function_t

and expression_t = 
  | JSE_This
  | JSE_Null
  | JSE_Undefined
  | JSE_Elision
  | JSE_Bool of bool
  | JSE_Number of float
  | JSE_String of string
  | JSE_Regexp of (string * string)
  | JSE_Identifier of identifier_t
  | JSE_Array of list<expression_t>
  | JSE_Object of list<object_prop_t>
  | JSE_New of expression_t * option<list<expression_t>>
  | JSE_Typeof of expression_t
  | JSE_Delete of expression_t
  | JSE_Void of expression_t
  | JSE_Function of function_t
  | JSE_Plus of expression_t
  | JSE_Preincr of expression_t
  | JSE_Postincr of expression_t
  | JSE_Predecr of expression_t
  | JSE_Postdecr of expression_t
  | JSE_Minus of expression_t
  | JSE_Lnot of expression_t
  | JSE_Bnot of expression_t
  | JSE_Conditional of (expression_t * expression_t * expression_t)
  | JSE_Sequence of list<expression_t>
  | JSE_Assign of (expression_t * expression_t)
  | JSE_Ashassign of (expression_t * expression_t)
  | JSE_Property of (expression_t * expression_t)
  | JSE_Dot of (expression_t * identifier_t)
  | JSE_In of (expression_t * expression_t)
  | JSE_Instanceof of (expression_t * expression_t)
  | JSE_Add of (expression_t * expression_t)
  | JSE_Sub of (expression_t * expression_t)
  | JSE_Multiply of (expression_t * expression_t)
  | JSE_Mod of (expression_t * expression_t)
  | JSE_Divide of (expression_t * expression_t)
  | JSE_Lsh of (expression_t * expression_t)
  | JSE_Rsh of (expression_t * expression_t)
  | JSE_Ash of (expression_t * expression_t)
  | JSE_Lor of (expression_t * expression_t)
  | JSE_Land of (expression_t * expression_t)
  | JSE_Bor of (expression_t * expression_t)
  | JSE_Band of (expression_t * expression_t)
  | JSE_Bxor of (expression_t * expression_t)
  | JSE_Equal of (expression_t * expression_t)
  | JSE_Lt of (expression_t * expression_t)
  | JSE_Gt of (expression_t * expression_t)
  | JSE_Le of (expression_t * expression_t)
  | JSE_Ge of (expression_t * expression_t)
  | JSE_Sequal of (expression_t * expression_t)
  | JSE_Call of expression_t * list<expression_t>
