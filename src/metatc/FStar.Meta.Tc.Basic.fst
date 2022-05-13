module FStar.Meta.Tc.Basic

open FStar.Syntax.Syntax
open FStar.TypeChecker.Env

module BU = FStar.Compiler.Util

let tc_term (en:env) (t:term) () : term =
  BU.print_string "\n\n\nMeta.Tc.tc_term\n\n";
  t
