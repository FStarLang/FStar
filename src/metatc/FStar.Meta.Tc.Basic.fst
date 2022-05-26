module FStar.Meta.Tc.Basic

open FStar.Syntax.Syntax
open FStar.TypeChecker.Env

module BU = FStar.Compiler.Util
module List = FStar.Compiler.List
module Rel = FStar.TypeChecker.Rel

open FStar.Tactics.Result

type metatc 'a = unit -> tc_result 'a

let return (x:'a) : metatc 'a = fun _ -> x
let bind (f:metatc 'a) (g:'a -> metatc 'b) : metatc 'b =
  fun _ ->
  let r = f () in
  match r with
  | Tc_success x -> g x ()
  | Tc_failure m -> Tc_failure m
  
type valid_prop (_:env) (_:typ) = unit

let check_prop_validity (en:env) (t:typ) : metatc (valid_prop en t) =
  fun _ ->
  let errs = Rel.query_formula en t in
  if List.length errs = 0
  then Tc_success ()
  else Tc_failure ""
