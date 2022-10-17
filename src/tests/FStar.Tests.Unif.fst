(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
module FStar.Tests.Unif
//Unification tests
//open FSharp.Compatibility.OCaml
open FStar open FStar.Compiler
open FStar.Compiler.Effect
open FStar.Errors
open FStar.Compiler.Util
open FStar.Syntax.Syntax
open FStar.Tests.Pars
module S = FStar.Syntax.Syntax
module U = FStar.Syntax.Util
module SS = FStar.Syntax.Subst
module I = FStar.Ident
module P  = FStar.Syntax.Print
module N = FStar.TypeChecker.Normalize
module Rel = FStar.TypeChecker.Rel
module Env = FStar.TypeChecker.Env
module BU = FStar.Compiler.Util
open FStar.TypeChecker.Common
open FStar.TypeChecker.Env
open FStar.Ident
open FStar.Compiler.Range
open FStar.Tests.Util

let tcenv () = Pars.init()

let guard_to_string g = match g with
    | Trivial -> "trivial"
    | NonTrivial f ->
      N.term_to_string (tcenv()) f

let success = BU.mk_ref true

let fail msg =
    BU.print_string msg;
    success := false

let guard_eq i g g' =
    let b, g, g' = match g, g' with
        | Trivial, Trivial -> true, g, g'
        | NonTrivial f, NonTrivial f' ->
          let f = N.normalize  [Env.EraseUniverses] (tcenv()) f in
          let f' = N.normalize [Env.EraseUniverses] (tcenv()) f' in
          term_eq f f', NonTrivial f, NonTrivial f'
        | _ -> false, g, g' in
    if not b
    then fail <| BU.format3 "Test %s failed:\n\t\
                        Expected guard %s;\n\t\
                        Got guard      %s\n" (BU.string_of_int i) (guard_to_string g') (guard_to_string g);
    success := !success && b

let unify i x y g' check =
    BU.print1 "%s ..." (BU.string_of_int i);
    FStar.Main.process_args () |> ignore; //set options
    BU.print2 "Unify %s\nand %s\n" (FStar.Syntax.Print.term_to_string x) (FStar.Syntax.Print.term_to_string y);
    let g = Rel.teq (tcenv()) x y |> Rel.solve_deferred_constraints (tcenv()) |> Rel.simplify_guard (tcenv()) in
    guard_eq i g.guard_f g';
    check();
    Options.init()    //reset them; exceptions are fatal, so don't worry about resetting them in case guard_eq fails

let should_fail x y =
    try
        let g = Rel.teq (tcenv()) x y |> Rel.solve_deferred_constraints (tcenv()) in
        match g.guard_f with
            | Trivial -> fail (BU.format2 "%s and %s should not be unifiable\n" (P.term_to_string x) (P.term_to_string y))
            | NonTrivial f -> BU.print3 "%s and %s are unifiable if %s\n"  (P.term_to_string x) (P.term_to_string y) (P.term_to_string f)
    with Error(e, msg, r, _ctx) -> BU.print1 "%s\n" msg // FIXME?

let unify' x y =
    let x = pars x in
    let y = pars y in
    let g = Rel.teq (tcenv()) x y |> Rel.solve_deferred_constraints (tcenv()) in
    BU.print3 "%s and %s are unifiable with guard %s\n"  (P.term_to_string x) (P.term_to_string y) (guard_to_string g.guard_f)

let norm t = N.normalize [] (tcenv()) t

let check_core i x y =
  FStar.Main.process_args () |> ignore; //set options
  let env = tcenv () in
  let _ = 
    match FStar.TypeChecker.Core.check_term_equality env x y with
    | Inl None ->
      BU.print1 "%s core check ok\n" (BU.string_of_int i)
    | Inl (Some g) ->
      BU.print2 "%s core check computed guard %s ok\n" (BU.string_of_int i) (P.term_to_string g);
      success := false
    | Inr err ->
      success := false;
      BU.print2 "%s failed\n%s\n" (BU.string_of_int i) (FStar.TypeChecker.Core.print_error err)
  in
  Options.init()

let inst n tm =
   let rec aux out n =
    if n=0 then out
    else let t, _, _ = FStar.TypeChecker.Util.new_implicit_var "" dummyRange (init()) U.ktype0 in
         let u, _, _ = FStar.TypeChecker.Util.new_implicit_var "" dummyRange (init()) t in
         aux (u::out) (n - 1) in
   let us = aux [] n in
   norm (app tm us), us

let run_all () =
    BU.print_string "Testing the unifier\n";

    Options.__set_unit_tests();
    let unify_check n x y g f = unify n x y g f in
    let unify n x y g = unify n x y g (fun () -> ()) in
    let int_t = tc "Prims.int" in
    let x = S.gen_bv "x" None int_t |> S.bv_to_name in
    let y = S.gen_bv "y" None int_t |> S.bv_to_name in

    //syntactic equality of names
    unify 0 x x Trivial;

    //different names, equal with a guard
    unify 1 x y (NonTrivial (U.mk_eq2 U_zero U.t_bool x y));

    //equal after some reduction
    let id = tc "fun (x:bool) -> x" in
    unify 2 x (app id [x]) Trivial;

    //physical equality of terms
    let id = tc "fun (x:bool) -> x" in
    unify 3 id id Trivial;

    //alpha equivalence
    let id = tc "fun (x:bool) -> x" in
    let id' = tc "fun (y:bool) -> y" in
    unify 4 id id' Trivial; //(NonTrivial (pars "True /\ (forall x. True)"));

    //alpha equivalence 2
    unify 5 (tc "fun (x y:bool) -> x")
            (tc "fun (a b:bool) -> a")
            Trivial;

    //alpha equivalence 3
    unify 6 (tc "fun (x y z:bool) -> y")
            (tc "fun (a b c:bool) -> b")
            Trivial;

    //logical equality of distinct lambdas (questionable ... would only work for unit, or inconsistent context)
    unify 7 (tc "fun (x:int) (y:int) -> y")
            (tc "fun (x:int) (y:int) -> x")
            (NonTrivial (tc "(forall (x:int). (forall (y:int). y==x))"));

    //logical equality of distinct lambdas (questionable ... would only work for unit, or inconsistent context)
    unify 8 (tc "fun (x:int) (y:int) (z:int) -> y")
            (tc "fun (x:int) (y:int) (z:int) -> z")
            (NonTrivial (tc "(forall (x:int). (forall (y:int). (forall (z:int). y==z)))"));

    //imitation: unifies u to a constant
    FStar.Main.process_args () |> ignore; //set options
    let tm, us = inst 1 (tc "fun (u:Type0 -> Type0) (x:Type0) -> u x") in
    let sol = tc "fun (x:Type0) -> Prims.pair x x" in
    BU.print1 "Processed args: debug_at_level Core? %s\n" (BU.string_of_bool (Options.debug_at_level_no_module (Options.Other "Core")));
    unify_check 9 tm
            sol
            Trivial
            (fun () ->
                always 9 (term_eq (norm (List.hd us))
                                  (norm sol)));

    //imitation: unifies u to a lambda
    let tm, us = inst 1 (tc "fun (u: int -> int -> int) (x:int) -> u x") in
    let sol = tc "fun (x y:int) -> x + y" in
    unify_check 10 tm
            sol
            Trivial
            (fun () ->always 10 (term_eq (norm (List.hd us))
                                (norm sol)));

    let tm1 = tc ("x:int -> y:int{eq2 y x} -> bool") in
    let tm2 = tc ("x:int -> y:int -> bool") in
    unify 11 tm1 tm2
            (NonTrivial (tc "forall (x:int). (forall (y:int). y==x)"));

    let tm1 = tc ("a:Type0 -> b:(a -> Type0) -> x:a -> y:b x -> Tot Type0") in
    let tm2 = tc ("a:Type0 -> b:(a -> Type0) -> x:a -> y:b x -> Tot Type0") in
    unify 12 tm1 tm2
            Trivial;

    let tm1, tm2 =
        let int_typ = tc "int" in
        let x = FStar.Syntax.Syntax.new_bv None int_typ in

        let typ = tc "unit -> Type0" in
        let l = tc ("fun (q:(unit -> Type0)) -> q ()") in
        let q = FStar.Syntax.Syntax.new_bv None typ in
        let tm1 = norm (app l [FStar.Syntax.Syntax.bv_to_name q]) in

        let l = tc ("fun (p:unit -> Type0) -> p") in
        let unit = tc "()" in
        let env = Env.push_binders (init()) [S.mk_binder x; S.mk_binder q] in
        let u_p, _, _ = FStar.TypeChecker.Util.new_implicit_var "" dummyRange env typ in
        let tm2 = app (norm (app l [u_p])) [unit] in
        tm1, tm2
    in

    unify 13 tm1 tm2 Trivial;

    let tm1, tm2 =
        let int_typ = tc "int" in
        let x = FStar.Syntax.Syntax.new_bv None int_typ in

        let typ = tc "pure_post unit" in
        let l = tc ("fun (q:pure_post unit) -> q ()") in
        let q = FStar.Syntax.Syntax.new_bv None typ in
        let tm1 = norm (app l [FStar.Syntax.Syntax.bv_to_name q]) in

        let l = tc ("fun (p:pure_post unit) -> p") in
        let unit = tc "()" in
        let env = Env.push_binders (init()) [S.mk_binder x; S.mk_binder q] in
        let u_p, _, _ = FStar.TypeChecker.Util.new_implicit_var "" dummyRange env typ in
        let tm2 = app (norm (app l [u_p])) [unit] in
        tm1, tm2
    in

    unify 14 tm1 tm2 Trivial;

    let tm1, tm2 =
      let _ = Pars.pars_and_tc_fragment 
        "let ty0 n = x:int { x >= n }\n\
         let ty1 n = x:ty0 n { x > n }\n\
         assume val tc (t:Type0) : Type0"
      in
      let t0 = tc "ty1 17" in
      let t1 = tc "x:ty0 17 { x > 17 }" in
      t0, t1
    in
    check_core 15 tm1 tm2;

    let tm1, tm2 =
      let t0 = tc "x:int { x >= 17 /\ x > 17 }" in
      let t1 = tc "x:ty0 17 { x > 17 }" in
      t0, t1
    in
    check_core 16 tm1 tm2;

    let tm1, tm2 =
      let _ = Pars.pars_and_tc_fragment 
        "let defn17_0 (x:nat) : nat -> nat -> Type0 = fun y z -> a:int { a + x == y + z }"
      in
      let t0 = tc "defn17_0 0 1 2" in
      let t1_head = tc "(defn17_0 0)" in
      let arg1 = tc "1" in
      let arg2 = tc "2" in      
      let t1 = S.mk_Tm_app t1_head [(arg1, None); (arg2, None)] t0.pos in
      t0, t1
    in
    check_core 17 tm1 tm2;


    Options.__clear_unit_tests();

    if !success
    then BU.print_string "Unifier ok\n";
    !success
