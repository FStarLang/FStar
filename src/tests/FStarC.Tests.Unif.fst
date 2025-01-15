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
module FStarC.Tests.Unif
//Unification tests
//open FSharp.Compatibility.OCaml

open FStar
open FStarC
open FStarC
open FStarC.Effect
open FStarC.Errors
open FStarC.Util
open FStarC.Syntax.Syntax
open FStarC.Tests.Pars
module S = FStarC.Syntax.Syntax
module U = FStarC.Syntax.Util
module SS = FStarC.Syntax.Subst
module I = FStarC.Ident
module P  = FStarC.Syntax.Print
module N = FStarC.TypeChecker.Normalize
module Rel = FStarC.TypeChecker.Rel
module Env = FStarC.TypeChecker.Env
module BU = FStarC.Util
open FStarC.TypeChecker.Common
open FStarC.TypeChecker.Env
open FStarC.Ident
open FStarC.Range
open FStarC.Tests.Util

open FStarC.Class.Show

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

let unify i bvs x y g' check =
    BU.print1 "%s ..." (BU.string_of_int i);
    Options.parse_cmd_line () |> ignore; //set options
    BU.print2 "Unify %s\nand %s\n" (show x) (show y);
    let tcenv = tcenv() in
    let tcenv = Env.push_bvs tcenv bvs in
    let g = Rel.teq tcenv x y |> Rel.solve_deferred_constraints tcenv |> Rel.simplify_guard tcenv in
    guard_eq i g.guard_f g';
    check();
    Options.init()    //reset them; exceptions are fatal, so don't worry about resetting them in case guard_eq fails

let should_fail x y =
    try
        let g = Rel.teq (tcenv()) x y |> Rel.solve_deferred_constraints (tcenv()) in
        match g.guard_f with
            | Trivial -> fail (BU.format2 "%s and %s should not be unifiable\n" (show x) (show y))
            | NonTrivial f -> BU.print3 "%s and %s are unifiable if %s\n"  (show x) (show y) (show f)
    with Error(e, msg, r, _ctx) -> BU.print1 "%s\n" (Errors.rendermsg msg) // FIXME?

let unify' x y =
    let x = pars x in
    let y = pars y in
    let g = Rel.teq (tcenv()) x y |> Rel.solve_deferred_constraints (tcenv()) in
    BU.print3 "%s and %s are unifiable with guard %s\n"  (show x) (show y) (guard_to_string g.guard_f)

let norm t = N.normalize [] (tcenv()) t

let check_core i subtyping guard_ok x y =
  Options.parse_cmd_line () |> ignore; //set options
  let env = tcenv () in
  let res = 
    if subtyping
    then FStarC.TypeChecker.Core.check_term_subtyping true true env x y
    else FStarC.TypeChecker.Core.check_term_equality  true true env x y
  in
  let _ = 
    match res with
    | Inl None ->
      BU.print1 "%s core check ok\n" (BU.string_of_int i)
    | Inl (Some g) ->
      BU.print2 "%s core check computed guard %s ok\n" (BU.string_of_int i) (show g);
      if not guard_ok
      then success := false
    | Inr err ->
      success := false;
      BU.print2 "%s failed\n%s\n" (BU.string_of_int i) (FStarC.TypeChecker.Core.print_error err)
  in
  Options.init()

let check_core_typing i e t =
  Options.parse_cmd_line () |> ignore; //set options
  let env = tcenv () in
  let _ =
    match FStarC.TypeChecker.Core.check_term env e t true with
    | Inl None -> 
      BU.print1 "%s core typing ok\n" (BU.string_of_int i)
    | Inl (Some g) -> 
      BU.print1 "%s core typing produced a guard\n" (BU.string_of_int i);
      success := false
    | Inr err ->
      success := false;
      BU.print2 "%s failed\n%s\n" (BU.string_of_int i) (FStarC.TypeChecker.Core.print_error err)      
  in
  Options.init()

let inst n tm =
   let rec aux out n =
    if n=0 then out
    else let t, _, _ = FStarC.TypeChecker.Util.new_implicit_var "" dummyRange (init()) U.ktype0 false in
         let u, _, _ = FStarC.TypeChecker.Util.new_implicit_var "" dummyRange (init()) t false in
         aux (u::out) (n - 1) in
   let us = aux [] n in
   norm (app tm us), us

let run_all () =
    BU.print_string "Testing the unifier\n";

    Options.__set_unit_tests();
    let unify_check n bvs x y g f = unify n bvs x y g f in
    let unify n bvs x y g = unify n bvs x y g (fun () -> ()) in
    let int_t = tc "Prims.int" in
    let x_bv = S.gen_bv "x" None int_t in
    let y_bv = S.gen_bv "y" None int_t in
    let x = S.bv_to_name x_bv in
    let y = S.bv_to_name y_bv in

    //syntactic equality of names
    unify 0 [x_bv] x x Trivial;

    //different names, equal with a guard
    unify 1 [x_bv;y_bv] x y (NonTrivial (U.mk_eq2 U_zero U.t_bool x y));

    //equal after some reduction
    let id = tc "fun (x:bool) -> x" in
    unify 2 [x_bv] x (app id [x]) Trivial;

    //physical equality of terms
    let id = tc "fun (x:bool) -> x" in
    unify 3 [] id id Trivial;

    //alpha equivalence
    let id = tc "fun (x:bool) -> x" in
    let id' = tc "fun (y:bool) -> y" in
    unify 4 [] id id' Trivial; //(NonTrivial (pars "True /\ (forall x. True)"));

    //alpha equivalence 2
    unify 5 []
            (tc "fun (x y:bool) -> x")
            (tc "fun (a b:bool) -> a")
            Trivial;

    //alpha equivalence 3
    unify 6 []
            (tc "fun (x y z:bool) -> y")
            (tc "fun (a b c:bool) -> b")
            Trivial;

    //logical equality of distinct lambdas (questionable ... would only work for unit, or inconsistent context)
    unify 7 []
            (tc "fun (x:int) (y:int) -> y")
            (tc "fun (x:int) (y:int) -> x")
            (NonTrivial (tc "(forall (x:int). (forall (y:int). y==x))"));

    //logical equality of distinct lambdas (questionable ... would only work for unit, or inconsistent context)
    unify 8 []
            (tc "fun (x:int) (y:int) (z:int) -> y")
            (tc "fun (x:int) (y:int) (z:int) -> z")
            (NonTrivial (tc "(forall (x:int). (forall (y:int). (forall (z:int). y==z)))"));

    //imitation: unifies u to a constant
    Options.parse_cmd_line () |> ignore; //set options
    let tm, us = inst 1 (tc "fun (u:Type0 -> Type0) (x:Type0) -> u x") in
    let sol = tc "fun (x:Type0) -> Prims.pair x x" in
    unify_check 9 [] tm
            sol
            Trivial
            (fun () ->
                always 9 (term_eq (norm (List.hd us))
                                  (norm sol)));

    //imitation: unifies u to a lambda
    let tm, us = inst 1 (tc "fun (u: int -> int -> int) (x:int) -> u x") in
    let sol = tc "fun (x y:int) -> x + y" in
    unify_check 10 [] tm
            sol
            Trivial
            (fun () ->always 10 (term_eq (norm (List.hd us))
                                (norm sol)));

    let tm1 = tc ("x:int -> y:int{eq2 y x} -> bool") in
    let tm2 = tc ("x:int -> y:int -> bool") in
    unify 11 [] tm1 tm2
            (NonTrivial (tc "forall (x:int). (forall (y:int). y==x)"));

    let tm1 = tc ("a:Type0 -> b:(a -> Type0) -> x:a -> y:b x -> Tot Type0") in
    let tm2 = tc ("a:Type0 -> b:(a -> Type0) -> x:a -> y:b x -> Tot Type0") in
    unify 12 [] tm1 tm2
            Trivial;

    let tm1, tm2, bvs_13 =
        let int_typ = tc "int" in
        let x = FStarC.Syntax.Syntax.new_bv None int_typ in

        let typ = tc "unit -> Type0" in
        let l = tc ("fun (q:(unit -> Type0)) -> q ()") in
        let q = FStarC.Syntax.Syntax.new_bv None typ in
        let tm1 = norm (app l [FStarC.Syntax.Syntax.bv_to_name q]) in

        let l = tc ("fun (p:unit -> Type0) -> p") in
        let unit = tc "()" in
        let env = Env.push_binders (init()) [S.mk_binder x; S.mk_binder q] in
        let u_p, _, _ = FStarC.TypeChecker.Util.new_implicit_var "" dummyRange env typ false in
        let tm2 = app (norm (app l [u_p])) [unit] in
        tm1, tm2, [x;q]
    in

    unify 13 bvs_13 tm1 tm2 Trivial;

    let tm1, tm2, bvs_14 =
        let int_typ = tc "int" in
        let x = FStarC.Syntax.Syntax.new_bv None int_typ in

        let typ = tc "pure_post unit" in
        let l = tc ("fun (q:pure_post unit) -> q ()") in
        let q = FStarC.Syntax.Syntax.new_bv None typ in
        let tm1 = norm (app l [FStarC.Syntax.Syntax.bv_to_name q]) in

        let l = tc ("fun (p:pure_post unit) -> p") in
        let unit = tc "()" in
        let env = Env.push_binders (init()) [S.mk_binder x; S.mk_binder q] in
        let u_p, _, _ = FStarC.TypeChecker.Util.new_implicit_var "" dummyRange env typ false in
        let tm2 = app (norm (app l [u_p])) [unit] in
        tm1, tm2, [x;q]
    in

    unify 14 bvs_14 tm1 tm2 Trivial;

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
    check_core 15 false false tm1 tm2;

    let tm1, tm2 =
      let t0 = tc "x:int { x >= 17 /\ x > 17 }" in
      let t1 = tc "x:ty0 17 { x > 17 }" in
      t0, t1
    in
    check_core 16 false false tm1 tm2;

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
    check_core 17 false false tm1 tm2;

    let tm1, tm2 = 
      let t0 = tc "dp:((dtuple2 int (fun (y:int) -> z:int{ z > y })) <: Type0) { let (| x, _ |) = dp in x > 17 }" in
      let t1 = tc "(dtuple2 int (fun (y:int) -> z:int{ z > y }))" in
      t0, t1
    in
    check_core 18 true false tm1 tm2;

    let tm1, tm2 = 
      let _ = Pars.pars_and_tc_fragment 
        "type vprop' = { t:Type0 ; n:nat }"
      in
      let t0 = tc "x:(({ t=bool; n=0 }).t <: Type0) { x == false }" in
      let t1 = tc "x:bool{ x == false }" in
      t0, t1
    in
    check_core 19 false false tm1 tm2;


    let tm1, tm2 = 
      let t0 = tc "int" in
      let t1 = tc "j:(i:nat{ i > 17 } <: Type0){j > 42}" in
      t0, t1
    in
    check_core 20 true true tm1 tm2;

    let tm, ty = 
      let _ = Pars.pars_and_tc_fragment "assume val tstr21 (x:string) : Type0" in
      let t0 = tc "(fun (x:bool) (y:int) (z: (fun (x:string) -> tstr21 x) \"hello\") -> x)" in
      let ty = tc "bool -> int -> tstr21 \"hello\" -> bool" in
      t0, ty
    in
    check_core_typing 21 tm ty;

    Options.__clear_unit_tests();

    if !success
    then BU.print_string "Unifier ok\n";
    !success
