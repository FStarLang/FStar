#light "off"
module FStar.Tests.Unif
//Unification tests
//open FSharp.Compatibility.OCaml
open FStar
open FStar.All
open FStar.Errors
open FStar.Util
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
module BU = FStar.Util
open FStar.TypeChecker.Common
open FStar.TypeChecker.Env
open FStar.Ident
open FStar.Range
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
    with Error(e, msg, r) -> BU.print1 "%s\n" msg

let unify' x y =
    let x = pars x in
    let y = pars y in
    let g = Rel.teq (tcenv()) x y |> Rel.solve_deferred_constraints (tcenv()) in
    BU.print3 "%s and %s are unifiable with guard %s\n"  (P.term_to_string x) (P.term_to_string y) (guard_to_string g.guard_f)

let norm t = N.normalize [] (tcenv()) t

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
    let id = tc "fun x -> x" in
    unify 2 x (app id [x]) Trivial;

    //physical equality of terms
    let id = tc "fun x -> x" in
    unify 3 id id Trivial;

    //alpha equivalence
    let id = tc "fun x -> x" in
    let id' = tc "fun y -> y" in
    unify 4 id id' Trivial; //(NonTrivial (pars "True /\ (forall x. True)"));

    //alpha equivalence 2
    unify 5 (tc "fun x y -> x")
            (tc "fun a b -> a")
            Trivial;

    //alpha equivalence 3
    unify 6 (tc "fun x y z -> y")
            (tc "fun a b c -> b")
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
    let tm, us = inst 1 (tc "fun u x -> u x") in
    let sol = tc "fun x -> c_and x x" in
    unify_check 9 tm
            sol
            Trivial
            (fun () ->
                always 9 (term_eq (norm (List.hd us))
                                  (norm sol)));

    //imitation: unifies u to a lambda
    let tm, us = inst 1 (tc "fun u x -> u x") in
    let sol = tc "fun x y -> x + y" in
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

    Options.__clear_unit_tests();

    if !success
    then BU.print_string "Unifier ok\n";
    !success
