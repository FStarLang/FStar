#light "off"
module FStar.Tests.Unif
//Unification tests
open FStar
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
open FStar.TypeChecker.Common
open FStar.Ident
open FStar.Range
open FStar.Tests.Util

let x = S.gen_bv "x" None S.tun |> S.bv_to_name
let y = S.gen_bv "y" None S.tun |> S.bv_to_name

let tcenv () = Pars.init() |> snd

let guard_to_string g = match g with
    | Trivial -> "trivial"
    | NonTrivial f ->
      N.term_to_string (tcenv()) f

let guard_eq i g g' =
    let b, g, g' = match g, g' with
        | Trivial, Trivial -> true, g, g'
        | NonTrivial f, NonTrivial f' ->
          let f = N.normalize  [N.EraseUniverses] (tcenv()) f in
          let f' = N.normalize [N.EraseUniverses] (tcenv()) f' in
          term_eq f f', NonTrivial f, NonTrivial f'
        | _ -> false, g, g' in
    if not b then
    let msg =
        Printf.sprintf "Test %d failed:\n\t\
                        Expected guard %s;\n\t\
                        Got guard      %s\n" i (guard_to_string g') (guard_to_string g) in
    raise (Error(msg, Range.dummyRange))

let unify i x y g' =
    printfn "%d ..." i;
    FStar.Main.process_args () |> ignore; //set options
    printfn "Unify %s\nand %s\n" (FStar.Syntax.Print.term_to_string x) (FStar.Syntax.Print.term_to_string y);
    let g = Rel.teq (tcenv()) x y |> Rel.solve_deferred_constraints (tcenv()) in
    guard_eq i g.guard_f g';
    Options.init()    //reset them; exceptions are fatal, so don't worry about resetting them in case guard_eq fails

let should_fail x y =
    try
        let g = Rel.teq (tcenv()) x y |> Rel.solve_deferred_constraints (tcenv()) in
        match g.guard_f with
            | Trivial -> failwith (Printf.sprintf "%s and %s should not be unifiable\n" (P.term_to_string x) (P.term_to_string y))
            | NonTrivial f -> Printf.printf "%s and %s are unifiable if %s\n"  (P.term_to_string x) (P.term_to_string y) (P.term_to_string f)
    with Error(msg, r) -> print_string msg; print_newline()

let unify' x y =
    let x = pars x in
    let y = pars y in
    let g = Rel.teq (tcenv()) x y |> Rel.solve_deferred_constraints (tcenv()) in
    Printf.printf "%s and %s are unifiable with guard %s\n"  (P.term_to_string x) (P.term_to_string y) (guard_to_string g.guard_f)

let norm t = N.normalize [] (tcenv()) t

let inst n tm =
   let rec aux out n =
    if n=0 then out
    else let t, _ = Rel.new_uvar dummyRange [] U.ktype0 in
         let u, _ = Rel.new_uvar dummyRange [] t in
         aux (u::out) (n - 1) in
   let us = aux [] n in
   norm (app tm us), us

let run_all () =
    Printf.printf "Testing the unifier\n";
    let id  = pars "fun x -> x" in
    let id' = pars "fun y -> y" in

    Options.__set_unit_tests();

    //syntactic equality of names
    unify 0 x x Trivial;

    //different names, equal with a guard
    unify 1 x y (NonTrivial (app (pars "eq2") [x;y]));

    //equal after some reduction
    unify 2 x (app id [x]) Trivial;

    //physical equality of terms
    unify 3 id id Trivial;

    //alpha equivalence
    unify 4 id id' Trivial; //(NonTrivial (pars "True /\ (forall x. True)"));

    //alpha equivalence 2
    unify 5 (pars "fun x y -> x")
            (pars "fun a b -> a")
            Trivial;

    //alpha equivalence 3
    unify 6 (pars "fun x y z -> y")
            (pars "fun a b c -> b")
            Trivial;

    //logical equality of distinct lambdas (questionable ... would only work for unit, or inconsistent context)
    unify 7 (pars "fun (x:int) (y:int) -> y")
            (pars "fun (x:int) (y:int) -> x")
            (NonTrivial (tc "(forall (x:int). (forall (y:int). y==x))"));

    //logical equality of distinct lambdas (questionable ... would only work for unit, or inconsistent context)
    unify 8 (pars "fun (x:int) (y:int) (z:int) -> y")
            (pars "fun (x:int) (y:int) (z:int) -> z")
            (NonTrivial (tc "(forall (x:int). (forall (y:int). (forall (z:int). y==z)))"));

    //imitation: unifies u to a constant
    let tm, us = inst 1 (pars "fun u x -> u x") in
    unify 9 tm
            (pars "fun x -> tuple2 x x")
            Trivial;

    always 9 (term_eq (norm (List.hd us))
                    (norm (pars "fun x -> tuple2 x x")));

    //imitation: unifies u to a lambda
    let tm, us = inst 1 (pars "fun u x -> u x") in
    unify 10 tm
            (pars "fun x y -> x + y")
            Trivial;
    always 10 (term_eq (norm (List.hd us))
                    (norm (pars "fun x y -> x + y")));


    let tm1 = tc ("x:int -> y:int{eq2 y x} -> bool") in
    let tm2 = tc ("x:int -> y:int -> bool") in
    unify 11 tm1 tm2
            (NonTrivial (tc "forall (x:int). (forall (y:int). y==x <==> True)"));

    let tm1 = pars ("a:Type0 -> b:(a -> Type0) -> x:a -> y:b x -> Tot Type0") in
    let tm2 = pars ("a:Type0 -> b:(a -> Type0) -> x:a -> y:b x -> Tot Type0") in
    unify 12 tm1 tm2
            Trivial;

    Options.__clear_unit_tests();

    Printf.printf "Unifier ok\n";

