#light "off"
module FStar.Tests.Unif
//Unification tests
open FStar
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

let dummy = TypeChecker.Env.no_solver_env TypeChecker.Tc.type_of

let guard_to_string g = match g with
    | Trivial -> "trivial"
    | NonTrivial f ->
      N.term_to_string dummy f

let guard_eq i g g' = 
    let b = match g, g' with 
        | Trivial, Trivial -> true
        | NonTrivial f, NonTrivial f' ->
          let f = N.normalize [] dummy f in
          let f' = N.normalize [] dummy f' in
          term_eq f f'
        | _ -> false in
    if not b 
    then Printf.printf "Test %d failed:\n\t\
                        Expected guard %s;\n\t\
                        Got guard      %s\n" i (guard_to_string g') (guard_to_string g)


let unify i x y g' = 
    let g = Rel.teq dummy x y |> Rel.solve_deferred_constraints dummy in
    guard_eq i g.guard_f g'

let should_fail x y =
    try 
        let g = Rel.teq dummy x y |> Rel.solve_deferred_constraints dummy in
        match g.guard_f with  
            | Trivial -> failwith (Printf.sprintf "%s and %s should not be unifiable\n" (P.term_to_string x) (P.term_to_string y))
            | NonTrivial f -> Printf.printf "%s and %s are unifiable if %s\n"  (P.term_to_string x) (P.term_to_string y) (P.term_to_string f)
    with Error(msg, r) -> print_string msg; print_newline()
    
let unify' x y = 
    let x = pars x in
    let y = pars y in
    let g = Rel.teq dummy x y |> Rel.solve_deferred_constraints dummy in
    Printf.printf "%s and %s are unifiable with guard %s\n"  (P.term_to_string x) (P.term_to_string y) (guard_to_string g.guard_f)

let norm t = N.normalize [] dummy t

let inst n tm = 
   let rec aux out n = 
    if n=0 then out
    else let u, _ = Rel.new_uvar dummyRange [] tun in
         aux (u::out) (n - 1) in
   let us = aux [] n in 
   norm (app tm us), us

let run_all debug = 
   try
       Printf.printf "Testing the unifier\n";
       if debug 
       then (Options.debug := ["dummy"];
             Options.debug_level := [Options.Other "Rel"; Options.Other "RelCheck"];
             Options.print_implicits := true;
             Options.print_real_names := true);
       let id  = pars "fun x -> x" in
       let id' = pars "fun y -> y" in

       //syntactic equality of names
       unify 0 x x Trivial;

       //different names, equal with a guard
       unify 1 x y (NonTrivial (app (pars "Eq2") [x;y]));
       
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
//             (NonTrivial (pars "True /\ (forall x. True /\ (forall y. True))"));

       //alpha equivalence 3
       unify 6 (pars "fun x y z -> y")
               (pars "fun a b c -> b")
             Trivial;
//             (NonTrivial (pars "True /\ (forall x. True /\ (forall y. True /\ (forall z. True)))"));

       //logical equality of distinct lambdas (questionable ... would only work for unit, or inconsistent context)
       unify 7 (pars "fun x y -> y")
               (pars "fun x y -> x")
               (NonTrivial (pars "(forall x. (forall y. Eq2 y x))"));
//             (NonTrivial (pars "True /\ (forall x. True /\ (forall y. Eq2 y x))"));

       //logical equality of distinct lambdas (questionable ... would only work for unit, or inconsistent context)
       unify 8 (pars "fun x y z -> y")
               (pars "fun x y z -> z")
               (NonTrivial (pars "(forall x. (forall y. (forall z. Eq2 y z)))")); 
//             (NonTrivial (pars "True /\ (forall x. True /\ (forall y. True /\ (forall z. Eq2 y z)))")); 

       //imitation: unifies u to a constant
       let tm, us = inst 1 (pars "fun u x -> u x") in
       unify 9 tm 
               (pars "fun x -> Tuple2 x x") 
               Trivial;
//             (NonTrivial (pars "True /\ (forall x. True)"));
       assert (term_eq (norm (List.hd us))
                       (norm (pars "fun x -> Tuple2 x x")));

       //imitation: unifies u to a lambda
       let tm, us = inst 1 (pars "fun u x -> u x") in
       unify 10 tm 
                (pars "fun x y -> x + y") 
                Trivial;
//             (NonTrivial (pars "True /\ (forall x. True)"));
       assert (term_eq (norm (List.hd us))
                       (norm (pars "fun x y -> x + y")));

      
       let tm1 = pars ("x:int -> y:int{Eq2 y x} -> bool") in
       let tm2 = pars ("x:int -> y:int -> bool") in
       unify 11 tm1 tm2
                (NonTrivial (pars "forall (x:int). (forall (y:int). Eq2 y x <==> True)"));

       let tm1 = pars ("a:Type0 -> b:(a -> Type0) -> x:a -> y:b x -> Tot Type0") in
       let tm2 = pars ("a:Type0 -> b:(a -> Type0) -> x:a -> y:b x -> Tot Type0") in
       unify 12 tm1 tm2
                Trivial;

       Printf.printf "Unifier ok\n";

   with Error(msg, r) -> print_string msg; print_newline()
