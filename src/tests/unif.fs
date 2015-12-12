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
open FStar.Ident
open FStar.Range
open FStar.Tests.Util

let x = S.gen_bv "x" None S.tun |> S.bv_to_name
let y = S.gen_bv "y" None S.tun |> S.bv_to_name
let id  = pars "fun x -> x"
let id' = pars "fun y -> y"

let guard_to_string g = match g with
    | Rel.Trivial -> "trivial"
    | Rel.NonTrivial f ->
      N.term_to_string Env.dummy f

let guard_eq g g' = 
    let b = match g, g' with 
        | Rel.Trivial, Rel.Trivial -> true
        | Rel.NonTrivial f, Rel.NonTrivial f' ->
          let f = N.normalize [] Env.dummy f in
          let f' = N.normalize [] Env.dummy f' in
          term_eq f f'
        | _ -> false in
    if not b 
    then Printf.printf "Expected guard %s;\n\
                        Got guard      %s\n" (guard_to_string g') (guard_to_string g);
    b


let unify x y g' = 
    let g = Rel.teq Env.dummy x y |> Rel.solve_deferred_constraints Env.dummy in
    assert (guard_eq g.guard_f g')

let should_fail x y =
    try 
        let g = Rel.teq Env.dummy x y |> Rel.solve_deferred_constraints Env.dummy in
        match g.guard_f with  
            | Rel.Trivial -> failwith (Printf.sprintf "%s and %s should not be unifiable\n" (P.term_to_string x) (P.term_to_string y))
            | Rel.NonTrivial f -> Printf.printf "%s and %s are unifiable if %s\n"  (P.term_to_string x) (P.term_to_string y) (P.term_to_string f)
    with Error(msg, r) -> print_string msg; print_newline()
    
let unify' x y = 
    let x = pars x in
    let y = pars y in
    let g = Rel.teq Env.dummy x y |> Rel.solve_deferred_constraints Env.dummy in
    Printf.printf "%s and %s are unifiable with guard %s\n"  (P.term_to_string x) (P.term_to_string y) (guard_to_string g.guard_f)

let norm t = N.normalize [] Env.dummy t

let inst n tm = 
   let rec aux out n = 
    if n=0 then out
    else let u, _ = Rel.new_uvar dummyRange [] tun in
         aux (u::out) (n - 1) in
   let us = aux [] n in 
   norm (app tm us), us

let run_all debug = 
   try
       if debug 
       then (Options.debug := ["dummy"];
             Options.debug_level := [Options.Other "Rel"]);
       //syntactic equality of names
       unify x x Rel.Trivial;

       //different names, equal with a guard
       unify x y (Rel.NonTrivial (app (pars "Eq2") [x;y]));
       
       //equal after some reduction
       unify x (app id [x]) Rel.Trivial;
       
       //physical equality of terms
       unify id id Rel.Trivial;

       //alpha equivalence
       unify id id' (Rel.NonTrivial (pars "True /\ (forall x. True)"));

       //alpha equivalence 2
       unify (pars "fun x y -> x")
             (pars "fun a b -> a")
             (Rel.NonTrivial (pars "True /\ (forall x. True /\ (forall y. True))"));

       //alpha equivalence 3
       unify (pars "fun x y z -> y")
             (pars "fun a b c -> b")
             (Rel.NonTrivial (pars "True /\ (forall x. True /\ (forall y. True /\ (forall z. True)))"));

       //logical equality of distinct lambdas (questionable ... would only work for unit, or inconsistent context)
       unify (pars "fun x y -> y")
             (pars "fun x y -> x")
             (Rel.NonTrivial (pars "True /\ (forall x. True /\ (forall y. Eq2 y x))"));

       //logical equality of distinct lambdas (questionable ... would only work for unit, or inconsistent context)
       unify (pars "fun x y z -> y")
             (pars "fun x y z -> z")
             (Rel.NonTrivial (pars "True /\ (forall x. True /\ (forall y. True /\ (forall z. Eq2 y z)))")); 

       //imitation: unifies u to a constant
       let tm, us = inst 1 (pars "fun u x -> u x") in
       unify tm 
             (pars "fun x -> Tuple2 x x") 
             (Rel.NonTrivial (pars "True /\ (forall x. True)"));
       assert (term_eq (norm (List.hd us))
                       (norm (pars "fun x -> Tuple2 x x")));

       //imitation: unifies u to a lambda
       let tm, us = inst 1 (pars "fun u x -> u x") in
       unify tm 
             (pars "fun x y -> x + y") 
             (Rel.NonTrivial (pars "True /\ (forall x. True)"));
       assert (term_eq (norm (List.hd us))
                       (norm (pars "fun x y -> x + y")))

   with Error(msg, r) -> print_string msg; print_newline()
    