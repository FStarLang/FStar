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
    Printf.printf "Expected guard %s;\n\
                   Got guard      %s\n" (guard_to_string g') (guard_to_string g);
    match g, g' with 
    | Rel.Trivial, Rel.Trivial -> true
    | Rel.NonTrivial f, Rel.NonTrivial f' ->
      
     term_eq f f'
    | _ -> false

let unify x y g' = 
    let g = Rel.teq Env.dummy x y |> Rel.solve_deferred_constraints Env.dummy in
//  assert (Rel.is_trivial g);
    assert (guard_eq g.guard_f g');
    Printf.printf "%s and %s are unifiable with guard %s\n"  (P.term_to_string x) (P.term_to_string y) (guard_to_string g.guard_f)

let should_fail x y =
    try 
        let g = Rel.teq Env.dummy x y |> Rel.solve_deferred_constraints Env.dummy in
        match g.guard_f with  
            | Rel.Trivial -> failwith (Printf.sprintf "%s and %s should not be unifiable\n" (P.term_to_string x) (P.term_to_string y))
            | Rel.NonTrivial f -> Printf.printf "%s and %s are unifiable if %s\n"  (P.term_to_string x) (P.term_to_string y) (P.term_to_string f)
    with Error(msg, r) -> print_string msg; print_newline()
    
let run_all debug = 
//    unify x x;
//    should_fail x y;
//    unify x (app id [x]);
//    unify id id;
    Options.debug := ["dummy"];
    Options.debug_level := [Options.Other "Rel"];
    unify id id' (Rel.NonTrivial (pars "True /\ (forall x. True)"))