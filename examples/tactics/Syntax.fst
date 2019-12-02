(*
   Copyright 2008-2018 Microsoft Research

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
module Syntax

open FStar.Tactics
open FStar.Reflection.Arith

let quote_sanity_check =
    assert True
        by (let t = quote (1+1) in
            match inspect t with
            | Tv_App _ _ -> ()
            | _ -> fail ("oops!: " ^ term_to_string t))

let goal_sanity_check =
    assert (True /\ True)
        by (let g = cur_goal () in
            match term_as_formula g with
            | And _ _ -> ()
            | _ -> fail ("oops!: " ^ term_to_string g))

let test1 = 24

let test2 = assert True
                by (let x = quote test1 in
                    match inspect x with
                    | Tv_FVar fv -> ()
                    | _ -> fail "wat")


let rec blah (t : term) : Tac term =
    let tv = match inspect t with
             | Tv_Var b -> Tv_Var b
             | Tv_FVar f -> Tv_FVar f
             | Tv_BVar f -> Tv_BVar f
             | Tv_App l (r, q) -> let l = blah l in
                                  let r = blah r in
                                  Tv_App l (r, q)
             | Tv_Abs b t -> let t = blah t in
                             Tv_Abs b t
             | Tv_Arrow b t -> Tv_Arrow b t
             | Tv_Refine b t -> let t = blah t in
                                Tv_Refine b t
             | Tv_Type u -> Tv_Type ()
             | Tv_Const c -> Tv_Const c
             | Tv_Uvar u t -> Tv_Uvar u t
             | Tv_Let r attrs b t1 t2 -> Tv_Let r attrs b t1 t2
             | Tv_Match t brs -> Tv_Match t brs
             | Tv_AscribedT e t tac -> Tv_AscribedT e t tac
             | Tv_AscribedC e c tac -> Tv_AscribedC e c tac
             | Tv_Unknown -> Tv_Unknown
    in pack tv

let _ = assert True
            by (let t = quote (1+1) in
                let t' = blah t in
                if term_eq t t'
                then ()
                else fail "blah not an identity?")

let _ = assert True
            by (let t = `(x:int{x > 0}) in
                let s = `(x:int{x > 0}) in
                if term_eq s t
                then ()
                else fail "wat")

let _ = assert True
            by (let t = quote blah in
                match inspect t with
                | Tv_FVar _ -> ()
                | _ -> fail "Free variable did not return an FV")

let _ = assert True
            by (let t = quote (5 == 2 + 3) in
                match term_as_formula' t with
                | Comp (Eq _) _ _ -> ()
                | f -> fail ("term_as_formula did not recognize an equality: " ^ formula_to_string f))

let _ = assert True
            by (let t = quote ((fun (x:int) -> x) 5) in
                match inspect t with
                | Tv_App _ _ -> ()
                | Tv_Const (C_Int 5) -> fail "Quoted term got reduced!"
                | _ -> fail "What?")

open FStar.Tactics

let arith_test1 =
    assert True
        by (let t = quote (1 + 2) in
            match run_tm (is_arith_expr t) with
            | Inr (Plus (Lit 1) (Lit 2)) -> debug "alright!"
            | Inl s -> fail ("oops: " ^ s)
            | _ -> fail "different thing")

let arith_test2 (x : int) =
    assert True
        by (let t = quote (x + x) in
            match run_tm (is_arith_expr t) with
            | Inr (Plus (Atom 0 _) (Atom 0 _)) -> debug "alright!"
            | Inl s -> fail ("oops: " ^ s)
            | _ -> fail "different thing")

let _ = assert True
            by (let t = quote (let x = 2 in x + 6) in
                match inspect t with
                | Tv_Let r attrs bv t1 t2 -> (
                   debug ("r = " ^ (if r then "true" else "false"));
                   debug ("bv = " ^ bv_to_string bv);
                   debug ("t1 = " ^ term_to_string t1);
                   debug ("t2 = " ^ term_to_string t2)
                   )
                | _ -> fail "wat?")

let _ = assert True
            by (let t = quote (let rec f x = if (x <= 0) then 1 else f (x - 1) in f 5) in
                match inspect t with
                | Tv_Let r attrs bv t1 t2 -> (
                   debug ("r = " ^ (if r then "true" else "false"));
                   debug ("bv = " ^ bv_to_string bv);
                   debug ("t1 = " ^ term_to_string t1);
                   debug ("t2 = " ^ term_to_string t2)
                   )
                | _ -> fail "wat?")
