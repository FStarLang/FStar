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
module VC

open FStar.Tactics

(* Testing that all VCs needed here are trivial by normalization/simplification *)
#set-options "--no_smt"

let test1 (#a: Type) (f: a -> Tac unit) (l: list a): Tac unit = ()

let test2 (#a: Type) (f: a -> Tac unit) (l: list a): Tac unit =
    match l with
    | [] -> fail ""
    | h::_ -> f h
    | _ -> fail "impossible" // needed, we don't do syntactic coverage checks

let test3 (#a: Type) (f: a -> Tac unit) (l: list a): Tac unit =
    begin match l with
    | [] -> fail ""
    | h::_ -> (f h ; f h ; f h)
    | _ -> fail "impossible" // needed, we don't do syntactic coverage checks

    end;
    dump ""

let tau b tm : Tac term =
    let tm = norm_term [] tm in
    let tm = norm_term [] tm in
    let tm = norm_term [] tm in
    let tm = norm_term [] tm in
    let tm = norm_term [] tm in
    let tm = norm_term [] tm in
    match inspect (quote b) with
    | Tv_App l r -> tm
    | Tv_Type _ -> tm
    | Tv_AscribedT _ _ None -> tm
    | _ -> tm
