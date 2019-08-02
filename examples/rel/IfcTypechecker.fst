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
module IfcTypechecker

open WhileReify
open IfcRulesReify
open FStar.DM4F.Exceptions

(* Typechecking expressions: we infer the label *)
val tc_exp : env:label_fun -> e:exp -> Pure label (requires True) (ensures ni_exp env e)
let rec tc_exp env e =
  match e with
  | AInt i -> aint_exp env i ; Low
  | AVar r -> avar_exp env r ; env r
  | AOp o e1 e2 ->
    let l1 = tc_exp env e1 in
    let l2 = tc_exp env e2 in
    let l = join l1 l2 in
    sub_exp env e1 l1 l ; sub_exp env e2 l2 l ; binop_exp env o e1 e2 l ; l


(* TODO : refine this exception to have some interesting typechecking-error reporting *)
exception Not_well_typed

#set-options "--z3rlimit 30"

(* Typechecking commands: we typecheck in a given context *)
 val tc_com : env:label_fun -> c:com -> Exn label (requires True)
    (ensures fun ol -> Inl? ol ==> ni_com env c (Inl?.v ol))
    (decreases c)
 let rec tc_com env c =
  match c with

  | Skip -> skip_com env ; High

  | Assign r e ->
    let le = tc_exp env e in
    let lr = env r in
    if not (le <= lr) then raise Not_well_typed ;
    sub_exp env e le lr ;
    assign_com env e r ;
    lr

  | Seq c1 c2 ->
    let l1 = tc_com env c1 in
    let l2 = tc_com env c2 in
    let l = meet l1 l2 in
    sub_com env c1 l1 l ;
    sub_com env c2 l2 l ;
    seq_com env c1 c2 l ;
    l

  | If e ct cf ->
    let le = tc_exp env e in
    let lt = tc_com env ct in
    let lf = tc_com env cf in
    if not (le <= lt && le <= lf) then raise Not_well_typed ;
    let l = meet lt lf in
    universal_property_meet le lt lf ;
    sub_exp env e le l ;
    sub_com env ct lt l ;
    sub_com env cf lf l ;
    cond_com env e ct cf l ;
    l

  | While e c v ->
    let le = tc_exp env e in
    let lc = tc_com env c in
    if not (le <= lc) then raise Not_well_typed ;
    sub_exp env e le lc ;
    while_com env e c v lc ;
    lc

open FStar.List

 val tc_com_hybrid : env:label_fun -> c:com -> list (cl:(com*label){ni_com env (fst cl) (snd cl)}) ->
  Exn label (requires True) (ensures fun ol -> Inl? ol ==> ni_com env c (Inl?.v ol))
    (decreases c)
 let rec tc_com_hybrid env c cls =
  match find #(cl:(com*label){ni_com env (fst cl) (snd cl)})
             (fun cl -> fst cl = c) cls with
  | Some (_,l) -> l
  | None ->
  (* the rest is copied more or less verbatim from above *)
  begin
  match c with

  | Skip -> skip_com env ; High

  | Assign r e ->
    let le = tc_exp env e in
    let lr = env r in
    if not (le <= lr) then raise Not_well_typed ;
    sub_exp env e le lr ;
    assign_com env e r ;
    lr

  | Seq c1 c2 ->
    let l1 = tc_com_hybrid env c1 cls in
    let l2 = tc_com_hybrid env c2 cls in
    let l = meet l1 l2 in
    sub_com env c1 l1 l ;
    sub_com env c2 l2 l ;
    seq_com env c1 c2 l ;
    l

  | If e ct cf ->
    let le = tc_exp env e in
    let lt = tc_com_hybrid env ct cls in
    let lf = tc_com_hybrid env cf cls in
    if not (le <= lt && le <= lf) then raise Not_well_typed ;
    let l = meet lt lf in
    universal_property_meet le lt lf ;
    sub_exp env e le l ;
    sub_com env ct lt l ;
    sub_com env cf lf l ;
    cond_com env e ct cf l ;
    l

  | While e c v ->
    let le = tc_exp env e in
    let lc = tc_com_hybrid env c cls in
    if not (le <= lc) then raise Not_well_typed ;
    sub_exp env e le lc ;
    while_com env e c v lc ;
    lc
  end
