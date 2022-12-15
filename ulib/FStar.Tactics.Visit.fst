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
module FStar.Tactics.Visit

(* Visit a term and transform it step by step. *)

open FStar.Reflection
open FStar.Tactics.Effect
open FStar.Tactics.Types
open FStar.Tactics.Util

let on_sort_bv (f : term -> Tac term) (xbv:bv) : Tac bv =
  let bvv = inspect_bv xbv in
  let bvv = { bvv with bv_sort = f bvv.bv_sort } in
  let bv = pack_bv bvv in
  bv

let on_sort_binder (f : term -> Tac term) (b:binder) : Tac binder =
  let bv, (q, attrs) = inspect_binder b in
  let bv = on_sort_bv f bv in
  let b = pack_binder bv q attrs in
  b

let rec visit_tm (ff : term -> Tac term) (t : term) : Tac term =
  let tv = inspect_ln t in
  let tv' =
    match tv with
    | Tv_FVar _
    | Tv_UInst _ _ -> tv
    | Tv_Var bv ->
        let bv = on_sort_bv (visit_tm ff) bv in
        Tv_Var bv

    | Tv_BVar bv ->
        let bv = on_sort_bv (visit_tm ff) bv in
        Tv_BVar bv

    | Tv_Type u -> Tv_Type u
    | Tv_Const c -> Tv_Const c
    | Tv_Uvar i u -> Tv_Uvar i u
    | Tv_Unknown -> Tv_Unknown
    | Tv_Arrow b c ->
        let b = on_sort_binder (visit_tm ff) b in
        let c = visit_comp ff c in
        Tv_Arrow b c
    | Tv_Abs b t ->
        let b = on_sort_binder (visit_tm ff) b in
        let t = visit_tm ff t in
        Tv_Abs b t
    | Tv_App l (r, q) ->
         let l = visit_tm ff l in
         let r = visit_tm ff r in
         Tv_App l (r, q)
    | Tv_Refine b r ->
        let b = on_sort_bv (visit_tm ff) b in
        let r = visit_tm ff r in
        Tv_Refine b r
    | Tv_Let r attrs b def t ->
        let b = on_sort_bv (visit_tm ff) b in
        let def = visit_tm ff def in
        let t = visit_tm ff t in
        Tv_Let r attrs b def t
    | Tv_Match sc ret_opt brs ->
        let sc = visit_tm ff sc in
        let ret_opt = map_opt (fun (b, asc) ->
          let b = on_sort_binder (visit_tm ff) b in
          let asc =
            match asc with
            | Inl t, tacopt, use_eq ->
              Inl (visit_tm ff t), map_opt (visit_tm ff) tacopt, use_eq
            | Inr c, tacopt, use_eq->
              Inr (visit_comp ff c), map_opt (visit_tm ff) tacopt, use_eq in
          b, asc) ret_opt in
        let brs = map (visit_br ff) brs in
        Tv_Match sc ret_opt brs
    | Tv_AscribedT e t topt use_eq ->
        let e = visit_tm ff e in
        let t = visit_tm ff t in
        Tv_AscribedT e t topt use_eq
    | Tv_AscribedC e c topt use_eq ->
        let e = visit_tm ff e in
        Tv_AscribedC e c topt use_eq
  in
  ff (pack_ln tv')
and visit_br (ff : term -> Tac term) (b:branch) : Tac branch =
  let (p, t) = b in
  let p = visit_pat ff p in
  let t = visit_tm ff t in
  (p, t)
and visit_pat (ff : term -> Tac term) (p:pattern) : Tac pattern =
  match p with
  | Pat_Constant c -> p
  | Pat_Cons fv us l ->
      let l = (map (fun(p,b) -> (visit_pat ff p, b)) l) in
      Pat_Cons fv us l
  | Pat_Var bv ->
      let bv = on_sort_bv (visit_tm ff) bv in
      Pat_Var bv
  | Pat_Wild bv ->
      let bv = on_sort_bv (visit_tm ff) bv in
      Pat_Wild bv
  | Pat_Dot_Term eopt ->
      Pat_Dot_Term (map_opt (visit_tm ff) eopt)
and visit_comp (ff : term -> Tac term) (c : comp) : Tac comp =
  let cv = inspect_comp c in
  let cv' =
    match cv with
    | C_Total ret ->
        let ret = visit_tm ff ret in
        C_Total ret

    | C_GTotal ret ->
        let ret = visit_tm ff ret in
        C_GTotal ret

    | C_Lemma pre post pats ->
        let pre = visit_tm ff pre in
        let post = visit_tm ff post in
        let pats = visit_tm ff pats in
        C_Lemma pre post pats

    | C_Eff us eff res args decrs ->
        let res = visit_tm ff res in
        let args = map (fun (a, q) -> (visit_tm ff a, q)) args in
        let decrs = map (visit_tm ff) decrs in
        C_Eff us eff res args decrs
  in
  pack_comp cv'
