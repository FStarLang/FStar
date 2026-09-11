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
module FStarC.Tests.Util

open FStarC
open FStarC.Effect
open FStarC.Errors
open FStarC.Syntax
open FStarC.Syntax.Syntax

module S = FStarC.Syntax.Syntax
module U = FStarC.Syntax.Util
module SS = FStarC.Syntax.Subst
module I = FStarC.Ident
module UF = FStarC.Syntax.Unionfind
module Const = FStarC.Parser.Const
module BU = FStarC.Util

open FStarC.Ident
open FStarC.Range
open FStarC.Class.Tagged
open FStarC.Class.Show
open FStarC.Syntax.Print {}

let always (id : int) b : ML unit =
    if b
    then ()
    else raise_error0 Errors.Fatal_AssertionFailure (Format.fmt1 "Assertion failed: test %s" (show id))

let x = gen_bv "x" None S.tun
let y = gen_bv "y" None S.tun
let n = gen_bv "n" None S.tun
let h = gen_bv "h" None S.tun
let m = gen_bv "m" None S.tun
let tm t = mk t dummyRange
let nm x = bv_to_name x
let app x ts = S.mk_Tm_app x (List.map as_arg ts) dummyRange

let rec term_eq' t1 t2 : ML bool =
    let t1 = SS.compress t1 in
    let t2 = SS.compress t2 in
    let binders_eq xs ys =
        List.length xs = List.length ys
        && List.forall2 (fun (x:binder) (y:binder) -> term_eq' x.binder_bv.sort y.binder_bv.sort) xs ys in
    let args_eq xs ys =
         List.length xs = List.length ys
         && List.forall2 (fun (a, imp) (b, imp') -> term_eq' a b && U.eq_aqual imp imp') xs ys in
    let comp_eq (c:S.comp) (d:S.comp) =
        match c.n, d.n with
            | S.Comp ct1, S.Comp ct2 ->
              I.lid_equals ct1.effect_name ct2.effect_name
              && term_eq' ct1.result_typ ct2.result_typ

            | _ -> false in
    match t1.n, t2.n with
      | Tm_lazy l, _ -> term_eq' (Option.must !lazy_chooser l.lkind l) t2
      | _, Tm_lazy l -> term_eq' t1 (Option.must !lazy_chooser l.lkind l)
      | Tm_bvar x, Tm_bvar y -> x.index = y.index
      | Tm_name x, Tm_name y -> S.bv_eq x y
      | Tm_fvar f, Tm_fvar g -> S.fv_eq f g
      | Tm_uinst (t, _), Tm_uinst(s, _) -> term_eq' t s
      | Tm_constant c1, Tm_constant c2 -> FStarC.Const.eq_const c1 c2
      | Tm_type u, Tm_type v -> u=v
      | Tm_abs _, Tm_abs _ ->
        let xs, t, _ = U.abs_formals_ln t1 in
        let ys, u, _ = U.abs_formals_ln t2 in
        let nx, ny = List.length xs, List.length ys in
        if nx = ny
        then binders_eq xs ys && term_eq' t u
        else if nx > ny
        then let xs0, xs' = BU.first_N ny xs in
             binders_eq xs0 ys && term_eq' (U.abs_ln xs' t None) u
        else let ys0, ys' = BU.first_N nx ys in
             binders_eq xs ys0 && term_eq' t (U.abs_ln ys' u None)
      | Tm_arrow _, Tm_arrow _ ->
        let xs, c = U.arrow_formals_comp_ln t1 in
        let ys, d = U.arrow_formals_comp_ln t2 in
        binders_eq xs ys && comp_eq c d
      | Tm_refine {b=x; phi=t}, Tm_refine {b=y; phi=u} -> term_eq' x.sort y.sort && term_eq' t u
      | Tm_app _, Tm_app _ ->
        let hd1, args1 = U.head_and_args_full t1 in
        let hd2, args2 = U.head_and_args_full t2 in
        //Unification produces equality applications that may have unconstrained implicit arguments
        (match (SS.compress hd1).n, args1, (SS.compress hd2).n, args2 with
         | Tm_fvar fv_eq_1, [(_, Some ({ aqual_implicit = true })); a1; a2],
           Tm_fvar fv_eq_2, [(_, Some ({ aqual_implicit = true })); b1; b2]
             when S.fv_eq_lid fv_eq_1 Const.eq2_lid
               && S.fv_eq_lid fv_eq_2 Const.eq2_lid ->
           args_eq [a1;a2] [b1;b2]
         | _ -> term_eq' hd1 hd2 && args_eq args1 args2)
      | Tm_match {scrutinee=t; ret_opt=None; brs=pats},
        Tm_match {scrutinee=t'; ret_opt=None; brs=pats'} ->
        List.length pats = List.length pats'
        && List.forall2 (fun (_, _, e) (_, _, e') -> term_eq' e e') pats pats'
        && term_eq' t t'
      | Tm_ascribed {tm=t1; asc=(Inl t2, _, _)},
        Tm_ascribed {tm=s1; asc=(Inl s2, _, _)} ->
        term_eq' t1 s1 && term_eq' t2 s2
      | Tm_let {lbs=(is_rec, lbs); body=t},
        Tm_let {lbs=(is_rec',lbs'); body=s} when is_rec=is_rec' ->
        List.length lbs = List.length lbs'
        && List.forall2 (fun lb1 lb2 -> term_eq' lb1.lbtyp lb2.lbtyp && term_eq' lb1.lbdef lb2.lbdef) lbs lbs'
        && term_eq' t s
      | Tm_uvar (u,_), Tm_uvar (u',_) -> UF.equiv u.ctx_uvar_head u'.ctx_uvar_head
      | Tm_meta {tm=t1}, _ -> term_eq' t1 t2
      | _, Tm_meta {tm=t2} -> term_eq' t1 t2

      | Tm_delayed _, _
      | _, Tm_delayed _ ->
        failwith (Format.fmt2 "Impossible: %s and %s" (tag_of t1) (tag_of t2))

      | Tm_unknown, Tm_unknown -> true
      | _ -> false

let term_eq t1 t2 : ML bool =
//    Format.print2 "Comparing %s and\n\t%s\n" (show t1) (show t2);
    let b = term_eq' t1 t2 in
    if not b then (
      Format.print2 ">>>>>>>>>>>Term %s is not equal to %s\n" (show t1) (show t2)
    );
    b
