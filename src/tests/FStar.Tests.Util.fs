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
﻿#light "off"
module FStar.Tests.Util

open FStar
open FStar.All
open FStar.Errors
open FStar.Util
open FStar.Syntax
open FStar.Syntax.Syntax
module S = FStar.Syntax.Syntax
module U = FStar.Syntax.Util
module SS = FStar.Syntax.Subst
module I = FStar.Ident
module UF = FStar.Syntax.Unionfind
module Const = FStar.Parser.Const
module BU = FStar.Util

open FStar.Ident
open FStar.Range

let always id b =
    if b
    then ()
    else raise_error (Errors.Fatal_AssertionFailure, BU.format1 "Assertion failed: test %s" (BU.string_of_int id)) Range.dummyRange

let x = gen_bv "x" None S.tun
let y = gen_bv "y" None S.tun
let n = gen_bv "n" None S.tun
let h = gen_bv "h" None S.tun
let m = gen_bv "m" None S.tun
let tm t = mk t None dummyRange
let nm x = bv_to_name x
let app x ts = mk (Tm_app(x, List.map as_arg ts)) None dummyRange

let rec term_eq' t1 t2 =
    let t1 = SS.compress t1 in
    let t2 = SS.compress t2 in
    let binders_eq xs ys =
        List.length xs = List.length ys
        && List.forall2 (fun ((x, _):binder) ((y, _):binder) -> term_eq' x.sort y.sort) xs ys in
    let args_eq xs ys =
         List.length xs = List.length ys
         && List.forall2 (fun (a, imp) (b, imp') -> term_eq' a b && U.eq_aqual imp imp'=U.Equal) xs ys in
    let comp_eq (c:S.comp) (d:S.comp) =
        match c.n, d.n with
            | S.Total (t, _), S.Total (s, _) -> term_eq' t s
            | S.Comp ct1, S.Comp ct2 ->
              I.lid_equals ct1.effect_name ct2.effect_name
              && term_eq' ct1.result_typ ct2.result_typ
              && args_eq ct1.effect_args ct2.effect_args
            | _ -> false in
    match t1.n, t2.n with
      | Tm_lazy l, _ -> term_eq' (must !lazy_chooser l.lkind l) t2
      | _, Tm_lazy l -> term_eq' t1 (must !lazy_chooser l.lkind l)
      | Tm_bvar x, Tm_bvar y -> x.index = y.index
      | Tm_name x, Tm_name y -> S.bv_eq x y
      | Tm_fvar f, Tm_fvar g -> S.fv_eq f g
      | Tm_uinst (t, _), Tm_uinst(s, _) -> term_eq' t s
      | Tm_constant c1, Tm_constant c2 -> FStar.Const.eq_const c1 c2
      | Tm_type u, Tm_type v -> u=v
      | Tm_abs(xs, t, _), Tm_abs(ys, u, _) when (List.length xs = List.length ys) -> binders_eq xs ys && term_eq' t u
      | Tm_abs(xs, t, _), Tm_abs(ys, u, _) ->
        if List.length xs > List.length ys
        then let xs, xs' = BU.first_N (List.length ys) xs in
             let t1 = mk (Tm_abs(xs, mk (Tm_abs(xs', t, None)) None t1.pos, None)) None t1.pos in
             term_eq' t1 t2
        else let ys, ys' = BU.first_N (List.length xs) ys in
             let t2 = mk (Tm_abs(ys, mk (Tm_abs(ys', u, None)) None t2.pos, None)) None t2.pos in
             term_eq' t1 t2
      | Tm_arrow(xs, c), Tm_arrow(ys, d) -> binders_eq xs ys && comp_eq c d
      | Tm_refine(x, t), Tm_refine(y, u) -> term_eq' x.sort y.sort && term_eq' t u
      | Tm_app({n=Tm_fvar fv_eq_1}, [(_, Some (Implicit _)); t1; t2]),
        Tm_app({n=Tm_fvar fv_eq_2}, [(_, Some (Implicit _)); s1; s2])
            when S.fv_eq_lid fv_eq_1 Const.eq2_lid
              && S.fv_eq_lid fv_eq_2 Const.eq2_lid -> //Unification produces equality applications that may have unconstrainted implicit arguments
        args_eq [s1;s2] [t1;t2]
      | Tm_app(t, args), Tm_app(s, args') -> term_eq' t s && args_eq args args'
      | Tm_match(t, pats), Tm_match(t', pats') ->
        List.length pats = List.length pats'
        && List.forall2 (fun (_, _, e) (_, _, e') -> term_eq' e e') pats pats'
        && term_eq' t t'
      | Tm_ascribed(t1, (Inl t2, _), _), Tm_ascribed(s1, (Inl s2, _), _) ->
        term_eq' t1 s1 && term_eq' t2 s2
      | Tm_let((is_rec, lbs), t), Tm_let((is_rec',lbs'), s) when is_rec=is_rec' ->
        List.length lbs = List.length lbs'
        && List.forall2 (fun lb1 lb2 -> term_eq' lb1.lbtyp lb2.lbtyp && term_eq' lb1.lbdef lb2.lbdef) lbs lbs'
        && term_eq' t s
      | Tm_uvar (u,_), Tm_uvar (u',_) -> UF.equiv u.ctx_uvar_head u'.ctx_uvar_head
      | Tm_meta(t1, _), _ -> term_eq' t1 t2
      | _, Tm_meta(t2, _) -> term_eq' t1 t2

      | Tm_delayed _, _
      | _, Tm_delayed _ ->
        failwith (BU.format2 "Impossible: %s and %s" (Print.tag_of_term t1) (Print.tag_of_term t2))

      | Tm_unknown, Tm_unknown -> true
      | _ -> false

let term_eq t1 t2 =
//    BU.print2 "Comparing %s and\n\t%s\n" (Print.term_to_string t1) (Print.term_to_string t2);
    let b = term_eq' t1 t2 in
    if not b then BU.print2 ">>>>>>>>>>>Term %s is not equal to %s\n" (Print.term_to_string t1) (Print.term_to_string t2);
    b
