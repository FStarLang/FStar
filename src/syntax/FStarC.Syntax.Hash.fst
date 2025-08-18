(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or impliedmk_
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStarC.Syntax.Hash
open FStarC
open FStarC.Effect
open FStarC.Util
open FStarC.Syntax.Syntax
open FStarC.Const
module SS = FStarC.Syntax.Subst
module UU = FStarC.Syntax.Unionfind
module BU = FStarC.Util

(* maybe memo *)
let mm (t:Type) = bool -> t & bool

let (let?) (f:mm 't) (g: 't -> mm 's) : mm 's =
  fun b ->
    let t, b = f b in
    g t b

let ret (x:'t) : mm 't = fun b -> x, b

let should_memo : mm bool = fun b -> b, b

let no_memo : mm unit = fun _ -> (), false

module H = FStarC.Hash

let maybe_memoize (h:syntax 'a) (f:syntax 'a -> mm H.hash_code) : mm H.hash_code =
  fun should_memo ->
    if should_memo
    then (
      match !h.hash_code with
      | Some c -> c, should_memo
      | None ->
        let c, should_memo = f h should_memo in
        if should_memo
        then h.hash_code := Some c;
        c, should_memo
    )
    else f h should_memo

let of_int (i:int) : mm H.hash_code = ret (H.of_int i)

let of_string (s:string) : mm H.hash_code = ret (H.of_string s)

let mix (f:mm H.hash_code) (g:mm H.hash_code) : mm H.hash_code =
  fun b -> let x, b0 = f b in
        let y, b1 = g b in
        H.mix x y, b0 && b1

let nil_hc : mm H.hash_code = of_int 1229
let cons_hc : mm H.hash_code = of_int 1231

let mix_list (l:list (mm H.hash_code)) : mm H.hash_code =
  List.fold_right mix l nil_hc

let mix_list_lit = mix_list

let hash_list (h:'a -> mm H.hash_code) (ts:list 'a) : mm H.hash_code = mix_list (List.map h ts)

let hash_option (h:'a -> mm H.hash_code) (o:option 'a) : mm H.hash_code =
  match o with
  | None -> ret (H.of_int 1237)
  | Some o -> mix (ret (H.of_int 1249)) (h o)

// hash the string.
let hash_doc (d : Pprint.document) : mm H.hash_code =
  of_string (Pprint.pretty_string (float_of_string "1.0") 80 d)

let hash_doc_list (ds : list Pprint.document) : mm H.hash_code =
  hash_list hash_doc ds

let hash_pair (h:'a -> mm H.hash_code) (i:'b -> mm H.hash_code) (x:('a & 'b))
  : mm H.hash_code
  = mix (h (fst x)) (i (snd x))

let rec hash_term (t:term)
  : mm H.hash_code
  = maybe_memoize t hash_term'

and hash_comp c
  : mm H.hash_code
  = maybe_memoize c hash_comp'

and hash_term' (t:term)
  : mm H.hash_code
  = // if Debug.any ()
    // then FStarC.Util.print1 "Hash_term %s\n" (FStarC.Syntax.show t);
    match (SS.compress t).n with
    | Tm_bvar bv -> mix (of_int 3) (of_int bv.index)
    | Tm_name bv -> mix (of_int 5) (of_int bv.index)
    | Tm_fvar fv -> mix (of_int 7) (hash_fv fv)
    | Tm_uinst(t, us) -> mix (of_int 11)
                                   (mix (hash_term t)
                                               (hash_list hash_universe us))
    | Tm_constant sc -> mix (of_int 13) (hash_constant sc)
    | Tm_type u -> mix (of_int 17) (hash_universe u)
    | Tm_abs {bs; body=t; rc_opt=rcopt} -> mix (of_int 19)
                                        (mix (hash_list hash_binder bs)
                                                    (mix (hash_term t)
                                                                (hash_option hash_rc rcopt)))
    | Tm_arrow {bs; comp=c} -> mix (of_int 23) (mix (hash_list hash_binder bs) (hash_comp c))
    | Tm_refine {b; phi=t} -> mix (of_int 29) (mix (hash_bv b) (hash_term t))
    | Tm_app {hd=t; args} -> mix (of_int 31) (mix (hash_term t) (hash_list hash_arg args))
    | Tm_match {scrutinee=t; ret_opt=asc_opt; brs=branches; rc_opt=rcopt} ->
      mix (of_int 37)
            (mix (hash_option hash_match_returns asc_opt)
                   (mix (mix (hash_term t) (hash_list hash_branch branches))
                          (hash_option hash_rc rcopt)))
    | Tm_ascribed {tm=t; asc=a; eff_opt=lopt} -> mix (of_int 43) (mix (hash_term t) (mix (hash_ascription a) (hash_option hash_lid lopt)))
    | Tm_let {lbs=(false, [lb]); body=t} -> mix (of_int 47) (mix (hash_lb lb) (hash_term t))
    | Tm_let {lbs=(_, lbs); body=t} -> mix (of_int 51) (mix (hash_list hash_lb lbs) (hash_term t))
    | Tm_uvar uv -> mix (of_int 53) (hash_uvar uv)
    | Tm_meta {tm=t; meta=m} -> mix (of_int 61) (mix (hash_term t) (hash_meta m))
    | Tm_lazy li -> mix (of_int 67) (hash_lazyinfo li)
    | Tm_quoted (t, qi) -> mix (of_int 71) (mix (hash_term t) (hash_quoteinfo qi))
    | Tm_unknown -> of_int 73
    | Tm_delayed _ -> failwith "Impossible"

and hash_comp' (c:comp)
  : mm H.hash_code
  = match c.n with
    | Total t ->
      mix_list_lit
        [of_int 811;
         hash_term t]
    | GTotal t ->
      mix_list_lit
        [of_int 821;
         hash_term t]
    | Comp ct ->
      mix_list_lit
        [of_int 823;
         hash_list hash_universe ct.comp_univs;
         hash_lid ct.effect_name;
         hash_term ct.result_typ;
         hash_list hash_arg ct.effect_args;
         hash_list hash_flag ct.flags]

and hash_lb lb =
  mix_list_lit
    [ of_int 79;
      hash_lbname lb.lbname;
      hash_list hash_ident lb.lbunivs;
      hash_term lb.lbtyp;
      hash_lid lb.lbeff;
      hash_term lb.lbdef;
      hash_list hash_term lb.lbattrs]

and hash_match_returns (b, asc) =
  mix (hash_binder b)
      (hash_ascription asc)

and hash_branch b =
  let p, topt, t = b in
  mix_list_lit
    [of_int 83;
     hash_pat p;
     hash_option hash_term topt;
     hash_term t]

and hash_pat p =
  match p.v with
  | Pat_constant c -> mix (of_int 89) (hash_constant c)
  | Pat_cons(fv, us, args) ->
    mix_list_lit
      [of_int 97;
       hash_fv fv;
       hash_option (hash_list hash_universe) us;
       hash_list (hash_pair hash_pat hash_bool) args]
  | Pat_var bv -> mix (of_int 101) (hash_bv bv)
  | Pat_dot_term t -> mix_list_lit [of_int 107; hash_option hash_term t]


and hash_bv b = hash_term b.sort
and hash_fv fv = of_string (Ident.string_of_lid fv.fv_name)
and hash_binder (b:binder) =
  mix_list_lit
    [hash_bv b.binder_bv;
     hash_option hash_bqual b.binder_qual;
     hash_list hash_term b.binder_attrs]

and hash_universe =
  function
  | U_zero -> of_int 179
  | U_succ u -> mix (of_int 181) (hash_universe u)
  | U_max us -> mix (of_int 191) (hash_list hash_universe us)
  | U_bvar i -> mix (of_int 193) (of_int i)
  | U_name i -> mix (of_int 197) (hash_ident i)
  | U_unif uv -> mix (of_int 199) (hash_universe_uvar uv)
  | U_unknown -> of_int 211

and hash_arg (t, aq) =
  mix (hash_term t) (hash_option hash_arg_qualifier aq)

and hash_arg_qualifier aq =
  mix (hash_bool aq.aqual_implicit)
        (hash_list hash_term aq.aqual_attributes)

and hash_bqual =
  function
  | Implicit true -> of_int 419
  | Implicit false -> of_int 421
  | Meta t -> mix (of_int 431) (hash_term t)
  | Equality -> of_int 433

and hash_uvar (u, _) = of_int (UU.uvar_id u.ctx_uvar_head)

and hash_universe_uvar u = of_int (UU.univ_uvar_id u)

and hash_ascription (a, to, b) =
  mix
    (match a with
    | Inl t -> hash_term t
    | Inr c -> hash_comp c)
    (hash_option hash_term to)

and hash_bool b =
  if b then of_int 307
  else of_int 311

and hash_constant =
  function
  | Const_effect -> of_int 283
  | Const_unit -> of_int 293
  | Const_bool b -> hash_bool b
  | Const_int (s, o) -> mix (of_int 313)
                             (mix (of_string s)
                                    (hash_option hash_sw o))
  | Const_char c -> mix (of_int 317) (of_int (FStar.Char.int_of_char c))
  | Const_real s -> mix (of_int 337) (of_string s)
  | Const_string (s, _) -> mix (of_int 349) (of_string s)
  | Const_range_of -> of_int 353
  | Const_set_range_of -> of_int 359
  | Const_range r -> mix (of_int 367) (of_string (Range.string_of_range r))
  | Const_reify _ -> of_int 367
  | Const_reflect l -> mix (of_int 373) (hash_lid l)

and hash_sw (s, w) =
  mix
  (match s with
   | Unsigned -> of_int 547
   | Signed -> of_int 557)
  (match w with
   | Int8 -> of_int 563
   | Int16 -> of_int 569
   | Int32 -> of_int 571
   | Int64 -> of_int 577
   | Sizet -> of_int 583)

and hash_ident i = of_string (Ident.string_of_id i)
and hash_lid l = of_string (Ident.string_of_lid l)
and hash_lbname l =
  match l with
  | Inl bv -> hash_bv bv
  | Inr fv -> hash_fv fv
and hash_rc rc =
  mix_list_lit
    [ hash_lid rc.residual_effect;
      hash_option hash_term rc.residual_typ;
      hash_list hash_flag rc.residual_flags ]

and hash_flag =
  function
  | TOTAL -> of_int 947
  | MLEFFECT -> of_int 953
  | LEMMA -> of_int 967
  | RETURN -> of_int 971
  | PARTIAL_RETURN -> of_int 977
  | SOMETRIVIAL -> of_int 983
  | TRIVIAL_POSTCONDITION -> of_int 991
  | SHOULD_NOT_INLINE -> of_int 997
  | CPS -> of_int 1009
  | DECREASES (Decreases_lex ts) -> mix (of_int 1013) (hash_list hash_term ts)
  | DECREASES (Decreases_wf (t0, t1)) -> mix (of_int 2341) (hash_list hash_term [t0;t1])

and hash_meta m =
  match m with
  | Meta_pattern (ts, args) ->
    mix_list_lit
      [ of_int 1019;
        hash_list hash_term ts;
        hash_list (hash_list hash_arg) args ]
  | Meta_named l ->
    mix_list_lit
      [ of_int 1021;
        hash_lid l ]
  | Meta_labeled (s, r, _) ->
    mix_list_lit
      [ of_int 1031;
        hash_doc_list s;
        of_string (Range.string_of_range r) ]
  | Meta_desugared msi ->
    mix_list_lit
      [ of_int 1033;
        hash_meta_source_info msi ]
  | Meta_monadic(m, t) ->
    mix_list_lit
      [ of_int 1039;
        hash_lid m;
        hash_term t ]
  | Meta_monadic_lift (m0, m1, t) ->
    mix_list_lit
      [of_int 1069;
       hash_lid m0;
       hash_lid m1;
       hash_term t]

and hash_meta_source_info m =
   match m with
   | Sequence -> of_int 1049
   | Primop -> of_int 1051
   | Masked_effect -> of_int 1061
   | Meta_smt_pat -> of_int 1063
   | Machine_integer sw -> mix (of_int 1069) (hash_sw sw)

and hash_lazyinfo li = of_int 0 //no meaningful way to hash the blob

and hash_quoteinfo qi =
  mix
    (hash_bool (qi.qkind = Quote_static))
    (hash_list hash_term (snd qi.antiquotations))

////////////////////////////////////////////////////////////////////////////////
let rec equal_list f l1 l2 =
  match l1, l2 with
  | [], [] -> true
  | h1::t1, h2::t2 -> f h1 h2 && equal_list f t1 t2
  | _ -> false

let equal_opt f o1 o2 =
  match o1, o2 with
  | None, None -> true
  | Some a, Some b -> f a b
  | _ -> false

let equal_pair f g (x1, y1) (x2, y2) = f x1 x2 && g y1 y2

let equal_poly x y = x=y

let ext_hash_term (t:term) = fst (hash_term t true)
let ext_hash_term_no_memo (t:term) = fst (hash_term t false)

let rec equal_term (t1 t2:term)
  : bool
  = if physical_equality t1 t2 then true else
    if physical_equality t1.n t2.n then true else
    if ext_hash_term t1 <> ext_hash_term t2 then false else
    match (SS.compress t1).n, (SS.compress t2).n with
    | Tm_bvar x, Tm_bvar y -> x.index = y.index
    | Tm_name x, Tm_name y -> x.index = y.index
    | Tm_fvar f, Tm_fvar g -> equal_fv f g
    | Tm_uinst (t1, u1), Tm_uinst (t2, u2) ->
      equal_term t1 t2 &&
      equal_list equal_universe u1 u2
    | Tm_constant c1, Tm_constant c2 -> equal_constant c1 c2
    | Tm_type u1, Tm_type u2 -> equal_universe u1 u2
    | Tm_abs {bs=bs1; body=t1; rc_opt=rc1}, Tm_abs {bs=bs2; body=t2; rc_opt=rc2} ->
      equal_list equal_binder bs1 bs2 &&
      equal_term t1 t2 &&
      equal_opt equal_rc rc1 rc2
    | Tm_arrow {bs=bs1; comp=c1}, Tm_arrow {bs=bs2; comp=c2} ->
      equal_list equal_binder bs1 bs2 &&
      equal_comp c1 c2
    | Tm_refine {b=b1; phi=t1}, Tm_refine {b=b2; phi=t2} ->
      equal_bv b1 b2 &&
      equal_term t1 t2
    | Tm_app {hd=t1; args=as1}, Tm_app {hd=t2; args=as2} ->
      equal_term t1 t2 &&
      equal_list equal_arg as1 as2
    | Tm_match {scrutinee=t1; ret_opt=asc_opt1; brs=bs1; rc_opt=ropt1},
      Tm_match {scrutinee=t2; ret_opt=asc_opt2; brs=bs2; rc_opt=ropt2} ->
      equal_term t1 t2 &&
      equal_opt equal_match_returns asc_opt1 asc_opt2 &&
      equal_list equal_branch bs1 bs2 &&
      equal_opt equal_rc ropt1 ropt2
    | Tm_ascribed {tm=t1; asc=a1; eff_opt=l1},
      Tm_ascribed {tm=t2; asc=a2; eff_opt=l2} ->
      equal_term t1 t2 &&
      equal_ascription a1 a2 &&
      equal_opt Ident.lid_equals l1 l2
    | Tm_let {lbs=(r1, lbs1); body=t1}, Tm_let {lbs=(r2, lbs2); body=t2} ->
      r1 = r2 &&
      equal_list equal_letbinding lbs1 lbs2 &&
      equal_term t1 t2
    | Tm_uvar u1, Tm_uvar u2 ->
      equal_uvar u1 u2
    | Tm_meta {tm=t1; meta=m1}, Tm_meta {tm=t2; meta=m2} ->
      equal_term t1 t2 &&
      equal_meta m1 m2
    | Tm_lazy l1, Tm_lazy l2 ->
      equal_lazyinfo l1 l2
    | Tm_quoted (t1, q1), Tm_quoted (t2, q2) ->
      equal_term t1 t2 &&
      equal_quoteinfo q1 q2
    | Tm_unknown, Tm_unknown ->
      true
    | _ -> false

and equal_comp c1 c2 =
  if physical_equality c1 c2 then true else
  match c1.n, c2.n with
  | Total t1, Total t2
  | GTotal t1, GTotal t2 ->
    equal_term t1 t2
  | Comp ct1, Comp ct2 ->
    Ident.lid_equals ct1.effect_name ct2.effect_name &&
    equal_list equal_universe ct1.comp_univs ct2.comp_univs &&
    equal_term ct1.result_typ ct2.result_typ &&
    equal_list equal_arg ct1.effect_args ct2.effect_args &&
    equal_list equal_flag ct1.flags ct2.flags
  | _ -> false

and equal_binder b1 b2 =
  if physical_equality b1 b2 then true else
  equal_bv b1.binder_bv b2.binder_bv &&
  equal_bqual b1.binder_qual b2.binder_qual &&
  equal_list equal_term b1.binder_attrs b2.binder_attrs

and equal_match_returns (b1, asc1) (b2, asc2) =
  equal_binder b1 b2 &&
  equal_ascription asc1 asc2

and equal_ascription x1 x2 =
  if physical_equality x1 x2 then true else
  let a1, t1, b1 = x1 in
  let a2, t2, b2 = x2 in
  (match a1, a2 with
   | Inl t1, Inl t2 -> equal_term t1 t2
   | Inr c1, Inr c2 -> equal_comp c1 c2
   | _ -> false) &&
  equal_opt equal_term t1 t2 &&
  b1 = b2

and equal_letbinding l1 l2 =
  if physical_equality l1 l2 then true else
  equal_lbname l1.lbname l2.lbname &&
  equal_list Ident.ident_equals l1.lbunivs l2.lbunivs &&
  equal_term l1.lbtyp l2.lbtyp &&
  Ident.lid_equals l1.lbeff l2.lbeff &&
  equal_term l1.lbdef l2.lbdef &&
  equal_list equal_term l1.lbattrs l2.lbattrs

and equal_uvar (u1, (s1, _)) (u2, (s2, _)) =
  UU.equiv u1.ctx_uvar_head u2.ctx_uvar_head &&
  equal_list (equal_list equal_subst_elt) s1 s2

and equal_bv b1 b2 =
  if physical_equality b1 b2 then true else
  Ident.ident_equals b1.ppname b2.ppname &&
  equal_term b1.sort b2.sort

and equal_fv f1 f2 =
  if physical_equality f1 f2 then true else
  Ident.lid_equals f1.fv_name f2.fv_name

and equal_universe u1 u2 =
  if physical_equality u1 u2 then true else
  match (SS.compress_univ u1), (SS.compress_univ u2) with
  | U_zero, U_zero -> true
  | U_succ u1, U_succ u2 -> equal_universe u1 u2
  | U_max us1, U_max us2 -> equal_list equal_universe us1 us2
  | U_bvar i1, U_bvar i2 -> i1 = i2
  | U_name x1, U_name x2 -> Ident.ident_equals x1 x2
  | U_unif u1, U_unif u2 -> UU.univ_equiv u1 u2
  | U_unknown, U_unknown -> true
  | _ -> false

and equal_constant c1 c2 =
  if physical_equality c1 c2 then true else
  match c1, c2 with
  | Const_effect, Const_effect
  | Const_unit, Const_unit -> true
  | Const_bool b1, Const_bool b2 -> b1 = b2
  | Const_int (s1, o1), Const_int(s2, o2) -> s1=s2 && o1=o2
  | Const_char c1, Const_char c2 -> c1=c2
  | Const_real s1, Const_real s2 -> s1=s2
  | Const_string (s1, _), Const_string (s2, _) -> s1=s2
  | Const_range_of, Const_range_of
  | Const_set_range_of, Const_set_range_of -> true
  | Const_range r1, Const_range r2 -> Range.compare r1 r2 = 0
  | Const_reify _, Const_reify _ -> true
  | Const_reflect l1, Const_reflect l2 -> Ident.lid_equals l1 l2
  | _ -> false

and equal_arg arg1 arg2 =
  if physical_equality arg1 arg2 then true else
  let t1, a1 = arg1 in
  let t2, a2 = arg2 in
  equal_term t1 t2 &&
  equal_opt equal_arg_qualifier a1 a2

and equal_bqual b1 b2 =
  equal_opt equal_binder_qualifier b1 b2

and equal_binder_qualifier b1 b2 =
  match b1, b2 with
  | Implicit b1, Implicit b2 -> b1 = b2
  | Equality, Equality -> true
  | Meta t1, Meta t2 -> equal_term t1 t2
  | _ -> false

and equal_branch (p1, w1, t1) (p2, w2, t2) =
  equal_pat p1 p2 &&
  equal_opt equal_term w1 w2 &&
  equal_term t1 t2

and equal_pat p1 p2 =
  if physical_equality p1 p2 then true else
  match p1.v, p2.v with
  | Pat_constant c1, Pat_constant c2 ->
    equal_constant c1 c2
  | Pat_cons(fv1, us1, args1), Pat_cons(fv2, us2, args2) ->
    equal_fv fv1 fv2 &&
    equal_opt (equal_list equal_universe) us1 us2 &&
    equal_list (equal_pair equal_pat equal_poly) args1 args2
  | Pat_var bv1, Pat_var bv2 ->
    equal_bv bv1 bv2
  | Pat_dot_term t1, Pat_dot_term t2 ->
    equal_opt equal_term t1 t2
  | _ -> false

and equal_meta m1 m2 =
  match m1, m2 with
  | Meta_pattern (ts1, args1), Meta_pattern (ts2, args2) ->
    equal_list equal_term ts1 ts2 &&
    equal_list (equal_list equal_arg) args1 args2
  | Meta_named l1, Meta_named l2  ->
    Ident.lid_equals l1 l2
  | Meta_labeled (s1, r1, _), Meta_labeled (s2, r2, _) ->
    s1 = s2 &&
    Range.compare r1 r2 = 0
  | Meta_desugared msi1, Meta_desugared msi2 ->
    msi1 = msi2
  | Meta_monadic(m1, t1), Meta_monadic(m2, t2) ->
    Ident.lid_equals m1 m2 &&
    equal_term t1 t2
  | Meta_monadic_lift (m1, n1, t1), Meta_monadic_lift (m2, n2, t2) ->
    Ident.lid_equals m1 m2 &&
    Ident.lid_equals n1 n2 &&
    equal_term t1 t2
  | _ -> false

and equal_lazyinfo l1 l2 =
  (* We cannot really compare the blobs. Just try physical
  equality (first matching kinds). *)
  l1.lkind = l1.lkind && BU.physical_equality l1.blob l2.blob

and equal_quoteinfo q1 q2 =
  q1.qkind = q2.qkind &&
  (fst q1.antiquotations) = (fst q2.antiquotations) &&
  equal_list equal_term (snd q1.antiquotations) (snd q2.antiquotations)

and equal_rc r1 r2 =
  Ident.lid_equals r1.residual_effect r2.residual_effect &&
  equal_opt equal_term r1.residual_typ r2.residual_typ &&
  equal_list equal_flag r1.residual_flags r2.residual_flags

and equal_flag f1 f2 =
  match f1, f2 with
  | DECREASES t1, DECREASES t2 ->
    equal_decreases_order t1 t2

  | _ -> f1 = f2

and equal_decreases_order d1 d2 =
  match d1, d2 with
  | Decreases_lex ts1, Decreases_lex ts2 ->
    equal_list equal_term ts1 ts2

  | Decreases_wf (t1, t1'), Decreases_wf (t2, t2') ->
    equal_term t1 t2 &&
    equal_term t1' t2'
  | _ -> false

and equal_arg_qualifier a1 a2 =
  a1.aqual_implicit = a2.aqual_implicit &&
  equal_list equal_term a1.aqual_attributes a2.aqual_attributes

and equal_lbname l1 l2 =
  match l1, l2 with
  | Inl b1, Inl b2 -> Ident.ident_equals b1.ppname b2.ppname
  | Inr f1, Inr f2 -> Ident.lid_equals f1.fv_name f2.fv_name
  | _ -> false

and equal_subst_elt s1 s2 =
  match s1, s2 with
  | DB (i1, bv1), DB(i2, bv2)
  | NM (bv1, i1), NM (bv2, i2) ->
    i1=i2 && equal_bv bv1 bv2
  | NT (bv1, t1), NT (bv2, t2) ->
    equal_bv bv1 bv2 &&
    equal_term t1 t2
  | UN (i1, u1), UN (i2, u2) ->
    i1 = i2 &&
    equal_universe u1 u2
  | UD (un1, i1), UD (un2, i2) ->
    i1 = i2 &&
    Ident.ident_equals un1 un2
  | DT (i1, t1), DT (i2, t2) ->
    i1 = i2 &&
    equal_term t1 t2
  | _ -> false

instance hashable_term : hashable term = {
  hash = ext_hash_term;
}

instance hashable_lident : hashable Ident.lident = {
  hash = (fun l -> hash (Ident.string_of_lid l));
}

instance hashable_ident : hashable Ident.ident = {
  hash = (fun i -> hash (Ident.string_of_id i));
}

instance hashable_binding : hashable binding = {
  hash = (function
          | Binding_var bv -> hash bv.sort
          | Binding_lid (l, (us, t)) -> hash l `H.mix` hash us `H.mix` hash t
          | Binding_univ u -> hash u);
}

instance hashable_bv : hashable bv = {
  // hash name?
  hash = (fun b -> hash b.sort);
}

instance hashable_fv : hashable fv = {
  hash = (fun f -> hash f.fv_name);
}

instance hashable_binder : hashable binder = {
  hash = (fun b -> hash b.binder_bv);
}

instance hashable_letbinding : hashable letbinding = {
  hash = (fun lb -> hash lb.lbname `H.mix` hash lb.lbtyp `H.mix` hash lb.lbdef);
}

instance hashable_pragma : hashable pragma = {
  hash = (function
          | ShowOptions -> hash 1
          | SetOptions s -> hash 2 `H.mix` hash s
          | ResetOptions s -> hash 3 `H.mix` hash s
          | PushOptions s -> hash 4 `H.mix` hash s
          | PopOptions -> hash 5
          | RestartSolver -> hash 6
          | PrintEffectsGraph -> hash 7
          | Check t -> hash 8 `H.mix` hash t
          );
}

let rec hash_sigelt (se:sigelt) : hash_code =
  hash_sigelt' se.sigel

and hash_sigelt' (se:sigelt') : hash_code =
  match se with
  | Sig_inductive_typ {lid; us; params; num_uniform_params; t; mutuals; ds; injective_type_params} ->
    hash 0 `H.mix`
    hash lid `H.mix`
    hash us `H.mix`
    hash params `H.mix`
    hash num_uniform_params `H.mix`
    hash t `H.mix`
    hash mutuals `H.mix`
    hash ds `H.mix`
    hash injective_type_params
  | Sig_bundle {ses; lids} ->
    hash 1 `H.mix`
    (hashable_list #_ {hash=hash_sigelt}).hash ses // sigh, reusing hashable instance when we don't have an instance
    `H.mix` hash lids
  | Sig_datacon {lid; us; t; ty_lid; num_ty_params; mutuals; injective_type_params} ->
    hash 2 `H.mix`
    hash lid `H.mix`
    hash us `H.mix`
    hash t `H.mix`
    hash ty_lid `H.mix`
    hash num_ty_params `H.mix`
    hash mutuals `H.mix`
    hash injective_type_params
  | Sig_declare_typ {lid; us; t} ->
    hash 3 `H.mix`
    hash lid `H.mix`
    hash us `H.mix`
    hash t
  | Sig_let {lbs; lids} ->
    hash 4 `H.mix`
    hash lbs `H.mix`
    hash lids
  | Sig_assume {lid; us; phi} ->
    hash 5 `H.mix`
    hash lid `H.mix`
    hash us `H.mix`
    hash phi
  | Sig_pragma p ->
    hash 6 `H.mix`
    hash p
  | _ ->
    (* FIXME: hash is not completely faithful. In particular
    it ignores effect decls and hashes them the same. *)
    hash 0

instance hashable_sigelt : hashable sigelt = {
  hash = hash_sigelt;
}
