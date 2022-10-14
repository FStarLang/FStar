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
module FStar.Syntax.Hash
open FStar
open FStar.Compiler
open FStar.Compiler.Effect
open FStar.Compiler.Util
open FStar.Syntax.Syntax
open FStar.Const
module SS = FStar.Syntax.Subst
module UU = FStar.Syntax.Unionfind

module H = FStar.Hash
inline_for_extraction
let memoize (h:syntax 'a) (f:syntax 'a -> H.hash_code) : H.hash_code =
  match !h.hash_code with
  | Some c -> c
  | None ->
    let c = f h in
    h.hash_code := Some c;
    c
let rec mix_list (l:list H.hash_code) : H.hash_code =
  match l with
  | [] -> H.of_int 1229
  | hd::tl -> H.mix (H.of_int 1231) (H.mix hd (mix_list tl))
let hash_list (h:'a -> H.hash_code) (ts:list 'a) : H.hash_code = mix_list (List.map h ts)
let hash_array (h:'a -> H.hash_code) (ts:array 'a) : H.hash_code = admit()
let hash_option (h:'a -> H.hash_code) (o:option 'a) : H.hash_code =
  match o with
  | None -> H.of_int 1237
  | Some o -> H.mix (H.of_int 1249) (h o)
inline_for_extraction
let hash_pair (h:'a -> H.hash_code) (i:'b -> H.hash_code) (x:('a * 'b)) =
  H.mix (h (fst x)) (i (snd x))
inline_for_extraction
let hash_list_lit (h:'a -> H.hash_code) (ts:list 'a) : H.hash_code =
  Pervasives.norm [zeta_full; delta_only [`%hash_list; `%List.map]; iota] (hash_list h ts)
let mix_list_lit (l:list H.hash_code) : H.hash_code =
  Pervasives.norm [zeta_full; delta_only [`%mix_list]; iota] (mix_list l)
let hash_byte (b:FStar.BaseTypes.byte) : H.hash_code = H.of_int (UInt8.v b)
let rec hash_term (t:term)
  : H.hash_code
  = memoize t hash_term'

and hash_term' (t:term)
  : H.hash_code
  //Primes: 1 -- 40
  = match (SS.compress t).n with
    | Tm_bvar bv -> H.mix (H.of_int 3) (H.of_int bv.index)
    | Tm_name bv -> H.mix (H.of_int 5)
                         (H.mix (H.of_string (Ident.string_of_id bv.ppname))
                                (H.of_int bv.index))
    | Tm_fvar fv -> H.mix (H.of_int 7) (hash_fv fv)
    | Tm_uinst(t, us) -> H.mix (H.of_int 11)
                                   (H.mix (hash_term t)
                                               (hash_list hash_universe us))
    | Tm_constant sc -> H.mix (H.of_int 13) (hash_constant sc)
    | Tm_type u -> H.mix (H.of_int 17) (hash_universe u)
    | Tm_abs(bs, t, rcopt) -> H.mix (H.of_int 19)
                                        (H.mix (hash_list hash_binder bs)
                                                    (H.mix (hash_term t)
                                                                (hash_option hash_rc rcopt)))
    | Tm_arrow(bs, c) -> H.mix (H.of_int 23) (hash_comp c)
    | Tm_refine(b, t) -> H.mix (H.of_int 29) (H.mix (hash_bv b) (hash_term t))
    | Tm_app (t, args) -> H.mix (H.of_int 31) (H.mix (hash_term t) (hash_list hash_arg args))
    | Tm_match (t, asc_opt, branches, rcopt) ->
      H.mix (H.of_int 37) 
            (H.mix (hash_option hash_match_returns asc_opt)
                   (H.mix (H.mix (hash_term t) (hash_list hash_branch branches))
                          (hash_option hash_rc rcopt)))
    | Tm_ascribed(t, a, lopt) -> H.mix (H.of_int 43) (H.mix (hash_term t) (H.mix (hash_ascription a) (hash_option hash_lid lopt)))
    | Tm_let((false, [lb]), t) -> H.mix (H.of_int 47) (H.mix (hash_lb lb) (hash_term t))
    | Tm_let((_, lbs), t) -> H.mix (H.of_int 51) (H.mix (hash_list hash_lb lbs) (hash_term t))
    | Tm_uvar uv -> H.mix (H.of_int 53) (hash_uvar uv)
    | Tm_meta(t, m) -> H.mix (H.of_int 61) (hash_meta m)
    | Tm_lazy li -> H.mix (H.of_int 67) (hash_lazyinfo li)
    | Tm_quoted (t, qi) -> H.mix (H.of_int 71) (hash_quoteinfo qi)
    | Tm_unknown -> H.of_int 73
    | Tm_delayed _ -> failwith "Impossible"

and hash_lb lb =
  mix_list_lit
    [ H.of_int 79;
      hash_lbname lb.lbname;
      hash_list hash_ident lb.lbunivs;
      hash_term lb.lbtyp;
      hash_lid lb.lbeff;
      hash_term lb.lbdef;
      hash_list hash_term lb.lbattrs]

and hash_match_returns (b, asc) = 
  H.mix (hash_binder b)
        (hash_ascription asc)
        
and hash_branch b =
  let p, topt, t = b in
  mix_list_lit
    [H.of_int 83;
     hash_pat p;
     hash_option hash_term topt;
     hash_term t]

and hash_pat p =
  match p.v with
  | Pat_constant c -> H.mix (H.of_int 89) (hash_constant c)
  | Pat_cons(fv, _us, args) ->
    mix_list_lit
      [H.of_int 97;
       hash_fv fv;
       hash_list (hash_pair hash_pat hash_bool) args]
  | Pat_var bv -> H.mix (H.of_int 101) (hash_bv bv)
  | Pat_wild bv -> H.mix (H.of_int 103) (hash_bv bv)
  | Pat_dot_term t -> mix_list_lit [H.of_int 107; hash_option hash_term t]

and hash_comp c =
  //Primes: 141--160
  memoize c (fun c ->
    match c.n with
    | Total (t, ou) ->
      mix_list_lit
        [H.of_int 811;
         hash_term t;
         hash_option hash_universe ou]
    | GTotal (t, ou) ->
      mix_list_lit
        [H.of_int 821;
         hash_term t;
         hash_option hash_universe ou]
    | Comp ct ->
      mix_list_lit
        [H.of_int 823;
         hash_list hash_universe ct.comp_univs;
         hash_lid ct.effect_name;
         hash_term ct.result_typ;
         hash_list hash_arg ct.effect_args;
         hash_list hash_flag ct.flags])

and hash_bv b = H.mix (hash_ident b.ppname) (hash_term b.sort)
and hash_fv fv = H.of_string (Ident.string_of_lid fv.fv_name.v)
and hash_binder (b:binder) =
  mix_list_lit
    [hash_bv b.binder_bv;
     hash_option hash_bqual b.binder_qual;
     hash_list hash_term b.binder_attrs]

and hash_universe =
  //Primes: 41 -- 60
  function
  | U_zero -> H.of_int 179
  | U_succ u -> H.mix (H.of_int 181) (hash_universe u)
  | U_max us -> H.mix (H.of_int 191) (hash_list hash_universe us)
  | U_bvar i -> H.mix (H.of_int 193) (H.of_int i)
  | U_name i -> H.mix (H.of_int 197) (hash_ident i)
  | U_unif uv -> H.mix (H.of_int 199) (hash_universe_uvar uv)
  | U_unknown -> H.of_int 211

and hash_arg (t, aq) =
  H.mix (hash_term t) (hash_option hash_arg_qualifier aq)

and hash_arg_qualifier aq = 
  H.mix (hash_bool aq.aqual_implicit)
        (hash_list hash_term aq.aqual_attributes)
  
and hash_bqual =
  //Primes: 81--100
  function
  | Implicit true -> H.of_int 419
  | Implicit false -> H.of_int 421
  | Meta t -> H.mix (H.of_int 431) (hash_term t)
  | Equality -> H.of_int 433

and hash_uvar (u, _) = H.of_int (UU.uvar_id u.ctx_uvar_head)

and hash_universe_uvar u = H.of_int (UU.univ_uvar_id u)

and hash_ascription (a, to, b) =
  H.mix
    (match a with
    | Inl t -> hash_term t
    | Inr c -> hash_comp c)
    (hash_option hash_term to)

and hash_bool b =
  if b then H.of_int 307
  else H.of_int 311

and hash_constant =
  //Primes: 61--80
  function
  | Const_effect -> H.of_int 283
  | Const_unit -> H.of_int 293
  | Const_bool b -> hash_bool b
  | Const_int (s, o) -> H.mix (H.of_int 313)
                             (H.mix (H.of_string s)
                                    (hash_option hash_sw o))
  | Const_char c -> H.mix (H.of_int 317) (H.of_int (UInt32.v (Char.u32_of_char c)))
  | Const_float d -> H.mix (H.of_int 331) (H.of_int 0) //(hash_double d)(* ?? *)
  | Const_real s -> H.mix (H.of_int 337) (H.of_string s)
  | Const_bytearray (bs, _) -> H.mix (H.of_int 347) (hash_array hash_byte bs)
  | Const_string (s, _) -> H.mix (H.of_int 349) (H.of_string s)
  | Const_range_of -> H.of_int 353
  | Const_set_range_of -> H.of_int 359
  | Const_range r -> H.mix (H.of_int 367) (H.of_string (Range.string_of_range r))
  | Const_reify -> H.of_int 367
  | Const_reflect l -> H.mix (H.of_int 373) (hash_lid l)

and hash_sw (s, w) =
  //Primes: 101-120
  H.mix
  (match s with
   | Unsigned -> H.of_int 547
   | Signed -> H.of_int 557)
  (match w with
   | Int8 -> H.of_int 563
   | Int16 -> H.of_int 569
   | Int32 -> H.of_int 571
   | Int64 -> H.of_int 577)

and hash_ident i = H.of_string (Ident.string_of_id i)
and hash_lid l = H.of_string (Ident.string_of_lid l)
and hash_lbname l =
  match l with
  | Inl bv -> hash_bv bv
  | Inr fv -> hash_fv fv
and hash_rc rc =
  mix_list_lit
    [ hash_lid rc.residual_effect;
      hash_option hash_term rc.residual_typ;
      hash_list hash_flag rc.residual_flags ]

and hash_subst (s:subst_ts) : H.hash_code =
  hash_list (hash_list hash_subst_elt) (fst s)

and hash_subst_elt =
  function
   | DB (i, bv) -> mix_list_lit [H.of_int 1087; H.of_int i; hash_bv bv]
   | NM (bv, i) -> mix_list_lit [H.of_int 1091; hash_bv bv; H.of_int i]
   | NT (bv, t) -> mix_list_lit [H.of_int 1093; hash_bv bv; hash_term t]
   | UN (i, u) -> mix_list_lit [H.of_int 1097; H.of_int i; hash_universe u]
   | UD (un, i) -> mix_list_lit [H.of_int 1103; hash_ident un; H.of_int i]

and hash_flag =
  function
  | TOTAL -> H.of_int 947
  | MLEFFECT -> H.of_int 953
  | LEMMA -> H.of_int 967
  | RETURN -> H.of_int 971
  | PARTIAL_RETURN -> H.of_int 977
  | SOMETRIVIAL -> H.of_int 983
  | TRIVIAL_POSTCONDITION -> H.of_int 991
  | SHOULD_NOT_INLINE -> H.of_int 997
  | CPS -> H.of_int 1009
  | DECREASES (Decreases_lex ts) -> H.mix (H.of_int 1013) (hash_list hash_term ts)
  | DECREASES (Decreases_wf (t0, t1)) -> H.mix (H.of_int 2341) (hash_list hash_term [t0;t1])

and hash_meta m =
  match m with
  | Meta_pattern (ts, args) ->
    mix_list_lit
      [ H.of_int 1019;
        hash_list hash_term ts;
        hash_list (hash_list hash_arg) args ]
  | Meta_named l ->
    mix_list_lit
      [ H.of_int 1021;
        hash_lid l ]
  | Meta_labeled (s, r, _) ->
    mix_list_lit
      [ H.of_int 1031;
        H.of_string s;
        H.of_string (Range.string_of_range r) ]
  | Meta_desugared msi ->
    mix_list_lit
      [ H.of_int 1033;
        hash_meta_source_info msi ]
  | Meta_monadic(m, t) ->
    mix_list_lit
      [ H.of_int 1039;
        hash_lid m;
        hash_term t ]
  | Meta_monadic_lift (m0, m1, t) ->
    mix_list_lit
      [H.of_int 1069;
       hash_lid m0;
       hash_lid m1;
       hash_term t]

and hash_meta_source_info m =
   match m with
   | Sequence -> H.of_int 1049
   | Primop -> H.of_int 1051
   | Masked_effect -> H.of_int 1061
   | Meta_smt_pat -> H.of_int 1063
   | Machine_integer sw -> H.mix (H.of_int 1069) (hash_sw sw)

and hash_lazyinfo li = H.of_int 0 //no meaningful way to hash the blob

and hash_quoteinfo qi =
  H.mix
    (hash_bool (qi.qkind = Quote_static))
    (hash_list (hash_pair hash_bv hash_term) qi.antiquotes)

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

let rec equal_term (t1 t2:term)
  : bool
  = if physical_equality t1 t2 then true else
    if hash_term t1 <> hash_term t2 then false else
    match (SS.compress t1).n, (SS.compress t2).n with
    | Tm_bvar x, Tm_bvar y -> x.index = y.index
    | Tm_name x, Tm_name y ->
      Ident.ident_equals x.ppname y.ppname &&
      x.index = y.index
    | Tm_fvar f, Tm_fvar g -> equal_fv f g
    | Tm_uinst (t1, u1), Tm_uinst (t2, u2) ->
      equal_term t1 t2 &&
      equal_list equal_universe u1 u2
    | Tm_constant c1, Tm_constant c2 -> equal_constant c1 c2
    | Tm_type u1, Tm_type u2 -> equal_universe u1 u2
    | Tm_abs(bs1, t1, rc1), Tm_abs(bs2, t2, rc2) ->
      equal_list equal_binder bs1 bs2 &&
      equal_term t1 t2 &&
      equal_opt equal_rc rc1 rc2
    | Tm_arrow(bs1, c1), Tm_arrow(bs2, c2) ->
      equal_list equal_binder bs1 bs2 &&
      equal_comp c1 c2
    | Tm_refine(b1, t1), Tm_refine(b2, t2) ->
      equal_bv b1 b2 &&
      equal_term t1 t2
    | Tm_app(t1, as1), Tm_app(t2, as2) ->
      equal_term t1 t2 &&
      equal_list equal_arg as1 as2
    | Tm_match(t1, asc_opt1, bs1, ropt1), Tm_match(t2, asc_opt2, bs2, ropt2) ->
      equal_term t1 t2 &&
      equal_opt equal_match_returns asc_opt1 asc_opt2 &&
      equal_list equal_branch bs1 bs2 &&
      equal_opt equal_rc ropt1 ropt2
    | Tm_ascribed(t1, a1, l1), Tm_ascribed(t2, a2, l2) ->
      equal_term t1 t2 &&
      equal_ascription a1 a2 &&
      equal_opt Ident.lid_equals l1 l2
    | Tm_let((r1, lbs1), t1), Tm_let((r2, lbs2), t2) ->
      r1 = r2 &&
      equal_list equal_letbinding lbs1 lbs2 &&
      equal_term t1 t2
    | Tm_uvar u1, Tm_uvar u2 ->
      equal_uvar u1 u2
    | Tm_meta(t1, m1), Tm_meta(t2, m2) ->
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
  | Total (t1, u1), Total (t2, u2)
  | GTotal (t1, u1), GTotal (t2, u2) ->
    equal_term t1 t2 &&
    equal_opt equal_universe u1 u2
  | Comp ct1, Comp ct2 ->
    Ident.lid_equals ct1.effect_name ct2.effect_name &&
    equal_list equal_universe ct1.comp_univs ct2.comp_univs &&
    equal_term ct1.result_typ ct2.result_typ &&
    equal_list equal_arg ct1.effect_args ct2.effect_args &&
    equal_list equal_flag ct1.flags ct2.flags

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
  Ident.lid_equals f1.fv_name.v f2.fv_name.v

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
  | Const_float d1, Const_float d2 -> d1=d2
  | Const_real s1, Const_real s2 -> s1=s2
  | Const_bytearray (bs1, _), Const_bytearray(bs2, _) -> bs1=bs2
  | Const_string (s1, _), Const_string (s2, _) -> s1=s2
  | Const_range_of, Const_range_of
  | Const_set_range_of, Const_set_range_of -> true
  | Const_range r1, Const_range r2 -> Range.compare r1 r2 = 0
  | Const_reify, Const_reify -> true
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
  | Pat_wild bv1, Pat_wild bv2 ->
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

and equal_lazyinfo l1 l2 = l1 = l2

and equal_quoteinfo q1 q2 =
  q1.qkind = q2.qkind &&
  equal_list (equal_pair equal_bv equal_term) q1.antiquotes q2.antiquotes

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
    
and equal_arg_qualifier a1 a2 =
  a1.aqual_implicit = a2.aqual_implicit &&
  equal_list equal_term a1.aqual_attributes a2.aqual_attributes

and equal_lbname l1 l2 =
  match l1, l2 with
  | Inl b1, Inl b2 -> Ident.ident_equals b1.ppname b2.ppname
  | Inr f1, Inr f2 -> Ident.lid_equals f1.fv_name.v f2.fv_name.v

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
