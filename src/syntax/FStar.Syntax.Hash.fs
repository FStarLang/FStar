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
#light "off"
module FStar.Syntax.Hash
open FStar.ST
open FStar.All
open FStar.Util
open FStar.Const
open FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module UU = FStar.Syntax.Unionfind

module H = FStar.Hash
inline_for_extraction
let memoize (h:syntax<'a>) (f:syntax<'a> -> H.hash_code) : H.hash_code =
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
    | Tm_name bv -> H.mix (H.of_int 5) (H.of_string (Ident.string_of_id bv.ppname))
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
    | Tm_match (t, branches) -> H.mix (H.of_int 37) (H.mix (hash_term t) (hash_list hash_branch branches))
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
  | Pat_cons(fv, args) ->
    mix_list_lit
      [H.of_int 97;
       hash_fv fv;
       hash_list (hash_pair hash_pat hash_bool) args]
  | Pat_var bv -> H.mix (H.of_int 101) (hash_bv bv)
  | Pat_wild bv -> H.mix (H.of_int 103) (hash_bv bv)
  | Pat_dot_term (bv, t) -> mix_list_lit [H.of_int 107; hash_bv bv; hash_term t]

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
     hash_option hash_arg_qualifier b.binder_qual;
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

and hash_arg_qualifier =
  //Primes: 81--100
  function
  | Implicit true -> H.of_int 419
  | Implicit false -> H.of_int 421
  | Meta t -> H.mix (H.of_int 431) (hash_term t)
  | Equality -> H.of_int 433

and hash_uvar (u, _) = H.of_int (FStar.Syntax.Unionfind.uvar_id u.ctx_uvar_head)

and hash_universe_uvar u = H.of_int (FStar.Syntax.Unionfind.univ_uvar_id u)

and hash_ascription (a, to) =
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
  | DECREASES t -> H.mix (H.of_int 1013) (hash_term t)

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
  H.of_int
  (match m with
   | Sequence -> 1049
   | Primop -> 1051
   | Masked_effect -> 1061
   | Meta_smt_pat -> 1063)

and hash_lazyinfo li = H.of_int 0 //no meaningful way to hash the blob

and hash_quoteinfo qi =
  H.mix
    (hash_bool (qi.qkind = Quote_static))
    (hash_list (hash_pair hash_bv hash_term) qi.antiquotes)
