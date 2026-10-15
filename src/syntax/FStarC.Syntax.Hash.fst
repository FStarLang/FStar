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
open FStarC.Class.Hashable
open FStarC
open FStarC.Effect
open FStarC.Util
open FStarC.Syntax.Syntax
open FStarC.Const
module BU = FStarC.Util

module H = FStarC.Hash
module Subst = FStarC.Syntax.Subst

////////////////////////////////////////////////////////////////////////////////
let rec equal_list (f:'a -> 'a -> ML bool) (l1 l2:list 'a)
  : ML bool
  = match l1, l2 with
    | [], [] -> true
    | h1::t1, h2::t2 -> f h1 h2 && equal_list f t1 t2
    | _ -> false

let equal_opt (f:'a -> 'a -> ML bool) (o1 o2:option 'a)
  : ML bool
  = match o1, o2 with
    | None, None -> true
    | Some a, Some b -> f a b
    | _ -> false

let equal_pair (f:'a -> 'a -> ML bool) (g:'b -> 'b -> ML bool) (x1:('a & 'b)) (x2:('a & 'b))
  : ML bool
  = f (fst x1) (fst x2) && g (snd x1) (snd x2)

let equal_poly x y = x=y

(* The unique id of a (term or universe) uvar, independent of the unionfind
   graph, as used by the hash codes. *)
let uvar_unique_id (u : FStarC.Unionfind.p_uvar 'a & version & Range.range) : int =
  let p, _, _ = u in
  FStarC.Unionfind.puf_unique_id p

(* The hash code is computed eagerly when the term is built,
   see FStarC.Syntax.Syntax.hash_term'. *)
let ext_hash_term (t:term) : H.hash_code = t.hash_code

(* Structural equality on terms. With [c = false], terms are compared *as they
   are*: delayed substitutions, solved uvars and lazy terms are not unfolded, so
   this is only complete for deeply compressed terms (it is always sound). It
   is then consistent with the eagerly computed hash codes: equal terms have
   equal hash codes. With [c = true], every subterm is compressed first, so
   this is equality up to delayed substitutions and solved uvars; the hash
   codes cannot be used to shortcut it then. *)
let rec equal_term_c (c:bool) (t1 t2:term)
  : ML bool
  = if physical_equality t1 t2 then true else
    if physical_equality t1.n t2.n then true else
    if not c && ext_hash_term t1 <> ext_hash_term t2 then false else
    let t1, t2 = if c then Subst.compress t1, Subst.compress t2 else t1, t2 in
    match t1.n, t2.n with
    | Tm_bvar x, Tm_bvar y -> x.index = y.index
    | Tm_name x, Tm_name y -> x.index = y.index
    | Tm_fvar f, Tm_fvar g -> equal_fv c f g
    | Tm_uinst (t1, u1), Tm_uinst (t2, u2) ->
      equal_term_c c t1 t2 &&
      equal_list (equal_universe c) u1 u2
    | Tm_constant c1, Tm_constant c2 -> equal_constant c c1 c2
    | Tm_type u1, Tm_type u2 -> equal_universe c u1 u2
    | Tm_abs {b=b1; body=t1; rc_opt=rc1}, Tm_abs {b=b2; body=t2; rc_opt=rc2} ->
      equal_binder c b1 b2 &&
      equal_term_c c t1 t2 &&
      equal_opt (equal_rc c) rc1 rc2
    | Tm_arrow {b=b1; comp=c1}, Tm_arrow {b=b2; comp=c2} ->
      equal_binder c b1 b2 &&
      equal_comp c c1 c2
    | Tm_refine {b=b1; phi=t1}, Tm_refine {b=b2; phi=t2} ->
      equal_bv c b1 b2 &&
      equal_term_c c t1 t2
    | Tm_app {hd=hd1; arg=arg1}, Tm_app {hd=hd2; arg=arg2} ->
      equal_term_c c hd1 hd2 &&
      equal_arg c arg1 arg2
    | Tm_match {scrutinee=t1; ret_opt=asc_opt1; brs=bs1; rc_opt=ropt1},
      Tm_match {scrutinee=t2; ret_opt=asc_opt2; brs=bs2; rc_opt=ropt2} ->
      equal_term_c c t1 t2 &&
      equal_opt (equal_match_returns c) asc_opt1 asc_opt2 &&
      equal_list (equal_branch c) bs1 bs2 &&
      equal_opt (equal_rc c) ropt1 ropt2
    | Tm_ascribed {tm=t1; asc=a1; eff_opt=l1},
      Tm_ascribed {tm=t2; asc=a2; eff_opt=l2} ->
      equal_term_c c t1 t2 &&
      equal_ascription c a1 a2 &&
      equal_opt Ident.lid_equals l1 l2
    | Tm_let {lbs=(r1, lbs1); body=t1}, Tm_let {lbs=(r2, lbs2); body=t2} ->
      r1 = r2 &&
      equal_list (equal_letbinding c) lbs1 lbs2 &&
      equal_term_c c t1 t2
    | Tm_uvar u1, Tm_uvar u2 ->
      equal_uvar c u1 u2
    | Tm_delayed {tm=t1; substs=s1}, Tm_delayed {tm=t2; substs=s2} ->
      equal_term_c c t1 t2 &&
      equal_subst_ts c s1 s2
    | Tm_meta {tm=t1; meta=m1}, Tm_meta {tm=t2; meta=m2} ->
      equal_term_c c t1 t2 &&
      equal_meta c m1 m2
    | Tm_lazy l1, Tm_lazy l2 ->
      equal_lazyinfo c l1 l2
    | Tm_quoted (t1, q1), Tm_quoted (t2, q2) ->
      equal_term_c c t1 t2 &&
      equal_quoteinfo c q1 q2
    | Tm_unknown, Tm_unknown ->
      true
    | _ -> false

and equal_comp (c:bool) c1 c2
  : ML bool
  =
  if physical_equality c1 c2 then true else
  if not c && c1.hash_code <> c2.hash_code then false else
  match c1.n, c2.n with
  | Comp ct1, Comp ct2 ->
    Ident.lid_equals ct1.effect_name ct2.effect_name &&
    equal_term_c c ct1.result_typ ct2.result_typ &&
    equal_list (equal_flag c) ct1.flags ct2.flags

and equal_binder (c:bool) b1 b2
  : ML bool
  =
  if physical_equality b1 b2 then true else
  equal_bv c b1.binder_bv b2.binder_bv &&
  equal_bqual c b1.binder_qual b2.binder_qual &&
  equal_list (equal_term_c c) b1.binder_attrs b2.binder_attrs

and equal_match_returns (c:bool) x1 x2
  : ML bool
  =
  let (b1, asc1) = x1 in
  let (b2, asc2) = x2 in
  equal_binder c b1 b2 &&
  equal_ascription c asc1 asc2

and equal_ascription (c:bool) x1 x2
  : ML bool
  =
  if physical_equality x1 x2 then true else
  let a1, t1, b1 = x1 in
  let a2, t2, b2 = x2 in
  (match a1, a2 with
   | Inl t1, Inl t2 -> equal_term_c c t1 t2
   | Inr c1, Inr c2 -> equal_comp c c1 c2
   | _ -> false) &&
  equal_opt (equal_term_c c) t1 t2 &&
  b1 = b2

and equal_letbinding (c:bool) l1 l2
  : ML bool
  =
  if physical_equality l1 l2 then true else
  equal_lbname c l1.lbname l2.lbname &&
  equal_list Ident.ident_equals l1.lbunivs l2.lbunivs &&
  equal_term_c c l1.lbtyp l2.lbtyp &&
  Ident.lid_equals l1.lbeff l2.lbeff &&
  equal_term_c c l1.lbdef l2.lbdef &&
  equal_list (equal_term_c c) l1.lbattrs l2.lbattrs

and equal_uvar (c:bool) x1 x2
  : ML bool
  =
  let (u1, (s1, _)) = x1 in
  let (u2, (s2, _)) = x2 in
  uvar_unique_id u1.ctx_uvar_head = uvar_unique_id u2.ctx_uvar_head &&
  equal_list (equal_list (equal_subst_elt c)) s1 s2

and equal_subst_ts (c:bool) (s1 s2:subst_ts)
  : ML bool
  = equal_list (equal_list (equal_subst_elt c)) (fst s1) (fst s2)

and equal_bv (c:bool) b1 b2
  : ML bool
  =
  if physical_equality b1 b2 then true else
  Ident.ident_equals b1.ppname b2.ppname &&
  equal_term_c c b1.sort b2.sort

and equal_fv (c:bool) f1 f2
  : ML bool
  =
  if physical_equality f1 f2 then true else
  Ident.lid_equals f1.fv_name f2.fv_name

and equal_universe (c:bool) u1 u2
  : ML bool
  =
  if physical_equality u1 u2 then true else
  let u1, u2 = if c then Subst.compress_univ u1, Subst.compress_univ u2 else u1, u2 in
  match u1, u2 with
  | U_zero, U_zero -> true
  | U_succ u1, U_succ u2 -> equal_universe c u1 u2
  | U_max us1, U_max us2 -> equal_list (equal_universe c) us1 us2
  | U_bvar i1, U_bvar i2 -> i1 = i2
  | U_name x1, U_name x2 -> Ident.ident_equals x1 x2
  | U_unif u1, U_unif u2 -> uvar_unique_id u1 = uvar_unique_id u2
  | U_unknown, U_unknown -> true
  | _ -> false

and equal_constant (c:bool) c1 c2
  : ML bool
  =
  if physical_equality c1 c2 then true else
  match c1, c2 with
  | Const_effect, Const_effect
  | Const_unit, Const_unit -> true
  | Const_bool b1, Const_bool b2 -> b1 = b2
  | Const_int (v1, _), Const_int (v2, _) -> v1 = v2
  | Const_machine_int (v1, _, s1, w1), Const_machine_int (v2, _, s2, w2) ->
    v1 = v2 && s1 = s2 && w1 = w2
  | Const_char c1, Const_char c2 -> c1=c2
  | Const_real r1, Const_real r2 -> Real.cmp r1 r2 = Order.Eq
  | Const_string (s1, _), Const_string (s2, _) -> s1=s2
  | Const_range_of, Const_range_of
  | Const_set_range_of, Const_set_range_of -> true
  (* NB: full structural equality, as in FStarC.Const.eq_const and in the
  reflection API (where [range] is an eqtype, and observable via [explode]).
  Comparing with Range.compare would be coarser -- it ignores the end
  position and the use range -- and hence unsound here. *)
  | Const_range r1, Const_range r2 -> r1 = r2
  | Const_reify _, Const_reify _ -> true
  | Const_reflect l1, Const_reflect l2 -> Ident.lid_equals l1 l2
  | _ -> false

and equal_arg (c:bool) arg1 arg2
  : ML bool
  =
  if physical_equality arg1 arg2 then true else
  let t1, a1 = arg1 in
  let t2, a2 = arg2 in
  equal_term_c c t1 t2 &&
  equal_opt (equal_arg_qualifier c) a1 a2

and equal_bqual (c:bool) b1 b2
  : ML bool
  =
  equal_opt (equal_binder_qualifier c) b1 b2

and equal_binder_qualifier (c:bool) b1 b2
  : ML bool
  =
  match b1, b2 with
  | Implicit b1, Implicit b2 -> b1 = b2
  | Equality, Equality -> true
  | Meta t1, Meta t2 -> equal_term_c c t1 t2
  | _ -> false

and equal_branch (c:bool) x1 x2
  : ML bool
  =
  let (p1, w1, t1) = x1 in
  let (p2, w2, t2) = x2 in
  equal_pat c p1 p2 &&
  equal_opt (equal_term_c c) w1 w2 &&
  equal_term_c c t1 t2

and equal_pat (c:bool) p1 p2
  : ML bool
  =
  if physical_equality p1 p2 then true else
  match p1.v, p2.v with
  | Pat_constant c1, Pat_constant c2 ->
    equal_constant c c1 c2
  | Pat_cons(fv1, us1, args1), Pat_cons(fv2, us2, args2) ->
    equal_fv c fv1 fv2 &&
    equal_opt (equal_list (equal_universe c)) us1 us2 &&
    equal_list (equal_pair (equal_pat c) equal_poly) args1 args2
  | Pat_var bv1, Pat_var bv2 ->
    equal_bv c bv1 bv2
  | Pat_dot_term t1, Pat_dot_term t2 ->
    equal_opt (equal_term_c c) t1 t2
  | _ -> false

and equal_meta (c:bool) m1 m2
  : ML bool
  =
  match m1, m2 with
  | Meta_pattern (ts1, args1), Meta_pattern (ts2, args2) ->
    equal_list (equal_term_c c) ts1 ts2 &&
    equal_list (equal_list (equal_arg c)) args1 args2
  | Meta_named l1, Meta_named l2  ->
    Ident.lid_equals l1 l2
  | Meta_labeled (s1, r1, _), Meta_labeled (s2, r2, _) ->
    Range.compare r1 r2 = 0 &&
    s1 = s2
  | Meta_desugared msi1, Meta_desugared msi2 ->
    msi1 = msi2
  | Meta_monadic(m1, t1), Meta_monadic(m2, t2) ->
    Ident.lid_equals m1 m2 &&
    equal_term_c c t1 t2
  | Meta_monadic_lift (m1, n1, t1), Meta_monadic_lift (m2, n2, t2) ->
    Ident.lid_equals m1 m2 &&
    Ident.lid_equals n1 n2 &&
    equal_term_c c t1 t2
  | _ -> false

and equal_lazyinfo (c:bool) l1 l2
  : ML bool
  =
  (* We cannot really compare the blobs. Just try physical
  equality (first matching kinds). *)
  BU.physical_equality l1.blob l2.blob &&
  (match l1.lkind, l2.lkind with
   (* Lazy_embedding carries a thunk, which polymorphic equality rejects. *)
   | Lazy_embedding (e1, _), Lazy_embedding (e2, _) -> e1 = e2
   | Lazy_embedding _, _ | _, Lazy_embedding _ -> false
   | k1, k2 -> k1 = k2)

and equal_quoteinfo (c:bool) q1 q2
  : ML bool
  =
  q1.qkind = q2.qkind &&
  (fst q1.antiquotations) = (fst q2.antiquotations) &&
  equal_list (equal_term_c c) (snd q1.antiquotations) (snd q2.antiquotations)

and equal_rc (c:bool) r1 r2
  : ML bool
  =
  Ident.lid_equals r1.residual_effect r2.residual_effect &&
  equal_opt (equal_term_c c) r1.residual_typ r2.residual_typ &&
  equal_list (equal_flag c) r1.residual_flags r2.residual_flags

and equal_flag (c:bool) f1 f2
  : ML bool
  =
  match f1, f2 with
  | DECREASES t1, DECREASES t2 ->
    equal_decreases_order c t1 t2

  | SMTPAT p1, SMTPAT p2 ->
    equal_term_c c p1 p2

  | _ -> f1 = f2

and equal_decreases_order (c:bool) d1 d2
  : ML bool
  =
  match d1, d2 with
  | Decreases_lex ts1, Decreases_lex ts2 ->
    equal_list (equal_term_c c) ts1 ts2

  | Decreases_wf (t1, t1'), Decreases_wf (t2, t2') ->
    equal_term_c c t1 t2 &&
    equal_term_c c t1' t2'
  | _ -> false

and equal_arg_qualifier (c:bool) a1 a2
  : ML bool
  =
  a1.aqual_implicit = a2.aqual_implicit &&
  equal_list (equal_term_c c) a1.aqual_attributes a2.aqual_attributes

and equal_lbname (c:bool) l1 l2
  : ML bool
  =
  match l1, l2 with
  | Inl b1, Inl b2 -> Ident.ident_equals b1.ppname b2.ppname
  | Inr f1, Inr f2 -> Ident.lid_equals f1.fv_name f2.fv_name
  | _ -> false

and equal_subst_elt (c:bool) s1 s2
  : ML bool
  =
  match s1, s2 with
  (* Names are identified by their index; their sorts are ignored. *)
  | DB (i1, bv1), DB(i2, bv2)
  | NM (bv1, i1), NM (bv2, i2) ->
    i1=i2 && bv1.index = bv2.index
  | NT (bv1, t1), NT (bv2, t2) ->
    bv1.index = bv2.index &&
    equal_term_c c t1 t2
  | UN (i1, u1), UN (i2, u2) ->
    i1 = i2 &&
    equal_universe c u1 u2
  | UD (un1, i1), UD (un2, i2) ->
    i1 = i2 &&
    Ident.ident_equals un1 un2
  | DT (i1, t1), DT (i2, t2) ->
    i1 = i2 &&
    equal_term_c c t1 t2
  | _ -> false

let equal_term (t1 t2:term) : ML bool = equal_term_c false t1 t2
let equal_term_upto_compress (t1 t2:term) : ML bool = equal_term_c true t1 t2

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
          | Eval t -> hash 9 `H.mix` hash t
          );
}

let rec hash_sigelt (se:sigelt) : ML hash_code =
  hash_sigelt' se.sigel

and hash_sigelt' (se:sigelt') : ML hash_code =
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

open FStarC.Class.Deq
instance deq_term : deq term = {
  (=?) = equal_term;
}

module H = FStarC.HashMap
let term_map (a:Type) = H.hashmap term a
let term_map_empty (#a:Type) : ML (term_map a) = H.empty #term #a
let term_map_add (#a:Type) (t:term) (v:a) (m:term_map a) : ML (term_map a) = H.add t v m
let term_map_lookup (#a:Type) (t:term) (m:term_map a) : ML (option a) = H.lookup t m
let term_map_mem (#a:Type) (t:term) (m:term_map a) : ML bool = H.mem t m
let term_map_fold #a #b (f:term -> a -> b -> ML b) (m:term_map a) (i:b) : ML b = H.fold f m i