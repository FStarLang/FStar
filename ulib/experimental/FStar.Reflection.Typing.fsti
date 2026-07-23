(*
   Copyright 2008-2023 Microsoft Research

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

module FStar.Reflection.Typing

(** This module defines a typing judgment for (parts of) the total
    and ghost fragment of F*.
    
    We are using it in the meta DSL framework as an
    official specification for the F* type system.

    We expect it to grow to cover more of the F* language.

    IT IS HIGHLY EXPERIMENTAL AND NOT YET READY TO USE.
  *)

open FStar.List.Tot
open FStar.Reflection.V2
module L = FStar.List.Tot
module R = FStar.Reflection.V2
open FStar.Stubs.Tactics.V2.Builtins
open FStar.Stubs.Tactics.Types
include FStar.Stubs.Tactics.Types.Reflection
open FStar.Tactics.Effect
module RD = FStar.Stubs.Reflection.V2.Data
open FStar.Reflection.TermSpec
open FStar.Reflection.TermSpec.Lemmas

(* MOVE to some helper module *)
let rec fold_left_dec #a #b
  (acc : a)
  (l : list b)
  (f : a -> (x:b{x << l}) -> a)
  : Tot a (decreases l)
  =
  match l with
  | [] -> acc
  | x::xs -> fold_left_dec (f acc x) xs f

let rec map_dec #a #b
  (l : list a)
  (f : (x:a{x << l}) -> b)
  : Tot (list b) (decreases l)
  =
  match l with
  | [] -> []
  | x::xs -> f x :: map_dec xs f

let rec zip2prop #a #b (f : a -> b -> prop) (xs : list a) (ys : list b) : prop =
  match xs, ys with
  | [], [] -> True
  | x::xx, y::yy -> f x y /\ zip2prop f xx yy
  | _ -> False
(* / MOVE *)

val inspect_pack (t:R.term_view)
  : Lemma (ensures R.(inspect_ln (pack_ln t) == t))
          [SMTPat R.(inspect_ln (pack_ln t))]
  
val pack_inspect (t:R.term)
  : Lemma (requires ~(Tv_Unsupp? (inspect_ln t)))
          (ensures R.(pack_ln (inspect_ln t) == t))
          [SMTPat R.(pack_ln (inspect_ln t))]
  
val inspect_pack_namedv (t:R.namedv_view)
  : Lemma (ensures R.(inspect_namedv (pack_namedv t) == t))
          [SMTPat R.(inspect_namedv (pack_namedv t))]

val pack_inspect_namedv (t:R.namedv)
  : Lemma (ensures R.(pack_namedv (inspect_namedv t) == t))
          [SMTPat R.(pack_namedv (inspect_namedv t))]

val inspect_pack_bv (t:R.bv_view)
  : Lemma (ensures R.(inspect_bv (pack_bv t) == t))
          [SMTPat R.(inspect_bv (pack_bv t))]
  
val pack_inspect_bv (t:R.bv)
  : Lemma (ensures R.(pack_bv (inspect_bv t) == t))
          [SMTPat R.(pack_bv (inspect_bv t))]
  
val inspect_pack_binder (bview:R.binder_view)
  : Lemma (ensures R.(R.inspect_binder (R.pack_binder bview) == bview))
          [SMTPat R.(inspect_binder (pack_binder bview))]
  
val pack_inspect_binder (t:R.binder)
   : Lemma (ensures (R.pack_binder (R.inspect_binder t) == t))
           [SMTPat (R.pack_binder (R.inspect_binder t))]
  
val inspect_pack_comp (t:R.comp_view)
  : Lemma (ensures (R.inspect_comp (R.pack_comp t) == t))
          [SMTPat (R.inspect_comp (R.pack_comp t))]

val pack_inspect_comp (t:R.comp)
  : Lemma (ensures (R.pack_comp (R.inspect_comp t) == t))
          [SMTPat (R.pack_comp (R.inspect_comp t))]
  
val inspect_pack_fv (nm:R.name)
  : Lemma (ensures R.inspect_fv (R.pack_fv nm) == nm)
          [SMTPat (R.inspect_fv (R.pack_fv nm))]

val pack_inspect_fv (fv:R.fv)
  : Lemma (ensures R.pack_fv (R.inspect_fv fv) == fv)
          [SMTPat (R.pack_fv (R.inspect_fv fv))]

val inspect_pack_universe (u:R.universe_view)
  : Lemma (ensures R.inspect_universe (R.pack_universe u) == u)
          [SMTPat (R.inspect_universe (R.pack_universe u))]

val pack_inspect_universe (u:R.universe)
  : Lemma (requires ~(Uv_Unk? (inspect_universe u)))
          (ensures R.pack_universe (R.inspect_universe u) == u)
          [SMTPat (R.pack_universe (R.inspect_universe u))]

val inspect_pack_lb (lb:R.lb_view)
  : Lemma (ensures R.inspect_lb (R.pack_lb lb) == lb)
          [SMTPat (R.inspect_lb (R.pack_lb lb))]

val pack_inspect_lb (lb:R.letbinding)
  : Lemma (ensures R.pack_lb (R.inspect_lb lb) == lb)
          [SMTPat (R.pack_lb (R.inspect_lb lb))]

val inspect_pack_sigelt (sev:R.sigelt_view { ~ (Unk? sev) })
  : Lemma (ensures R.inspect_sigelt (R.pack_sigelt sev) == sev)
          [SMTPat (R.inspect_sigelt (R.pack_sigelt sev))]

val pack_inspect_sigelt (se:R.sigelt)
  : Lemma (requires ~ (Unk? (R.inspect_sigelt se)))
          (ensures R.pack_sigelt (R.inspect_sigelt se) == se)
          [SMTPat (R.pack_sigelt (R.inspect_sigelt se))]

val lookup_bvar (e:env) (x:int) : GTot (option term)

val lookup_fvar_uinst (e:R.env) (x:R.fv) (us:list R.universe) : GTot (option R.term)

let lookup_fvar (e:env) (x:fv) : GTot (option term) = lookup_fvar_uinst e x []

let pp_name_t = FStar.Sealed.Inhabited.sealed "x"
let pp_name_default : pp_name_t = FStar.Sealed.Inhabited.seal "x"
let seal_pp_name x : pp_name_t = FStar.Sealed.Inhabited.seal x

let tun = pack_ln Tv_Unknown

let sort_t = FStar.Sealed.Inhabited.sealed tun
let sort_default : sort_t = FStar.Sealed.Inhabited.seal tun
let seal_sort x : sort_t = FStar.Sealed.Inhabited.seal x

let mk_binder (pp_name:pp_name_t) (ty:term) (q:aqualv) : binder
  = pack_binder
      { ppname = pp_name;
        qual   = q;
        attrs  = [];
        sort   = ty}

let mk_simple_binder (pp_name:pp_name_t) (ty:term) : simple_binder
  = pack_binder
      { ppname = pp_name;
        qual   = Q_Explicit;
        attrs  = [];
        sort   = ty}

let extend_env (e:env) (x:var) (ty:term) : env =
  R.push_binding e ({
    ppname = seal_pp_name "x";
    uniq   = x;
    sort   = ty;
  })
  
val lookup_bvar_extend_env (g:env) (x y:var) (ty:term)
  : Lemma 
    (ensures (
           if x = y
           then lookup_bvar (extend_env g x ty) y == Some ty
           else lookup_bvar (extend_env g x ty) y == lookup_bvar g y))
    [SMTPat (lookup_bvar (extend_env g x ty) y)]

val lookup_fvar_extend_env (g:env) (x:fv) (us:universes) (y:var) (ty:term)
  : Lemma 
    (ensures lookup_fvar_uinst (extend_env g y ty) x us == lookup_fvar_uinst g x us)
    [SMTPat (lookup_fvar_uinst (extend_env g y ty) x us)]

let bv_index (x:bv)
  : var
  = (inspect_bv x).index

let namedv_uniq (x:namedv)
  : var
  = (inspect_namedv x).uniq

let binder_sort (b:binder) =
  (inspect_binder b).sort

let binder_qual (b:binder) =
  let { qual = q } = inspect_binder b in q

noeq
type subst_elt =
  | DT : nat -> term -> subst_elt
  | NT : var -> term -> subst_elt
  | ND : var -> nat -> subst_elt

let shift_subst_elt (n:nat) = function
  | DT i t -> DT (i + n) t
  | NT x t -> NT x t
  | ND x i -> ND x (i + n)

let subst = list subst_elt

let shift_subst_n (n:nat) = L.map (shift_subst_elt n)

let shift_subst = shift_subst_n 1

let maybe_uniq_of_term (x:term) =
  match inspect_ln x with
  | Tv_Var namedv -> Some (namedv_uniq namedv)
  | _ -> None

let rec find_matching_subst_elt_bv (s:subst) (bv:bv) : option subst_elt =
  match s with
  | [] -> None
  | (DT j t)::ss ->
    if j = bv_index bv
    then Some (DT j t)
    else find_matching_subst_elt_bv ss bv
  | _::ss -> find_matching_subst_elt_bv ss bv

let subst_db (bv:bv) (s:subst) : term =
  match find_matching_subst_elt_bv s bv with
  | Some (DT _ t) ->
    (match maybe_uniq_of_term t with
     | None -> t
     | Some k ->
       //if we're substituting a name j for a name k, retain the pp_name of j
       let v : namedv = pack_namedv {
         sort = (inspect_bv bv).sort;
         ppname = (inspect_bv bv).ppname;
         uniq = k;
       } in
       pack_ln (Tv_Var v))
  | _ -> pack_ln (Tv_BVar bv)

let rec find_matching_subst_elt_var (s:subst) (v:namedv) : option subst_elt =
  match s with
  | [] -> None
  | (NT y _)::rest 
  | (ND y _)::rest ->
    if y = namedv_uniq v
    then Some (L.hd s)
    else find_matching_subst_elt_var rest v
  | _::rest -> find_matching_subst_elt_var rest v

let subst_var (v:namedv) (s:subst) : term =
  match find_matching_subst_elt_var s v with
  | Some (NT _ t) ->
    (match maybe_uniq_of_term t with
     | None -> t
     | Some k ->
       pack_ln (Tv_Var (pack_namedv { inspect_namedv v with uniq = k })))
  | Some (ND _ i) ->
    let bv = pack_bv {
      sort = (inspect_namedv v).sort;
      ppname = (inspect_namedv v).ppname;
      index = i;
    } in
    pack_ln (Tv_BVar bv)
  | _ -> pack_ln (Tv_Var v)

let make_bv (n:nat) : bv_view = {
  ppname = pp_name_default;
  index = n;
  sort = sort_default;
}
let make_bv_with_name (s:pp_name_t) (n:nat) : bv_view = {
  ppname = s;
  index  = n;
  sort   = sort_default;
}


let var_as_bv (v:nat) = pack_bv (make_bv v)

let make_namedv (n:nat) : namedv_view = {
  ppname = pp_name_default;
  uniq   = n;
  sort   = sort_default;
}

let make_namedv_with_name (s:pp_name_t) (n:nat) : namedv_view = {
  ppname = s;
  uniq   = n;
  sort   = sort_default;
}

let var_as_namedv (v:nat) : namedv =
  pack_namedv {
    uniq = v;
    sort = sort_default;
    ppname = pp_name_default;
  }

(* spec-level term builder for a named variable *)
let var_as_term (v:var) : term_spec = Ts_Var v

(* concrete binder builder, kept for the (concrete) env/token/sigelt layer *)
let binder_of_t_q t q = mk_binder pp_name_default t q

(* spec-level smart constructors (return [term_spec]/[comp_spec]) *)
let mk_abs (ty:term_spec) (qual:aqualv_spec) (t:term_spec) : term_spec = Ts_Abs (Bs ty qual) t
let mk_total (t:term_spec) : comp_spec = Cs_Total t
let mk_ghost (t:term_spec) : comp_spec = Cs_GTotal t
let mk_arrow (ty:term_spec) (qual:aqualv_spec) (t:term_spec) : term_spec =
  Ts_Arrow (Bs ty qual) (mk_total t)
let mk_ghost_arrow (ty:term_spec) (qual:aqualv_spec) (t:term_spec) : term_spec =
  Ts_Arrow (Bs ty qual) (mk_ghost t)
let bound_var (i:nat) : term_spec = Ts_BVar i
let mk_let (e1 t1 e2:term_spec) : term_spec =
  Ts_Let false [] t1 e1 e2

(* concrete comp builder, kept for the (concrete) env/token/sigelt layer *)
let mk_total_tm (t:R.term) : R.comp = pack_comp (C_Total t)

let open_with_var_elt (x:var) (i:nat) : subst_elt =
  DT i (pack_ln (Tv_Var (var_as_namedv x)))
let open_with_var (x:var) (i:nat) : subst = [open_with_var_elt x i]


let rec binder_offset_patterns (ps:list (pattern & bool))
  : nat
  = match ps with
    | [] -> 0
    | (p, b)::ps ->
      let n = binder_offset_pattern p in
      let m = binder_offset_patterns ps in
      n + m

and binder_offset_pattern (p:pattern)
  : nat
  = match p with
    | Pat_Constant _
    | Pat_Dot_Term _ -> 0

    | Pat_Var _ _ -> 1

    | Pat_Cons head univs subpats ->
      binder_offset_patterns subpats



val open_with (t:term) (v:term) : term

val open_with_spec (t v:term)
  : Lemma (denote_term (open_with t v) ==
           subst_term_spec (denote_term t) [ DTs 0 (denote_term v) ])

val open_term (t:term) (v:var) : term

val open_term_spec (t:term) (v:var)
  : Lemma (denote_term (open_term t v) ==
           subst_term_spec (denote_term t) (open_with_var_spec v 0))

val close_term (t:term) (v:var) : term

val close_term_spec (t:term) (v:var)
  : Lemma (denote_term (close_term t v) ==
           subst_term_spec (denote_term t) [ NDs v 0 ])

val rename (t:term) (x y:var) : term

val rename_spec (t:term) (x y:var)
  : Lemma (denote_term (rename t x y) ==
           subst_term_spec (denote_term t) [ NTs x (Ts_Var y) ])

  
val bv_index_of_make_bv (n:nat)
  : Lemma (ensures bv_index (pack_bv (make_bv n)) == n)
          [SMTPat (bv_index (pack_bv (make_bv n)))]

val namedv_uniq_of_make_namedv (n:nat)
  : Lemma (ensures namedv_uniq (pack_namedv (make_namedv n)) == n)
          [SMTPat (namedv_uniq (pack_namedv (make_namedv n)))]

(* spec-level constants (used as [typing]/[related] indices) *)
let constant_as_term (v:vconst) : term_spec = Ts_Const v
let unit_exp : term_spec = Ts_Const C_Unit
let unit_fv = pack_fv unit_lid
let unit_ty : term_spec = Ts_FVar unit_lid
let bool_fv = pack_fv bool_lid
let bool_ty : term_spec = Ts_FVar bool_lid

(* spec-level universe helpers *)
let u_max (u1 u2:universe_spec) : universe_spec = Us_Max [u1; u2]
let u_succ (u:universe_spec) : universe_spec = Us_Succ u
let tm_type (u:universe_spec) : term_spec = Ts_Type u
let tm_prop : term_spec = Ts_FVar R.prop_qn
let eqtype_lid : R.name = ["Prims"; "eqtype"]

let true_bool : term_spec = Ts_Const C_True
let false_bool : term_spec = Ts_Const C_False

(* ---- concrete duals, kept for the (concrete) env/token/sigelt layer ---- *)
let u_zero : R.universe = pack_universe Uv_Zero
let tm_type_tm (u:R.universe) : R.term = pack_ln (Tv_Type u)
let bool_ty_tm : R.term = pack_ln (Tv_FVar bool_fv)
let true_bool_tm : R.term = pack_ln (Tv_Const C_True)
let false_bool_tm : R.term = pack_ln (Tv_Const C_False)

(* concrete [eq2] : this is only ever stored into the (concrete) [env] as a
   hypothesis, so it stays concrete. *)
let eq2 (u:universe) (t v0 v1:term)
  : term
  = let eq2 = pack_fv eq2_qn in
    let eq2 = pack_ln (Tv_UInst eq2 [u]) in
    let h = pack_ln (Tv_App eq2 (t, Q_Implicit)) in
    let h1 = pack_ln (Tv_App h (v0, Q_Explicit)) in
    let h2 = pack_ln (Tv_App h1 (v1, Q_Explicit)) in    
    h2

let b2t_lid : R.name = ["Prims"; "b2t"]
let b2t_fv : R.fv = R.pack_fv b2t_lid
(* concrete: only used to specify [fstar_env_fvs] *)
let b2t_ty : R.term = R.pack_ln (R.Tv_Arrow (mk_binder (seal "x") bool_ty_tm Q_Explicit) (mk_total_tm (tm_type_tm u_zero)))




//
// term_ctxt is used to define the equiv relation later,
//   basically putting two equiv terms in a hole gives equiv terms
//
// The abs, arrow, refine, and let cases don't seem right here,
//   since to prove their equiv, we need to extend gamma for their bodies
//
// If this is useful only for app, then may be we should remove it,
//   and add app rules to the equiv relation itself

[@@ no_auto_projectors]
noeq
type term_ctxt =
  | Ctxt_hole     : term_ctxt
  | Ctxt_app_head : term_ctxt -> (term_spec & aqualv_spec) -> term_ctxt
  | Ctxt_app_arg  : term_spec -> aqualv_spec -> term_ctxt -> term_ctxt

let rec apply_term_ctxt (e:term_ctxt) (t:term_spec) : Tot term_spec (decreases e) =
  match e with
  | Ctxt_hole -> t
  | Ctxt_app_head e arg -> Ts_App (apply_term_ctxt e t) (fst arg) (snd arg)
  | Ctxt_app_arg hd q e -> Ts_App hd (apply_term_ctxt e t) q

noeq
type constant_typing: vconst -> term_spec -> Type0 = 
  | CT_Unit: constant_typing C_Unit unit_ty
  | CT_True: constant_typing C_True bool_ty
  | CT_False: constant_typing C_False bool_ty

[@@ no_auto_projectors]
noeq
type univ_eq : universe_spec -> universe_spec -> Type0 = 
  | UN_Refl : 
    u:universe_spec ->
    univ_eq u u

  | UN_MaxCongL :
    u:universe_spec ->
    u':universe_spec ->
    v:universe_spec ->
    univ_eq u u' ->
    univ_eq (u_max u v) (u_max u' v)

  | UN_MaxCongR :
    u:universe_spec ->
    v:universe_spec ->
    v':universe_spec ->
    univ_eq v v' ->
    univ_eq (u_max u v) (u_max u v')

  | UN_MaxComm:
    u:universe_spec ->
    v:universe_spec ->
    univ_eq (u_max u v) (u_max v u)

  | UN_MaxLeq:
    u:universe_spec ->
    v:universe_spec ->
    univ_leq u v ->
    univ_eq (u_max u v) v

and univ_leq : universe_spec -> universe_spec -> Type0 = 
  | UNLEQ_Refl:
    u:universe_spec ->
    univ_leq u u

  | UNLEQ_Succ:
    u:universe_spec ->
    v:universe_spec ->
    univ_leq u v ->
    univ_leq u (u_succ v)

  | UNLEQ_Max:
    u:universe_spec ->
    v:universe_spec ->
    univ_leq u (u_max u v)

let mk_if (scrutinee then_ else_:R.term) : R.term =
  pack_ln (Tv_Match scrutinee None [(Pat_Constant C_True, then_);
                                    (Pat_Constant C_False, else_)])


// effect and type
type comp_typ = tot_or_ghost & typ
// [comp_spec_typ = tot_or_ghost & term_spec] is provided by the included
// module [FStar.Stubs.Tactics.Types.Reflection] (the token layer).

let close_comp_typ' (c:comp_spec_typ) (x:var) (i:nat) =
  fst c, subst_term_spec (snd c) [ NDs x i ]

let close_comp_typ (c:comp_spec_typ) (x:var) =
  close_comp_typ' c x 0

let open_comp_typ' (c:comp_spec_typ) (x:var) (i:nat) =
  fst c, subst_term_spec (snd c) (open_with_var_spec x i)

let open_comp_typ (c:comp_spec_typ) (x:var) =
  open_comp_typ' c x 0

let freevars_comp_typ (c:comp_spec_typ) = freevars_spec (snd c)

let mk_comp (c:comp_spec_typ) : comp_spec =
  match fst c with
  | E_Total -> mk_total (snd c)
  | E_Ghost -> mk_ghost (snd c)

let mk_arrow_ct (ty:term_spec) (qual:aqualv_spec) (c:comp_spec_typ) : term_spec =
  Ts_Arrow (Bs ty qual) (mk_comp c)

(* spec-level open/close/rename on the [term_spec] typing index *)
let open_term_spec' (t:term_spec) (v:var) : term_spec = subst_term_spec t (open_with_var_spec v 0)
let close_term_spec' (t:term_spec) (v:var) : term_spec = subst_term_spec t [ NDs v 0 ]
let open_with_spec' (t:term_spec) (v:term_spec) : term_spec = subst_term_spec t [ DTs 0 v ]
let rename_spec' (t:term_spec) (x y:var) : term_spec = subst_term_spec t [ NTs x (Ts_Var y) ]
 
type relation =
  | R_Eq
  | R_Sub

let binding = var & term
let bindings = list binding
let rename_bindings bs x y = FStar.List.Tot.map (fun (v, t) -> (v, rename t x y)) bs

let rec extend_env_l (g:env) (bs:bindings)
  : env
  = match bs with
    | [] -> g
    | (x,t)::bs -> extend_env (extend_env_l g bs) x t

//
// TODO: support for erasable attribute
//
let is_non_informative_name (l:name) : bool =
  l = R.unit_lid ||
  l = R.squash_qn ||
  l = ["FStar"; "Ghost"; "erased"]

let is_non_informative_fv (f:fv) : bool =
  is_non_informative_name (inspect_fv f)

let rec __close_term_vs_spec (i:nat) (vs : list var) (t : term_spec) : GTot term_spec (decreases vs) =
  match vs with
  | [] -> t
  | v::vs ->
    subst_term_spec (__close_term_vs_spec (i+1) vs t) [NDs v i]

let close_term_vs_spec (vs : list var) (t : term_spec) : GTot term_spec =
  __close_term_vs_spec 0 vs t

let close_term_bs_spec (bs : list binding) (t : term_spec) : GTot term_spec =
  close_term_vs_spec (List.Tot.map fst bs) t

let bindings_to_refl_bindings (bs : list binding) : list R.binding =
  L.map (fun (v, ty) -> {uniq=v; sort=ty; ppname = pp_name_default}) bs

let refl_bindings_to_bindings (bs : list R.binding) : list binding =
  L.map (fun (b:R.binding) -> b.uniq, b.sort) bs

[@@ no_auto_projectors]
noeq
type non_informative : env -> term_spec -> Type0 =
  | Non_informative_type:
    g:env ->
    u:universe_spec ->
    non_informative g (Ts_Type u)
  
  | Non_informative_fv:
    g:env ->
    x:fv{is_non_informative_fv x} ->
    non_informative g (Ts_FVar (inspect_fv x))
  
  | Non_informative_uinst:
    g:env ->
    x:fv{is_non_informative_fv x} ->
    us:list universe_spec ->
    non_informative g (Ts_UInst (inspect_fv x) us)

  | Non_informative_app:
    g:env ->
    t:term_spec ->
    arg:term_spec ->
    q:aqualv_spec ->
    non_informative g t ->
    non_informative g (Ts_App t arg q)

  | Non_informative_total_arrow:
    g:env ->
    t0:term_spec ->
    q:aqualv_spec ->
    t1:term_spec ->
    non_informative g t1 ->
    non_informative g (mk_arrow_ct t0 q (E_Total, t1))
  
  | Non_informative_ghost_arrow:
    g:env ->
    t0:term_spec ->
    q:aqualv_spec ->
    t1:term_spec ->
    non_informative g (mk_arrow_ct t0 q (E_Ghost, t1))

  | Non_informative_token:
    g:env ->
    t:term_spec ->
    squash (non_informative_token g t) ->
    non_informative g t

val bindings_ok_for_pat : env -> list R.binding -> pattern -> prop

val bindings_ok_pat_constant :
  g:env -> c:R.vconst -> Lemma (bindings_ok_for_pat g [] (Pat_Constant c))

let bindings_ok_for_branch (g:env) (bs : list R.binding) (br : branch) : prop =
  bindings_ok_for_pat g bs (fst br)

let bindings_ok_for_branch_N (g:env) (bss : list (list R.binding)) (brs : list branch) =
  zip2prop (bindings_ok_for_branch g) bss brs

let binding_to_namedv (b:R.binding) : Tot namedv =
  pack_namedv {
    RD.uniq   = b.uniq;
    RD.sort   = seal b.sort;
    RD.ppname = b.ppname;
  }

(* Elaborates the p pattern into a term, using the bs bindings for the
pattern variables. The resulting term is properly scoped only on an
environment which contains all of bs. See for instance the branch_typing
judg. Returns an option, since this can fail if e.g. there are not
enough bindings, and returns the list of unused binders as well, which
should be empty if the list of binding was indeed ok. *)
let rec elaborate_pat (p : pattern) (bs : list R.binding) : Tot (option (term & list R.binding)) (decreases p) =
  match p, bs with
  | Pat_Constant c, _ -> Some (pack_ln (Tv_Const c), bs)
  | Pat_Cons fv univs subpats, bs ->
    let head =
      match univs with
      | Some univs -> pack_ln (Tv_UInst fv univs)
      | None -> pack_ln (Tv_FVar fv)
    in
    fold_left_dec
      (Some (head, bs))
      subpats
      (fun st pi ->
        let (p,i) = pi in
        match st with | None -> None | Some (head, bs) ->
          match elaborate_pat p bs with | None -> None | Some (t, bs') -> Some (pack_ln (Tv_App head (t, (if i then Q_Implicit else Q_Explicit))), bs'))

  | Pat_Var _ _, b::bs ->
    Some (pack_ln (Tv_Var (binding_to_namedv b)), bs)
  | Pat_Dot_Term (Some t), _ -> Some (t, bs)
  | Pat_Dot_Term None, _ -> None
  | _ -> None

[@@ no_auto_projectors]
noeq
type typing : env -> term_spec -> comp_spec_typ -> Type0 =
  | T_Token :
    g:env ->
    e:term_spec ->
    c:comp_spec_typ ->
    squash (typing_token g e c) ->
    typing g e c

  | T_Var : 
     g:env ->
     x:namedv { Some? (lookup_bvar g (namedv_uniq x)) } ->
     typing g (Ts_Var (namedv_uniq x)) (E_Total, denote_term (Some?.v (lookup_bvar g (namedv_uniq x))))

  | T_FVar :
     g:env ->
     x:fv { Some? (lookup_fvar g x) } -> 
     typing g (Ts_FVar (inspect_fv x)) (E_Total, denote_term (Some?.v (lookup_fvar g x)))

  | T_UInst :
     g:env ->
     x:fv ->
     us:list universe { Some? (lookup_fvar_uinst g x us) } ->
     typing g (Ts_UInst (inspect_fv x) (denote_universes us)) (E_Total, denote_term (Some?.v (lookup_fvar_uinst g x us)))

  | T_Const:
     g:env ->
     v:vconst ->
     t:term_spec ->
     constant_typing v t ->
     typing g (constant_as_term v) (E_Total, t)

  | T_Abs :
     g:env ->
     x:var { None? (lookup_bvar g x) } ->
     ty:term ->
     body:term_spec { ~(x `Set.mem` freevars_spec body) } ->
     body_c:comp_spec_typ ->
     u:universe_spec ->
     q:aqualv_spec ->
     ty_eff:tot_or_ghost ->
     typing g (denote_term ty) (ty_eff, tm_type u) ->
     typing (extend_env g x ty) (open_term_spec' body x) body_c ->
     typing g (Ts_Abs (Bs (denote_term ty) q) body)
              (E_Total,
               Ts_Arrow (Bs (denote_term ty) q)
                        (mk_comp (close_comp_typ body_c x)))

  | T_App :
     g:env ->
     e1:term_spec ->
     e2:term_spec ->
     x:binder_spec ->
     t:term_spec ->
     eff:tot_or_ghost ->
     typing g e1 (eff, Ts_Arrow x (mk_comp (eff, t))) ->
     typing g e2 (eff, Bs?.sort x) ->
     typing g (Ts_App e1 e2 (Bs?.qual x))
              (eff, open_with_spec' t e2)

  | T_Let:
     g:env ->
     x:var { None? (lookup_bvar g x) } ->
     e1:term_spec ->
     t1:typ ->
     e2:term_spec ->
     t2:term_spec ->
     eff:tot_or_ghost ->
     typing g e1 (eff, denote_term t1) ->
     typing (extend_env g x t1) (open_term_spec' e2 x) (eff, t2) ->
     typing g (mk_let e1 (denote_term t1) e2) (eff, open_with_spec' (close_term_spec' t2 x) e1)

  | T_Arrow:
     g:env ->
     x:var { None? (lookup_bvar g x) } ->
     t1:term ->
     t2:term_spec { ~(x `Set.mem` freevars_spec t2) } ->
     u1:universe_spec ->
     u2:universe_spec ->
     q:aqualv_spec ->
     eff:tot_or_ghost ->
     t1_eff:tot_or_ghost ->
     t2_eff:tot_or_ghost ->
     typing g (denote_term t1) (t1_eff, tm_type u1) ->
     typing (extend_env g x t1) (open_term_spec' t2 x) (t2_eff, tm_type u2) ->
     typing g (Ts_Arrow (Bs (denote_term t1) q) (mk_comp (eff, t2)))
              (E_Total, tm_type (u_max u1 u2))

  | T_Refine:
     g:env ->
     x:var { None? (lookup_bvar g x) } ->     
     t:term ->
     e:term_spec { ~(x `Set.mem` freevars_spec e) } ->
     u1:universe_spec ->
     u2:universe_spec ->
     t_eff:tot_or_ghost ->
     e_eff:tot_or_ghost ->
     typing g (denote_term t) (t_eff, tm_type u1) ->
     typing (extend_env g x t) (open_term_spec' e x) (e_eff, tm_type u2) ->
     typing g (Ts_Refine (denote_term t) e) (E_Total, tm_type u1)

  | T_PropIrrelevance:
     g:env -> 
     e:term_spec -> 
     t:term_spec ->
     e_eff:tot_or_ghost ->
     t_eff:tot_or_ghost ->
     typing g e (e_eff, t) ->
     typing g t (t_eff, tm_prop) ->
     typing g unit_exp (E_Total, t)
     
  | T_Sub:
     g:env ->
     e:term_spec ->
     c:comp_spec_typ ->
     c':comp_spec_typ ->
     typing g e c ->
     sub_comp g c c' ->
     typing g e c'

  | T_If: 
     g:env ->
     scrutinee:term ->
     then_:term ->
     else_:term ->
     ty:term ->
     u_ty:universe_spec ->
     hyp:var { None? (lookup_bvar g hyp) /\
               ~(hyp `Set.mem` (freevars_spec (denote_term then_) `Set.union` freevars_spec (denote_term else_))) } ->
     eff:tot_or_ghost ->
     ty_eff:tot_or_ghost ->
     typing g (denote_term scrutinee) (eff, bool_ty) ->
     typing (extend_env g hyp (eq2 u_zero bool_ty_tm scrutinee true_bool_tm)) (denote_term then_) (eff, denote_term ty) ->
     typing (extend_env g hyp (eq2 u_zero bool_ty_tm scrutinee false_bool_tm)) (denote_term else_) (eff, denote_term ty) ->
     typing g (denote_term ty) (ty_eff, tm_type u_ty) -> //typedness of ty cannot rely on hyp
     typing g (denote_term (mk_if scrutinee then_ else_)) (eff, denote_term ty)

  | T_Match:
     g:env ->
     sc_u : universe ->
     sc_ty : typ ->
     sc : term ->
     ty_eff:tot_or_ghost ->
     typing g (denote_term sc_ty) (ty_eff, tm_type (denote_universe sc_u)) ->
     eff:tot_or_ghost ->
     typing g (denote_term sc) (eff, denote_term sc_ty) ->
     branches:list (pattern_spec & term_spec) ->
     ty:comp_spec_typ ->
     bnds:list (list R.binding) ->
     complet : match_is_complete g (denote_term sc) (denote_term sc_ty) (List.Tot.map fst branches) bnds -> // complete patterns
     branches_typing g sc_u sc_ty sc ty branches bnds -> // each branch has proper type
     typing g (Ts_Match (denote_term sc) None branches) ty

and related : env -> term_spec -> relation -> term_spec -> Type0 =
  | Rel_refl:
    g:env ->
    t:term_spec ->
    rel:relation ->
    related g t rel t

  | Rel_sym:
    g:env ->
    t0:term_spec ->
    t1:term_spec ->
    related g t0 R_Eq t1 ->
    related g t1 R_Eq t0

  | Rel_trans:
    g:env ->
    t0:term_spec ->
    t1:term_spec ->
    t2:term_spec ->
    rel:relation ->
    related g t0 rel t1 ->
    related g t1 rel t2 ->
    related g t0 rel t2

  | Rel_univ:
    g:env ->
    u:universe_spec ->
    v:universe_spec ->
    univ_eq u v ->
    related g (tm_type u) R_Eq (tm_type v)

  | Rel_beta:
    g:env ->
    t:term_spec ->
    q:aqualv_spec ->
    e:term_spec { ln_spec' e 0 } ->
    arg:term_spec { ln_spec arg } ->
    related g (Ts_App (mk_abs t q e) arg q)
            R_Eq
            (subst_term_spec e [ DTs 0 arg ])

  | Rel_eq_token:
    g:env ->
    t0:term_spec ->
    t1:term_spec ->
    squash (equiv_token g t0 t1) ->
    related g t0 R_Eq t1

  | Rel_subtyping_token:
    g:env ->
    t0:term_spec ->
    t1:term_spec ->
    squash (subtyping_token g t0 t1) ->
    related g t0 R_Sub t1

  | Rel_equiv:
    g:env ->
    t0:term_spec ->
    t1:term_spec ->
    rel:relation ->
    related g t0 R_Eq t1 ->
    related g t0 rel t1

  | Rel_arrow:
    g:env ->
    t1:term ->
    t2:term ->
    q:aqualv_spec ->
    c1:comp_spec_typ ->
    c2:comp_spec_typ ->
    rel:relation ->
    x:var{
      None? (lookup_bvar g x) /\
      ~ (x `Set.mem` (freevars_comp_typ c1 `Set.union` freevars_comp_typ c2))
    } ->
    related g (denote_term t2) rel (denote_term t1) ->
    related_comp (extend_env g x t2)
                 (open_comp_typ c1 x)
                 rel
                 (open_comp_typ c2 x) ->
    related g (mk_arrow_ct (denote_term t1) q c1) rel (mk_arrow_ct (denote_term t2) q c2)

  | Rel_abs:
    g:env ->
    t1:term ->
    t2:term ->
    q:aqualv_spec ->
    e1:term_spec ->
    e2:term_spec ->
    x:var{
      None? (lookup_bvar g x) /\ ~ (x `Set.mem` (freevars_spec e1 `Set.union` freevars_spec e2))
    } ->
    related g (denote_term t1) R_Eq (denote_term t2) ->
    related (extend_env g x t1)
            (subst_term_spec e1 (open_with_var_spec x 0))
            R_Eq
            (subst_term_spec e2 (open_with_var_spec x 0)) ->
    related g (mk_abs (denote_term t1) q e1) R_Eq (mk_abs (denote_term t2) q e2)

  | Rel_ctxt:
    g:env ->
    t0:term_spec ->
    t1:term_spec ->
    ctxt:term_ctxt ->
    related g t0 R_Eq t1 ->
    related g (apply_term_ctxt ctxt t0) R_Eq (apply_term_ctxt ctxt t1)

and related_comp : env -> comp_spec_typ -> relation -> comp_spec_typ -> Type0 =
  | Relc_typ:
    g:env ->
    t0:term_spec ->
    t1:term_spec ->
    eff:tot_or_ghost ->
    rel:relation ->
    related g t0 rel t1 ->
    related_comp g (eff, t0) rel (eff, t1)
  
  | Relc_total_ghost:
    g:env ->
    t:term_spec ->
    related_comp g (E_Total, t) R_Sub (E_Ghost, t)

  | Relc_ghost_total:
    g:env ->
    t:term_spec ->
    non_informative g t ->
    related_comp g (E_Ghost, t) R_Sub (E_Total, t)

and branches_typing (g:env) (sc_u:universe) (sc_ty:typ) (sc:term) (rty:comp_spec_typ)
  : (brs:list (pattern_spec & term_spec)) -> (bnds : list (list R.binding)) -> Type0
=
  (* This judgement only enforces that branch_typing holds for every
  element of brs and its respective bnds (which must have the same
  length). *)

  | BT_Nil :
    branches_typing g sc_u sc_ty sc rty [] []

  | BT_S :

    br : (pattern_spec & term_spec) ->
    bnds : list R.binding ->
    pf : branch_typing g sc_u sc_ty sc rty br bnds ->

    rest_br : list (pattern_spec & term_spec) ->
    rest_bnds : list (list R.binding) ->
    rest : branches_typing g sc_u sc_ty sc rty rest_br rest_bnds ->
    branches_typing g sc_u sc_ty sc rty (br :: rest_br) (bnds :: rest_bnds)

and branch_typing (g:env) (sc_u:universe) (sc_ty:typ) (sc:term) (rty:comp_spec_typ)
  : (br : (pattern_spec & term_spec)) -> (bnds : list R.binding) -> Type0
=
  | BO :
    pat : pattern ->
    bnds : list R.binding{bindings_ok_for_pat g bnds pat} ->
    hyp_var:var{None? (lookup_bvar (extend_env_l g (refl_bindings_to_bindings bnds)) hyp_var)} ->

    body:term_spec ->

    _ : squash (Some? (elaborate_pat pat bnds)) ->

    typing (extend_env
            (extend_env_l g (refl_bindings_to_bindings bnds))
             hyp_var (eq2 sc_u sc_ty sc (fst (Some?.v (elaborate_pat pat bnds))))
           )
           body rty ->

    branch_typing g sc_u sc_ty sc rty
       (denote_pattern pat, close_term_bs_spec (refl_bindings_to_bindings bnds) body)
       bnds

and match_is_complete : env -> term_spec -> term_spec -> list pattern_spec -> list (list R.binding) -> Type0 =
  | MC_Tok :
    env:_ ->
    sc:_ ->
    ty:_ ->
    pats:_ ->
    bnds:_ ->
    squash (match_complete_token env sc ty pats bnds) -> match_is_complete env sc ty pats bnds

and sub_typing (g:env) (t1 t2:term_spec) = related g t1 R_Sub t2

and sub_comp (g:env) (c1 c2:comp_spec_typ) = related_comp g c1 R_Sub c2

and equiv (g:env) (t1 t2:term_spec) = related g t1 R_Eq t2

type tot_typing (g:env) (e:term_spec) (t:term_spec) = typing g e (E_Total, t)

type ghost_typing (g:env) (e:term_spec) (t:term_spec) = typing g e (E_Ghost, t)

val subtyping_token_renaming (g:env)
                             (bs0:bindings)
                             (bs1:bindings)
                             (x:var { None? (lookup_bvar (extend_env_l g (bs1@bs0)) x) })
                             (y:var { None? (lookup_bvar (extend_env_l g (bs1@bs0)) y) })
                             (t:term)
                             (t0 t1:term_spec)
                             (d:subtyping_token (extend_env_l g (bs1@(x,t)::bs0)) t0 t1)
  : GTot (subtyping_token (extend_env_l g (rename_bindings bs1 x y@(y,t)::bs0))
                      (rename_spec' t0 x y)
                      (rename_spec' t1 x y))

val subtyping_token_weakening (g:env)
                              (bs0:bindings)
                              (bs1:bindings)
                              (x:var { None? (lookup_bvar (extend_env_l g (bs1@bs0)) x) })
                              (t:term)
                              (t0 t1:term_spec)
                              (d:subtyping_token (extend_env_l g (bs1@bs0)) t0 t1)
  : GTot (subtyping_token (extend_env_l g (bs1@(x,t)::bs0)) t0 t1)

let simplify_umax (#g:R.env) (#t:term_spec) (#u:universe_spec)
                  (d:typing g t (E_Total, tm_type (u_max u u)))
   : typing g t (E_Total, tm_type u)
   = let ue
       : univ_eq (u_max u u) u
       = UN_MaxLeq u u (UNLEQ_Refl u)
     in
     let du : related g (tm_type (u_max u u)) R_Eq (tm_type u)
       = Rel_univ g (u_max u u) u ue in
     let du : related g (tm_type (u_max u u)) R_Sub (tm_type u)
       = Rel_equiv _ _ _ _ du in
     T_Sub _ _ _ _ d (Relc_typ _ _ _ E_Total _ du)

val well_typed_terms_are_ln (g:R.env) (e:term_spec) (c:comp_spec_typ) (_:typing g e c)
  : Lemma (ensures ln_spec e /\ ln_spec (snd c))

val type_correctness (g:R.env) (e:term_spec) (c:comp_spec_typ) (_:typing g e c)
  : GTot (u:universe_spec & typing g (snd c) (E_Total, tm_type u))

// this also requires x to be not in freevars e1 `Set.union` freevars e2
val equiv_arrow (#g:R.env) (#e1 #e2:term_spec) (ty:R.typ) (q:aqualv_spec)
  (x:var { None? (lookup_bvar g x) })
  (eq:equiv (extend_env g x ty)
            (subst_term_spec e1 (open_with_var_spec x 0))
            (subst_term_spec e2 (open_with_var_spec x 0)))
  : GTot (equiv g (mk_arrow (denote_term ty) q e1)
            (mk_arrow (denote_term ty) q e2))


// the proof for this requires e1 and e2 to be ln
val equiv_abs_close (#g:R.env) (#e1 #e2:term_spec) (ty:R.typ) (q:aqualv_spec)
  (x:var{None? (lookup_bvar g x)})
  (eq:equiv (extend_env g x ty) e1 e2)
  : GTot (equiv g (mk_abs (denote_term ty) q (subst_term_spec e1 [ NDs x 0 ]))
            (mk_abs (denote_term ty) q (subst_term_spec e2 [ NDs x 0 ])))

//
// Type of the top-level tactic that would splice-in the definitions
//

let fstar_env_fvs (g:R.env) =
  lookup_fvar g unit_fv == Some (tm_type_tm u_zero) /\
  lookup_fvar g bool_fv == Some (tm_type_tm u_zero) /\
  lookup_fvar g b2t_fv  == Some b2t_ty

type fstar_env = g:R.env{fstar_env_fvs g}

type fstar_top_env = g:fstar_env {
  forall x. None? (lookup_bvar g x )
}

open FStar.Nonempty

// Note: even though the sigelt_typing judgement takes a list of universe
// parameters, there is no way to exhibit typing judgements of terms
// containing universe variables yet (without invoking admit).
// TODO: expose push_univ_names/lookup_univ operations on environments, require
// them for universe names in typing judgements, and extend
// sigelt_has_type/dsl_tac_t with universe parameters.
noeq
type sigelt_typing : env -> sigelt -> Type0 =
  | ST_Let :
    g : env ->
    fv : R.fv ->
    us: list R.univ_name ->
    ty : R.typ ->
    tm : R.term ->
    nonempty (typing g (denote_term tm) (E_Total, denote_term ty)) ->
    sigelt_typing g (pack_sigelt (Sg_Let false [pack_lb ({ lb_fv = fv; lb_us = us; lb_typ = ty; lb_def = tm })]))

  | ST_Let_Opaque :
    g : env ->
    fv : R.fv ->
    us: list R.univ_name ->
    ty : R.typ ->
    (* no tm: only a proof of existence *)
    squash (exists (tm:R.term). nonempty (typing g (denote_term tm) (E_Total, denote_term ty))) ->
    sigelt_typing g (pack_sigelt (Sg_Let false [pack_lb ({ lb_fv = fv; lb_us = us; lb_typ = ty; lb_def = (`_) })]))

(**
 * The type of the top-level tactic that would splice-in the definitions.
 *
 * The tactic takes as input as type environment and an optional expected type
 *
 * It returns (sigelts_before, sigelt, sigelt_after)
 *   where sigelts_before and sigelt_after are list of sigelts
 *
 * All the returned sigelts indicate via a boolean flag whether they are well-typed,
 *   in the judgment above
 *
 * If the flag is not set, F* typechecker typechecks the returned sigelts
 *
 * The sigelt in the middle, if well-typed, has the input expected type
 *
 * In addition, each sigelt can have a 'blob' attached with a given name.
 * The blob can be used later, e.g., during extraction, and passed back to the
 * extension to perform additional processing.
 *
 * The blob is stored in the sigmeta_extension_data field of the enclosing sigelt.
 *)

let blob = string & R.term

//
// t is the optional expected type
//
let sigelt_has_type (s:R.sigelt) (t:option R.term) : prop =
  let open R in
  match t with
  | None -> True
  | Some t ->
    match inspect_sigelt s with
    | Sg_Let false [lb] -> begin
      let {lb_typ} = inspect_lb lb in
      lb_typ == t
    end

    | _ -> False

//
// If checked is true, this sigelt is properly typed for the environment
// If not, we don't know and let F* re-typecheck the sigelt.
//

let sigelt_for (g:env) (t:option R.typ) =
  tup:(bool & sigelt & option blob) {
    let (checked, se, _) = tup in
    checked ==> (nonempty (sigelt_typing g se) /\ sigelt_has_type se t)
  }

//
// sigelts_before, sigelt, sigelts_after
//
let dsl_tac_result_t (g:env) (t:option R.typ) =
  list (sigelt_for g None) &
  (sigelt_for g t) &
  list (sigelt_for g None)

//
// The input option R.typ is the expected type
//
type dsl_tac_t =
  gt:(fstar_top_env & option R.typ) ->
  Tac (dsl_tac_result_t (fst gt) (snd gt))

val if_complete_match (g:env) (t:term_spec)
  : GTot (match_complete_token g t bool_ty [
       Ps_Constant C_True;
       Ps_Constant C_False;
    ] [[]; []])

// Derived rule for if

val mkif
    (g:fstar_env)
    (scrutinee:term)
    (then_:term)
    (else_:term)
    (ty:term)
    (u_ty:universe_spec)
    (hyp:var { None? (lookup_bvar g hyp) /\
               ~(hyp `Set.mem` (freevars_spec (denote_term then_) `Set.union` freevars_spec (denote_term else_))) })
    (eff:tot_or_ghost)
    (ty_eff:tot_or_ghost)
    (ts : typing g (denote_term scrutinee) (eff, bool_ty))
    (tt : typing (extend_env g hyp (eq2 u_zero bool_ty_tm scrutinee true_bool_tm)) (denote_term then_) (eff, denote_term ty))
    (te : typing (extend_env g hyp (eq2 u_zero bool_ty_tm scrutinee false_bool_tm)) (denote_term else_) (eff, denote_term ty))
    (tr : typing g (denote_term ty) (ty_eff, tm_type u_ty))
: typing g (denote_term (mk_if scrutinee then_ else_)) (eff, denote_term ty)

(* Helper to return a single let definition in a splice_t tactic. *)
let mk_checked_let (g:R.env) (cur_module:name) (nm:string) (tm:R.term) (ty:R.typ{nonempty (typing g (denote_term tm) (E_Total, denote_term ty))})
  : sigelt_for g (Some ty) =
  let fv = pack_fv (cur_module @ [nm]) in
  let lb = R.pack_lb ({ lb_fv = fv; lb_us = []; lb_typ = ty; lb_def = tm }) in
  let se = R.pack_sigelt (R.Sg_Let false [lb]) in
  nonempty_intro (ST_Let g fv [] ty tm () <: sigelt_typing g se);
  ( true, se, None )

let mk_unchecked_let (g:R.env) (cur_module:name) (nm:string) (tm:R.term) (ty:R.typ)
  : bool & sigelt & option blob =
  let fv = pack_fv (cur_module @ [nm]) in
  let lb = R.pack_lb ({ lb_fv = fv; lb_us = []; lb_typ = ty; lb_def = tm }) in
  let se = R.pack_sigelt (R.Sg_Let false [lb]) in
  ( false, se, None )

(* Turn a typing derivation into a token. This is useful
to call primitives that require a proof of typing, like
`call_subtac`, since they do not take derivations nor can
they even be mentioned in that module due to dependencies.
Probably the right thing to do is refactor and avoid this, though. *)
val typing_to_token (#g:env) (#e:term_spec) (#c:comp_spec_typ)
  : typing g e c -> GTot (typing_token g e c)
