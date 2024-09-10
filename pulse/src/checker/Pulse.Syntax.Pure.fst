(*
   Copyright 2023 Microsoft Research

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

module Pulse.Syntax.Pure

module R = FStar.Reflection.V2
module T = FStar.Tactics.V2
module RT = FStar.Reflection.Typing

open Pulse.Syntax.Base
open Pulse.Readback
open Pulse.Elaborate.Pure
open Pulse.Reflection.Util
open Pulse.RuntimeUtils

let (let?) (f:option 'a) (g:'a -> option 'b) : option 'b =
  match f with
  | None -> None
  | Some x -> g x

let u0 : universe = R.pack_universe R.Uv_Zero
let u1 : universe = R.pack_universe (R.Uv_Succ u0)
let u2 : universe = R.pack_universe (R.Uv_Succ u1)

let u_zero = u0
let u_one = u1
let u_succ (u:universe) : universe =
  R.pack_universe (R.Uv_Succ u)
let u_var (s:string) : universe =
  R.pack_universe (R.Uv_Name (R.pack_ident (s, FStar.Range.range_0)))
let u_max (u0 u1:universe) : universe =
  R.pack_universe (R.Uv_Max [u0; u1])
let u_unknown : universe = R.pack_universe R.Uv_Unk

let tm_bvar (bv:bv) : term =
  set_range (R.pack_ln (R.Tv_BVar (R.pack_bv (RT.make_bv_with_name bv.bv_ppname.name bv.bv_index))))
            bv.bv_ppname.range

let tm_var (nm:nm) : term =
  set_range (R.pack_ln (R.Tv_Var (R.pack_namedv (RT.make_namedv_with_name nm.nm_ppname.name nm.nm_index))))
            nm.nm_ppname.range

let tm_fvar (l:fv) : term =
  set_range (R.pack_ln (R.Tv_FVar (R.pack_fv l.fv_name)))
            l.fv_range

let tm_uinst (l:fv) (us:list universe) : term =
  set_range (R.pack_ln (R.Tv_UInst (R.pack_fv l.fv_name) us))
            l.fv_range

let tm_constant (c:constant) : term =
  R.pack_ln (R.Tv_Const c)

let tm_refine (b:binder) (t:term) rng : term =
  let rb : R.simple_binder = RT.mk_simple_binder b.binder_ppname.name b.binder_ty in
  set_range (R.pack_ln (R.Tv_Refine rb t))
            rng

let tm_let (t e1 e2:term) rng : term =
  let rb : R.simple_binder = RT.mk_simple_binder RT.pp_name_default t in
  set_range (R.pack_ln (R.Tv_Let false
                                 []
                                 rb
                                 e1
                                 e2))
           rng

let tm_pureapp (head:term) (q:option qualifier) (arg:term) : term =
  set_range (R.mk_app head [(arg, elab_qual q)])
            (union_ranges (range_of_term head) (range_of_term arg))

let tm_pureabs (ppname:R.ppname_t) (ty : term) (q : option qualifier) (body:term) rng : term =
  let open R in
  let open T in
  let b : T.binder = {
      uniq = 0;
      ppname = ppname;
      sort = ty;
      qual = elab_qual q;
      attrs = [];
  }
  in
  let r = pack (Tv_Abs b body) in
  assume (~(R.Tv_Unknown? (R.inspect_ln r))); // NamedView API doesn't ensure this, it should
  set_range r rng

let tm_arrow (b:binder) (q:option qualifier) (c:comp) : term =
  set_range (mk_arrow_with_name b.binder_ppname.name (b.binder_ty, elab_qual q)
                                                     (elab_comp c))
            (union_ranges (range_of_term b.binder_ty) (range_of_comp c))

let tm_type (u:universe) : term = RT.tm_type u

let mk_bvar (s:string) (r:Range.range) (i:index) : term =
  tm_bvar {bv_index=i;bv_ppname=mk_ppname (RT.seal_pp_name s) r}

let null_var (v:var) : term =
  tm_var {nm_index=v;nm_ppname=ppname_default}

let null_bvar (i:index) : term =
  tm_bvar {bv_index=i;bv_ppname=ppname_default}

let term_of_nvar (x:nvar) : term =
  tm_var { nm_index=snd x; nm_ppname=fst x}
let term_of_no_name_var (x:var) : term =
  term_of_nvar (v_as_nv x)

let is_bvar (t:term) : option nat =
  let open R in
  match R.inspect_ln t with
  | R.Tv_BVar bv ->
    let bv_view = R.inspect_bv bv in
    Some bv_view.index
  | _ -> None

let is_var (t:term) : option nm =
  let open R in
  match R.inspect_ln t with
  | R.Tv_Var nv ->
    let nv_view = R.inspect_namedv nv in
    Some {nm_index=nv_view.uniq;
          nm_ppname=mk_ppname (nv_view.ppname) (range_of_term t)}
  | _ -> None


let is_fvar (t:term) : option (R.name & list universe) =
  let open R in
  match inspect_ln t with
  | Tv_FVar fv -> Some (inspect_fv fv, [])
  | Tv_UInst fv us -> Some (inspect_fv fv, us)
  | _ -> None

let readback_qual = function
  | R.Q_Implicit -> Some Implicit
  | _ -> None

let is_pure_app (t:term) : option (term & option qualifier & term) =
  match R.inspect_ln t with
  | R.Tv_App hd (arg, q) ->
    let q = readback_qual q in
    Some (hd, q, arg)
  | _ -> None

let leftmost_head (t:term) : option term =
  let hd, _ = R.collect_app_ln t in
  Some hd

let is_fvar_app (t:term) : option (R.name &
                                   list universe &
                                   option qualifier &
                                   option term) =
  match is_fvar t with
  | Some (l, us) -> Some (l, us, None, None)
  | None ->
    match is_pure_app t with
    | Some (head, q, arg) ->
      (match is_fvar head with
       | Some (l, us) -> Some (l, us, q, Some arg)
       | None -> None)
    | _ -> None

let is_arrow (t:term) : option (binder & option qualifier & comp) =
  match R.inspect_ln_unascribe t with
  | R.Tv_Arrow b c ->
    let {ppname;qual;sort} = R.inspect_binder b in
    begin match qual with
          | R.Q_Meta _ -> None
          | _ ->
            let q = readback_qual qual in
            let c_view = R.inspect_comp c in
            let ret (c_t:R.typ) =
              let binder_ty = sort in
              let? c =
                match readback_comp c_t with
                | Some c -> Some c <: option Pulse.Syntax.Base.comp
                | None -> None in
              Some (mk_binder_ppname
                      binder_ty
                      (mk_ppname ppname (T.range_of_term t)),
                      q,
                      c) in
                      
            begin match c_view with
            | R.C_Total c_t -> ret c_t
            | R.C_Eff _ eff_name c_t _ _ ->
              //
              // Consider Tot effect with decreases also
              //
              if eff_name = tot_lid
              then ret c_t
              else None
            | _ -> None
            end
    end
          
  | _ -> None

// TODO: write it better, with pattern matching on reflection syntax
let is_eq2 (t:term) : option (term & term & term) =
  match is_pure_app t with
  | Some (head, None, a2) ->
    (match is_pure_app head with
     | Some (head, None, a1) ->
       (match is_pure_app head with
        | Some (head, Some Implicit, ty) ->
          (match is_fvar head with
           | Some (l, _) ->
             if l = ["Pulse"; "Steel"; "Wrapper"; "eq2_prop"] ||
                l = ["Prims"; "eq2"]
             then Some (ty, a1, a2)
             else None
           | _ -> None)
        | _ -> None)
     | _ -> None)
  | _ -> None

let unreveal (t:term) : option term =
  match is_pure_app t with
  | Some (head, None, arg) ->
    (match is_pure_app head with
     | Some (head, Some Implicit, _) ->
       (match is_fvar head with
        | Some (l, _) ->
          if l = ["FStar"; "Ghost"; "reveal"]
          then Some arg
          else None
        | _ -> None)
     | _ -> None)
  | _ -> None

let is_arrow_tm_arrow (t:term)
  : Lemma (requires Some? (is_arrow t))
          (ensures (let Some (b, q, c) = is_arrow t in
                    t == tm_arrow b q c)) =
  admit ()

let is_fvar_app_tm_app (t:term)
  : Lemma (requires Some? (is_fvar_app t))
          (ensures (let Some (l, us, q_opt, arg_opt) = is_fvar_app t in
                    match us, arg_opt with
                    | [], None -> t == tm_fvar (as_fv l)
                    | [], Some arg -> t == tm_pureapp (tm_fvar (as_fv l)) q_opt arg
                    | us, None -> t == tm_uinst (as_fv l) us
                    | us, Some arg ->
                      t == tm_pureapp (tm_uinst (as_fv l) us) q_opt arg)) =
  admit ()

let mk_squash (u:universe) (t:term) : term =
  tm_pureapp (tm_uinst (as_fv R.squash_qn) [u]) None t

//
// A separation logic specific view of pure F* terms
// The inspect_term API returns a view,
//   where Tm_FStar is the catch all case
// See also the is_view_of predicate below
//
[@@ no_auto_projectors]
noeq
type term_view =
  | Tm_Emp        : term_view
  | Tm_Pure       : p:term -> term_view
  | Tm_Star       : l:slprop -> r:slprop -> term_view
  | Tm_ExistsSL   : u:universe -> b:binder -> body:slprop -> term_view
  | Tm_ForallSL   : u:universe -> b:binder -> body:slprop -> term_view
  | Tm_SLProp     : term_view
  | Tm_Inv        : iname:term -> p:slprop -> term_view
  | Tm_Inames     : term_view  // type inames
  | Tm_EmpInames  : term_view
  | Tm_Unknown    : term_view
  | Tm_FStar      : term -> term_view  // catch all

let wr (t:term) (r:range) : term = set_range t r

let pack_term_view (top:term_view) (r:range)
  : term
  = let open R in
    let w t' = wr t' r in
    match top with
    | Tm_SLProp ->
      w (pack_ln (Tv_FVar (pack_fv slprop_lid)))

    | Tm_Emp ->
      w (pack_ln (Tv_FVar (pack_fv emp_lid)))
      
    | Tm_Inv i p ->
      let head = pack_ln (Tv_FVar (pack_fv inv_lid)) in
      let t = pack_ln (Tv_App head (i, Q_Explicit)) in
      pack_ln (Tv_App t (p, Q_Explicit))

    | Tm_Pure p ->
      let head = pack_ln (Tv_FVar (pack_fv pure_lid)) in
      w (pack_ln (Tv_App head (p, Q_Explicit)))

    | Tm_Star l r ->
      w (mk_star l r)
      
    | Tm_ExistsSL u b body
    | Tm_ForallSL u b body ->
      let t = set_range_of b.binder_ty b.binder_ppname.range in
      let abs = mk_abs_with_name_and_range b.binder_ppname.name b.binder_ppname.range t R.Q_Explicit body in
      if Tm_ExistsSL? top
      then w (mk_exists u t abs)
      else w (mk_forall u t abs)

    | Tm_Inames ->
      w (pack_ln (Tv_FVar (pack_fv inames_lid)))

    | Tm_EmpInames ->
      w (pack_ln (Tv_FVar (pack_fv emp_inames_lid)))

    | Tm_Unknown ->
      w (pack_ln R.Tv_Unknown)

    | Tm_FStar t -> w t

let term_range (t:term) = range_of_term t
let pack_term_view_wr (t:term_view) (r:range) = pack_term_view t r
let tm_slprop = pack_term_view_wr Tm_SLProp FStar.Range.range_0
let tm_inames = pack_term_view_wr Tm_Inames FStar.Range.range_0
let tm_emp = pack_term_view_wr Tm_Emp FStar.Range.range_0
let tm_emp_inames = pack_term_view_wr Tm_EmpInames FStar.Range.range_0
let tm_unknown = pack_term_view_wr Tm_Unknown FStar.Range.range_0
let tm_pure (p:term) : term = pack_term_view (Tm_Pure p) (range_of_term p)
let tm_star (l:slprop) (r:slprop) : term =
  pack_term_view (Tm_Star l r)
                 (union_ranges (range_of_term l) (range_of_term r))
let tm_exists_sl (u:universe) (b:binder) (body:slprop) : term =
  pack_term_view (Tm_ExistsSL u b body)
                 (union_ranges (range_of_term b.binder_ty) (range_of_term body))
let tm_forall_sl (u:universe) (b:binder) (body:slprop) : term =
  pack_term_view (Tm_ForallSL u b body)
                 (union_ranges (range_of_term b.binder_ty) (range_of_term body))
let tm_iname = tm_fvar (as_fv iname_lid)
let tm_inv (i p:term) : term =
  pack_term_view (Tm_Inv i p)
                 (union_ranges (range_of_term i) (range_of_term p))
let tm_all_inames = tm_fvar (as_fv all_inames_lid)
let tm_add_inv (is iname:R.term) : R.term =
  let h = R.pack_ln (R.Tv_FVar (R.pack_fv add_inv_lid)) in
  R.mk_app h [ex is; ex iname]
let tm_full_perm = tm_constant (R.C_Real "1.0")


let is_view_of (tv:term_view) (t:term) : prop =
  match tv with
  | Tm_Emp -> t == tm_emp
  | Tm_SLProp -> t == tm_slprop
  | Tm_Inames -> t == tm_inames
  | Tm_EmpInames -> t == tm_emp_inames
  | Tm_Star t1 t2 ->
    t == tm_star t1 t2 /\
    t1 << t /\ t2 << t
  | Tm_ExistsSL u b body ->
    t == tm_exists_sl u b body /\
    u << t /\ b << t /\ body << t
  | Tm_ForallSL u b body ->
    t == tm_forall_sl u b body /\
    u << t /\ b << t /\ body << t
  | Tm_Pure p ->
    t == tm_pure p /\
    p << t
  | Tm_Inv i p ->
    t == tm_inv i p /\
    i << t /\ p << t
  | Tm_Unknown -> t == tm_unknown
  | Tm_FStar t' -> t' == t

let rec inspect_term (t:R.term)
  : (tv:term_view { tv `is_view_of` t }) =

  let open R in
  let open Pulse.Syntax.Base in

  let default_view = Tm_FStar t in

  pack_inspect_inv t;

  match inspect_ln t with
  | Tv_FVar fv ->
    let fv_lid = inspect_fv fv in
    if fv_lid = slprop_lid
    then Tm_SLProp
    else if fv_lid = emp_lid
    then Tm_Emp
    else if fv_lid = inames_lid
    then Tm_Inames
    else if fv_lid = emp_inames_lid
    then Tm_EmpInames
    else default_view

  | Tv_App hd (a, q) ->
    admit(); //this case doesn't work because it is using collect_app_ln, etc.
    let head, args = collect_app_ln t in
    begin
      match inspect_ln head, args with
      | Tv_FVar fv, [a1; a2] ->
        if inspect_fv fv = star_lid
        then Tm_Star (fst a1) (fst a2)
        else if inspect_fv fv = inv_lid
        then Tm_Inv (fst a1) (fst a2)
        else default_view
      | Tv_UInst fv [u], [a1; a2] ->
        if inspect_fv fv = exists_lid ||
           inspect_fv fv = forall_lid
        then (
          let t1 : R.term = fst a1 in
          let t2 : R.term = fst a2 in
          match inspect_ln t2 with
          | Tv_Abs b body ->
            let bview = inspect_binder b in
            let b = mk_binder_ppname t1 (mk_ppname bview.ppname (binder_range b)) in
            if inspect_fv fv = exists_lid
            then Tm_ExistsSL u b body
            else Tm_ForallSL u b body
          | _ -> default_view
        )
        else default_view
     | Tv_FVar fv, [a] ->
        if inspect_fv fv = pure_lid
        then Tm_Pure (fst a)
        else default_view
     | _ -> default_view
    end

  | Tv_Refine _ _
  | Tv_Arrow _ _
  | Tv_Type _
  | Tv_Const _
  | Tv_Let _ _ _ _ _
  | Tv_Var _
  | Tv_BVar _
  | Tv_UInst _ _
  | Tv_Match _ _ _
  | Tv_Abs _ _ -> default_view

  | Tv_AscribedT t _ _ _
  | Tv_AscribedC t _ _ _ ->
    //this case doesn't work because it is unascribing
    admit();
    inspect_term t

  | Tv_Uvar _ _ -> default_view
  
  | Tv_Unknown -> Tm_Unknown

  | Tv_Unsupp -> default_view

let rec slprop_as_list (vp:term)
  : list term
  = match inspect_term vp with
    | Tm_Emp -> []
    | Tm_Star vp0 vp1 ->
      slprop_as_list vp0 @ slprop_as_list vp1
    | _ -> [vp]

let rec list_as_slprop (vps:list term)
  : term
  = match vps with
    | [] -> tm_emp
    | [hd] -> hd
    | hd::tl -> tm_star hd (list_as_slprop tl)

let rec insert1 (t:term) (ts : list term) : T.Tac (list term) =
  match ts with
  | [] -> [t]
  | t'::ts' ->
    if Order.le (T.compare_term t t')
    then t::ts
    else t'::insert1 t ts'

let sort_terms (ts : list term) : T.Tac (list term) =
  T.fold_right insert1 ts []

(* This does not have any useful lemmas, but can put the terms
in order. It's useful to pretty-print contexts. See #96. *)
let canon_slprop_list_print (vs : list term)
  : T.Tac term
  = list_as_slprop <| sort_terms vs

let canon_slprop_print (vp:term)
  : T.Tac term
  = canon_slprop_list_print <| slprop_as_list vp
