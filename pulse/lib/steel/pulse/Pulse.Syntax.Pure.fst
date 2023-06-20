module Pulse.Syntax.Pure

module R = FStar.Reflection
module T = FStar.Tactics
module RT = FStar.Reflection.Typing

open Pulse.Syntax.Base
open Pulse.Elaborate.Pure
open Pulse.Readback
open Pulse.Reflection.Util

let (let?) (f:option 'a) (g:'a -> option 'b) : option 'b =
  match f with
  | None -> None
  | Some x -> g x

let u0 : universe = R.pack_universe R.Uv_Zero
let u1 : universe = R.pack_universe (R.Uv_Succ u0)
let u2 : universe = R.pack_universe (R.Uv_Succ u1)

let u_zero = u0
let u_succ (u:universe) : universe =
  R.pack_universe (R.Uv_Succ u)
let u_var (s:string) : universe =
  R.pack_universe (R.Uv_Name (s, FStar.Range.range_0)) 
let u_max (u0 u1:universe) : universe =
  R.pack_universe (R.Uv_Max [u0; u1])
let u_unknown : universe = R.pack_universe R.Uv_Unk

let tm_bvar (bv:bv) : term =
  tm_fstar (R.pack_ln (R.Tv_BVar (R.pack_bv (RT.make_bv_with_name bv.bv_ppname.name bv.bv_index))))
            bv.bv_ppname.range

let tm_var (nm:nm) : term =
  tm_fstar (R.pack_ln (R.Tv_Var (R.pack_bv (RT.make_bv_with_name nm.nm_ppname.name nm.nm_index))))
           nm.nm_ppname.range

let tm_fvar (l:fv) : term =
  tm_fstar (R.pack_ln (R.Tv_FVar (R.pack_fv l.fv_name)))
           l.fv_range

let tm_uinst (l:fv) (us:list universe) : term =
  tm_fstar (R.pack_ln (R.Tv_UInst (R.pack_fv l.fv_name) us))
           l.fv_range

let tm_constant (c:constant) : term =
  tm_fstar (R.pack_ln (R.Tv_Const c)) FStar.Range.range_0

let tm_refine (b:binder) (t:term) : term =
  tm_fstar (R.pack_ln (R.Tv_Refine (R.pack_bv (RT.make_bv_with_name b.binder_ppname.name 0))
                                   (elab_term b.binder_ty)
                                   (elab_term t)))
           FStar.Range.range_0

let tm_let (t e1 e2:term) : term =
  tm_fstar (R.pack_ln (R.Tv_Let false
                                []
                                (R.pack_bv (RT.make_bv 0))
                                (elab_term t)
                                (elab_term e1)
                                (elab_term e2)))
           FStar.Range.range_0

let tm_pureapp (head:term) (q:option qualifier) (arg:term) : term =
  tm_fstar (R.mk_app (elab_term head) [(elab_term arg, elab_qual q)])
           FStar.Range.range_0

let tm_arrow (b:binder) (q:option qualifier) (c:comp) : term =
  tm_fstar (mk_arrow_with_name b.binder_ppname.name (elab_term b.binder_ty, elab_qual q)
                                                    (elab_comp c))
           FStar.Range.range_0

let tm_type (u:universe) : term =
  tm_fstar (R.pack_ln (R.Tv_Type u)) FStar.Range.range_0

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

let is_var (t:term) : option nm =
  let open R in
  match t.t with
  | Tm_FStar host_term ->
    begin match R.inspect_ln host_term with
          | R.Tv_Var bv ->
            let bv_view = R.inspect_bv bv in
            Some {nm_index=bv_view.bv_index;
                  nm_ppname=mk_ppname (bv_view.bv_ppname) t.range}
          | _ -> None
    end
  | _ -> None


let is_fvar (t:term) : option (R.name & list universe) =
  let open R in
  match t.t with
  | Tm_FStar host_term ->
    begin match inspect_ln host_term with
          | Tv_FVar fv -> Some (inspect_fv fv, [])
          | Tv_UInst fv us -> Some (inspect_fv fv, us)
          | _ -> None
    end
  | _ -> None

let is_pure_app (t:term) : option (term & option qualifier & term) =
  match t.t with
  | Tm_FStar host_term ->
    begin match R.inspect_ln host_term with
          | R.Tv_App hd (arg, q) ->
            let? hd =
              match readback_ty hd with
              | Some hd -> Some hd <: option term
              | _ -> None in
            let q = readback_qual q in
            let? arg =
              match readback_ty arg with
              | Some arg -> Some arg <: option term
              | _ -> None in
            Some (hd, q, arg)
          | _ -> None
    end
  | _ -> None

let leftmost_head (t:term) : option term =
  match t.t with
  | Tm_FStar host_term ->
    let hd, _ = R.collect_app_ln host_term in
    (match readback_ty hd with
     | Some t -> Some t
     | None -> None)
  | _ -> None

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

    // | Tm_PureApp head q arg ->
    //   begin match is_fvar head with
    //         | Some (l, us) -> Some (l, us, q, Some arg)
    //         | None -> None
    //   end
    // | _ -> None

let is_arrow (t:term) : option (binder & option qualifier & comp) =
  match t.t with
  | Tm_FStar host_term ->
    begin match R.inspect_ln host_term with
          | R.Tv_Arrow b c ->
            let {binder_bv;binder_qual;binder_sort} =
              R.inspect_binder b in
            begin match binder_qual with
                  | R.Q_Meta _ -> None
                  | _ ->
                    let q = readback_qual binder_qual in
                    let bv_view = R.inspect_bv binder_bv in
                    let c_view = R.inspect_comp c in
                    begin match c_view with
                          | R.C_Total c_t ->
                            let? binder_ty = readback_ty binder_sort in
                            let? c =
                              match readback_comp c_t with
                              | Some c -> Some c <: option Pulse.Syntax.Base.comp
                              | None -> None in
                            Some ({binder_ty;
                                   binder_ppname=mk_ppname (bv_view.bv_ppname) (T.range_of_term host_term)},
                                  q,
                                  c)
                          | _ -> None
                    end
            end
          
          | _ -> None
    end
  | _ -> None

// TODO: write it better, with pattern matching on reflection syntax
let is_eq2 (t:term) : option (term & term) =
  match is_pure_app t with
  | Some (head, None, a2) ->
    (match is_pure_app head with
     | Some (head, None, a1) ->
       (match is_pure_app head with
        | Some (head, Some Implicit, _) ->
          (match is_fvar head with
           | Some (l, _) ->
             if l = ["Pulse"; "Steel"; "Wrapper"; "eq2_prop"] ||
                l = ["Prims"; "eq2"]
             then Some (a1, a2)
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
        | Some (l, []) ->
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

