module Pulse.Syntax.Util

module R = FStar.Reflection

open Pulse.Syntax.Base
open Pulse.Syntax.Naming
open Pulse.Elaborate.Pure
open Pulse.Readback

let (let?) (f:option 'a) (g:'a -> option 'b) : option 'b =
  match f with
  | None -> None
  | Some x -> g x

let is_var (t:term) : option nm =
  let open R in
  match t with
  | Tm_FStar host_term r ->
    begin match R.inspect_ln host_term with
          | R.Tv_Var bv ->
            let bv_view = R.inspect_bv bv in
            Some {nm_index=bv_view.bv_index;
                  nm_ppname=bv_view.bv_ppname;
                  nm_range=r}
          | _ -> None
    end
  | _ -> None


let is_fvar (t:term) : option (R.name & list universe) =
  let open R in
  match t with
  | Tm_FStar host_term _ ->
    begin match inspect_ln host_term with
          | Tv_FVar fv -> Some (inspect_fv fv, [])
          | Tv_UInst fv us -> Some (inspect_fv fv, us)
          | _ -> None
    end
  | _ -> None

let is_fvar_app (t:term) : option (R.name &
                                   list universe &
                                   option qualifier &
                                   option term) =
  match is_fvar t with
  | Some (l, us) -> Some (l, us, None, None)
  | None ->
    match t with
    | Tm_PureApp head q arg ->
      begin match is_fvar head with
            | Some (l, us) -> Some (l, us, q, Some arg)
            | None -> None
      end
    | _ -> None

let is_arrow (t:term) : option (binder & option qualifier & comp) =
  match t with
  | Tm_FStar host_term _ ->
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
                                   binder_ppname=bv_view.bv_ppname},
                                  q,
                                  c)
                          | _ -> None
                    end
            end
          
          | _ -> None
    end
  | _ -> None

let is_embedded_uvar (t:term) : option nat =
  match is_fvar t with
  | Some (l, [u]) ->
    if l = embedded_uvar_lid
    then begin match R.inspect_universe u with
               | R.Uv_BVar n -> Some n
               | _ -> None
         end
    else None
  | _ -> None
