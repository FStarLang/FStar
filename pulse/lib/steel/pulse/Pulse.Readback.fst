module Pulse.Readback
module R = FStar.Reflection
open Pulse.Syntax.Base
open Pulse.Reflection.Util

let (let?) (f:option 'a) (g:'a -> option 'b) : option 'b =
  match f with
  | None -> None
  | Some x -> g x


#push-options "--z3rlimit_factor 20"
// TODO: FIXME: may be mark as opaque_to_smt
let try_readback_st_comp
  (t:R.term)
  (readback_ty:(t':R.term ->
                option (ty:term { elab_term ty == t' })))

  : option (c:comp{elab_comp c == t}) =

  let open R in
  let hd, args = collect_app_ln t in
  match inspect_ln hd with
  | Tv_UInst fv [u] ->
    let fv_lid = inspect_fv fv in
    if fv_lid = stt_lid
    then match args with
         | [res; pre; post] ->
           (match inspect_ln (fst post) with
            | Tv_Abs b body ->
              let { binder_bv=bv; binder_qual=aq; binder_attrs=attrs; binder_sort=sort } =
                  inspect_binder b
              in    
              let bv_view = inspect_bv bv in
              assume (fv == stt_fv);
              assume (aq == Q_Explicit           /\
                      attrs == []                /\
                      bv_view.bv_index == 0      /\
                      sort == fst res /\
                      snd res == Q_Explicit      /\
                      snd pre == Q_Explicit      /\
                      snd post == Q_Explicit);

              assume (t == mk_stt_comp u (fst res) (fst pre) (mk_abs (fst res) R.Q_Explicit body));
              let? res' = readback_ty (fst res) in
              let? pre' = readback_ty (fst pre) in
              let? post' = readback_ty body in
              let c = C_ST {u; res=res'; pre=pre';post=post'} in
              Some (c <: c:Pulse.Syntax.Base.comp{ elab_comp c == t })
            | _ -> None)
         | _ -> None
    else if fv_lid = stt_atomic_lid || fv_lid = stt_ghost_lid
    then match args with
         | [res; opened; pre; post] ->
           (match inspect_ln (fst post) with
            | Tv_Abs b body ->
              let { binder_bv=bv; binder_qual=aq; binder_attrs=attrs }
                  = inspect_binder b
              in    
              let bv_view = inspect_bv bv in
              let? res' = readback_ty (fst res) in
              let? opened' = readback_ty (fst opened) in
              let? pre' = readback_ty (fst pre) in
              let? post' = readback_ty body in
              if fv_lid = stt_atomic_lid
              then begin
                assume (t == mk_stt_atomic_comp u (fst res) (fst opened) (fst pre) (mk_abs (fst res) R.Q_Explicit body));
                let c = C_STAtomic opened' ({u; res=res'; pre=pre';post=post'}) in
                Some (c <: c:Pulse.Syntax.Base.comp { elab_comp c == t })
              end
              else begin
                assume (t == mk_stt_ghost_comp u (fst res) (fst opened) (fst pre) (mk_abs (fst res) R.Q_Explicit body));
                let c = C_STGhost opened' ({u; res=res'; pre=pre';post=post'}) in
                Some (c <: c:Pulse.Syntax.Base.comp { elab_comp c == t })
              end
            | _ -> None)
         | _ -> None
    else None  
  | _ -> None
#pop-options

let readback_qual = function
  | R.Q_Implicit -> Some Implicit
  | _ -> None

#push-options "--admit_smt_queries true"
let collect_app_refined (t:R.term) : tuple2 (t':R.term{t' << t})
                                            (list (a:R.argv{a << t})) =
  R.collect_app_ln t

let readback_ty_ascribed (t:R.term { let t = R.inspect_ln t in
                                     R.Tv_AscribedT? t || R.Tv_AscribedC? t })
  : option (ty:term { elab_term ty == t }) =
  match R.inspect_ln t with
  //
  // The following is dropping the ascription, which is not ideal
  // However, if we don't, then ascriptions start to come in the way of
  //   R.term_eq used to decide equality of Tm_FStar terms,
  //   which then results in framing failures
  //
  // At least in the examples it came up, the ascription was a redundant
  //   ascription on F* Tm_Match
  //   I tried an F* patch that did not add the ascription, if it was already
  //   ascribed, but that failed a couple of proofs in HACL* : (
  //
  | R.Tv_AscribedT t _ _ _
  | R.Tv_AscribedC t _ _ _ -> Some (Tm_FStar t (R.range_of_term t))
#pop-options

let rec readback_ty (t:R.term)
  : option (ty:term { elab_term ty == t }) =

  let open R in
  let open Pulse.Syntax.Base in
  
  match inspect_ln t with
  | Tv_FVar fv ->
    let fv_lid = inspect_fv fv in
    if fv_lid = vprop_lid
    then Some Tm_VProp
    else if fv_lid = emp_lid
    then Some Tm_Emp
    else if fv_lid = inames_lid
    then Some Tm_Inames
    else if fv_lid = emp_inames_lid
    then Some Tm_EmpInames
    else Some (Tm_FStar t (range_of_term t))

  | Tv_App hd (a, q) -> 
    let aux () = 
      match q with
      | R.Q_Meta _ -> None
      | _ -> Some (Tm_FStar t (range_of_term t))
    in
    let head, args = collect_app_refined t in
    begin
    match inspect_ln head, args with
    | Tv_FVar fv, [(a1, _); (a2, _)] ->
      if inspect_fv fv = star_lid
      then (
        let? t1 = readback_ty a1 in
        let? t2 = readback_ty a2 in
        Some (Tm_Star t1 t2)
      )
      else aux ()
    | Tv_UInst fv [u], [(a1, _); (a2, _)] ->
      if inspect_fv fv = exists_lid ||
         inspect_fv fv = forall_lid
      then (
        let? ty = readback_ty a1 in
        let? (ppname, p) =
          match inspect_ln a2 with
          | Tv_Abs b body ->
            let? p = readback_ty body in
            let b = inspect_binder b in
            let bv = inspect_bv b.binder_bv in
            Some (bv.bv_ppname, p) <: option (ppname_t & term)
          | _ -> None in  // TODO: FIXME: provide error from this function?
        let b = { binder_ty = ty; binder_ppname = ppname } in
        let pulse_t : (t':Pulse.Syntax.Base.term{elab_term t' == t}) =
          if inspect_fv fv = exists_lid
          then Tm_ExistsSL u b p
          else Tm_ForallSL u b p in
          
        Some pulse_t
      )
      else aux ()
    | Tv_FVar fv, [(a, _)] ->
      if inspect_fv fv = pure_lid
      then (
        let? t1 = readback_ty a in
        Some (Tm_Pure t1)
      )
      else aux ()
    | _ -> aux ()
    end
  
  | Tv_Refine _ _ _
  | Tv_Arrow _ _
  | Tv_Type _
  | Tv_Const _
  | Tv_Let _ _ _ _ _ _
  | Tv_Var _
  | Tv_BVar _
  | Tv_UInst _ _
  | Tv_Match _ _ _ -> Some (Tm_FStar t (range_of_term t))

  | Tv_Abs _ _ -> None

  | Tv_Uvar _ _ -> None // TODO: FIXME: T.fail "readback_ty: unexpected Tv_Uvar"

  | Tv_AscribedT _ _ _ _
  | Tv_AscribedC _ _ _ _ -> readback_ty_ascribed t

  | Tv_Unknown -> Some Tm_Unknown

  | Tv_Unsupp -> None

let readback_comp (t:R.term)
  : option (c:comp { elab_comp c == t }) =

  let ropt = try_readback_st_comp t readback_ty in
  match ropt with
  | Some _ -> ropt
  | _ ->
    let? t' = readback_ty t in
    Some (C_Tot t' <: c:comp{ elab_comp c == t })
