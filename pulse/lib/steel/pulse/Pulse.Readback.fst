module Pulse.Readback
module R = FStar.Reflection
module L = FStar.List.Tot
// module T = FStar.Tactics
module RT = FStar.Reflection.Typing
open Pulse.Syntax.Base
open Pulse.Reflection.Util
open Pulse.Elaborate.Pure

let (let?) (f:option 'a) (g:'a -> option 'b) : option 'b =
  match f with
  | None -> None
  | Some x -> g x

// let rec readback_universe (u:R.universe)
//   : o:option universe{ Some? o ==> elab_universe (Some?.v o) == u } =
//   match R.inspect_universe u with
//   | R.Uv_Zero ->
//     Some U_zero

//   | R.Uv_Succ u' -> (
//     match readback_universe u' with
//     | None -> None
//     | Some u' -> 
//       Some (U_succ u')
//     )

//   | R.Uv_Name (s, r) ->
//     assume (r == FStar.Reflection.Typing.Builtins.dummy_range);
//     Some (U_var s)

//   | R.Uv_Max [u1; u2] -> (
//     assume (u2 << u);     //??
//     let u1' = readback_universe u1 in
//     let u2' = readback_universe u2 in
//     match u1', u2' with
//     | Some u1', Some u2' ->
//       Some (U_max u1' u2')
//     | _ -> None
//     )

//   | _ -> None

// let rec readback_universes (us:list R.universe)
//   : o:option (list universe) { 
//           Some? o ==> List.Tot.map elab_universe (Some?.v o) == us 
//     }
//   = match us with
//     | [] -> Some []
//     | hd::tl -> 
//       match readback_universe hd with
//       | None -> None
//       | Some hd -> 
//         match readback_universes tl with
//         | None -> None
//         | Some tl -> Some (hd::tl)
    
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

let collect_app_refined (t:R.term) : tuple2 (t':R.term{t' << t})
                                            (list (a:R.argv{a << t})) =
  admit ();
  R.collect_app_ln t

#push-options "--z3rlimit 100 --fuel 4 --ifuel 4"
let rec readback_ty (t:R.term)
  : option (ty:term { elab_term ty == t }) =

  let open R in
  let open Pulse.Syntax.Base in
  
  match inspect_ln t with
  | Tv_Var bv ->
    let bv_view = inspect_bv bv in
    assume (bv_view.bv_index >= 0);
    let r = tm_var {nm_index=bv_view.bv_index;nm_ppname=bv_view.bv_ppname;nm_range=range_of_term t} in
    // Needs some tweaks to how names are designed in the DSL,
    //   e.g. may need to expose ppname, what happens to tun bv sort?
    assume (elab_term r == t);
    Some r

  | Tv_BVar bv ->
    let bv_view = inspect_bv bv in
    assume (bv_view.bv_index >= 0);
    let r = tm_bvar {bv_index=bv_view.bv_index;bv_ppname=bv_view.bv_ppname; bv_range=range_of_term t} in
    // Similar to the name case
    assume (elab_term r == t);
    Some r

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
    else Some (tm_fvar {fv_name=inspect_fv fv; fv_range=range_of_term t})

  | Tv_UInst fv us ->
    let fv = {fv_name=inspect_fv fv; fv_range=range_of_term t} in
    Some (tm_uinst fv us)

  | Tv_App hd (a, q) -> 
    let aux () = 
      // let? hd' = readback_ty hd in
      match q with
      | R.Q_Meta _ -> None
      | _ -> Some (Tm_FStar t FStar.Range.range_0)
        // let? arg' = readback_ty a in
        // Some (Tm_PureApp hd' (readback_qual q) arg' <: ty:term {elab_term ty == t})
    in
    let head, args = collect_app_refined t in
    begin
    match inspect_ln head, args with
    | Tv_FVar fv, [(a1, _); (a2, _)] ->
      if inspect_fv fv = star_lid
      then (
        let? t1 = readback_ty a1 in
        let? t2 = readback_ty a2 in
        assume (elab_term (Tm_Star t1 t2) == t);
        Some #(t':Pulse.Syntax.Base.term {elab_term t' == t}) (Tm_Star t1 t2)
      )
      else aux ()
    | Tv_UInst fv [u], [(a1, _); (a2, _)] ->
      if inspect_fv fv = exists_lid ||
         inspect_fv fv = forall_lid
      then (
        let? ty = readback_ty a1 in
        let? p =
          match inspect_ln a2 with
          | Tv_Abs _ body ->
            let? p = readback_ty body in
            Some p <: option term
          | _ -> None in  // TODO: FIXME: provide error from this function?

        let pulse_t : (t':Pulse.Syntax.Base.term{elab_term t' == t}) =
          if inspect_fv fv = exists_lid
          then begin
            assume (elab_term (Tm_ExistsSL u ty p should_elim_true) == t);
            Tm_ExistsSL u ty p should_elim_true
          end
          else begin
            assume (elab_term (Tm_ForallSL u ty p) == t);
            Tm_ForallSL u ty p
          end in
          
        Some pulse_t
      )
      else aux ()
    | Tv_FVar fv, [(a, _)] ->
      if inspect_fv fv = pure_lid
      then (
        let? t1 = readback_ty a in
        assume (elab_term (Tm_Pure t1) == t);
        Some #(t':Pulse.Syntax.Base.term {elab_term t' == t}) (Tm_Pure t1)
      )
      else aux ()
    | _ -> aux ()
    end
  
  | Tv_Refine bv sort phi ->
    let bv_view = inspect_bv bv in
    let? ty = readback_ty sort in
    let? phi = readback_ty phi in
    let r = tm_refine {binder_ty=ty;binder_ppname=bv_view.bv_ppname} phi in
    assume (elab_term r == t);
    Some (r <: ty:term {elab_term ty == t})

  | Tv_Abs _ _ -> None  //T.fail "readback_ty: unexpected Tv_Abs"

  | Tv_Arrow _ _ ->
    Some (Tm_FStar t (range_of_term t))
  // (
  //   let { binder_bv=bv; binder_qual=aq; binder_attrs=attrs; binder_sort=sort } =
  //       inspect_binder b
  //   in
  //   assume (attrs == []);
  //   match aq with
  //   | R.Q_Meta _ -> None
  //   | _ -> 
  //     let q = readback_qual aq in
  //     RT.pack_inspect_binder b;  // This does not have SMTPat
  //     let bv_view = inspect_bv bv in
  //     assume (bv_view.bv_index == 0);
  //     let c_view = inspect_comp c in
  //     (match c_view with
  //      | C_Total c_t ->
  //        let? b_ty' = readback_ty sort in
  //        let? c' = readback_comp c_t in
  //        Some (tm_arrow {binder_ty=b_ty';binder_ppname=bv_view.bv_ppname} q c' <: ty:term{ elab_term ty == t})
  //     | _ -> None)
  //   )

  | Tv_Type _ -> Some (Tm_FStar t (range_of_term t))

  | Tv_Const _ -> Some (Tm_FStar t (range_of_term t))
 
  | Tv_Uvar _ _ -> None // TODO: FIXME: T.fail "readback_ty: unexpected Tv_Uvar"

  | Tv_Let _ _ _ _ _ _ ->
    Some (Tm_FStar t (range_of_term t))
    // if recf
    // then None // TODO: FIXME: T.fail "readback_ty: unexpected recursive Tv_Let"
    // else begin
    //   assume (attrs == []);
    //   let bv_view = inspect_bv bv in
    //   assume (bv_view.bv_index == 0);
    //   let? bv_t' = readback_ty ty in
    //   let? def' = readback_ty def in
    //   let? body' = readback_ty body in
    //   FStar.Sealed.sealed_singl bv_view.bv_ppname RT.pp_name_default;
    //   Some (Tm_Let bv_t' def' body' <: ty:term { elab_term ty == t })
    // end

  | Tv_Match _ _ _ -> Some (Tm_FStar t (range_of_term t))

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
  | Tv_AscribedT t _ _ _
  | Tv_AscribedC t _ _ _ -> admit (); Some (Tm_FStar t (range_of_term t))

  | Tv_Unknown ->
    Some Tm_Unknown

  | Tv_Unsupp ->
    None
#pop-options  

let readback_comp (t:R.term)
  : option (c:comp { elab_comp c == t }) =

  let ropt = try_readback_st_comp t readback_ty in
  match ropt with
  | Some _ -> ropt
  | _ ->
    let? t' = readback_ty t in
    Some (C_Tot t' <: c:comp{ elab_comp c == t })
