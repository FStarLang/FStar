module Pulse.Readback
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
module RT = Refl.Typing
open Pulse.Syntax
open Pulse.Elaborate.Pure

let (let?) (f:option 'a) (g:'a -> T.Tac (option 'b)) : T.Tac (option 'b) =
  match f with
  | None -> None
  | Some x -> g x

let rec readback_universe (u:R.universe)
  : o:option universe{ Some? o ==> elab_universe (Some?.v o) == u } =
  match R.inspect_universe u with
  | R.Uv_Zero ->
    Some U_zero

  | R.Uv_Succ u' -> (
    match readback_universe u' with
    | None -> None
    | Some u' -> 
      Some (U_succ u')
    )

  | R.Uv_Name (s, r) ->
    assume (r == Refl.Typing.Builtins.dummy_range);
    Some (U_var s)

  | R.Uv_Max [u1; u2] -> (
    assume (u2 << u);     //??
    let u1' = readback_universe u1 in
    let u2' = readback_universe u2 in
    match u1', u2' with
    | Some u1', Some u2' ->
      Some (U_max u1' u2')
    | _ -> None
    )

  | _ -> None

let rec readback_universes (us:list R.universe)
  : o:option (list universe) { 
          Some? o ==> List.Tot.map elab_universe (Some?.v o) == us 
    }
  = match us with
    | [] -> Some []
    | hd::tl -> 
      match readback_universe hd with
      | None -> None
      | Some hd -> 
        match readback_universes tl with
        | None -> None
        | Some tl -> Some (hd::tl)
    
#push-options "--z3rlimit_factor 20"
let try_readback_st_comp
  (t:R.term)
  (readback_ty:(t':R.term -> T.Tac (option (ty:pure_term { elab_term ty == Some t' }))))

  : T.Tac (option (c:comp{elab_comp c == Some t})) =

  let open R in
  let hd, args = collect_app t in
  match inspect_ln hd with
  | Tv_UInst fv [u] ->
    let fv_lid = inspect_fv fv in
    if fv_lid = stt_lid
    then match args with
         | [res; pre; post] ->
           (match inspect_ln (fst post) with
            | Tv_Abs b body ->
              let bv, (aq, attrs) = inspect_binder b in    
              RT.pack_inspect_binder b;  // This does not have SMTPat
              let bv_view = inspect_bv bv in
              assume (fv == stt_fv);
              assume (aq == Q_Explicit           /\
                      attrs == []                /\
                      bv_view.bv_ppname == "x"   /\
                      bv_view.bv_index == 0      /\
                      bv_view.bv_sort == fst res /\
                      snd res == Q_Explicit      /\
                      snd pre == Q_Explicit      /\
                      snd post == Q_Explicit);

              let l = [fst res; fst pre; mk_abs (fst res) R.Q_Explicit body] in
              assume (t == mk_stt_app u l);
              let? u'' = readback_universe u in
              let? res' = readback_ty (fst res) in
              let? pre' = readback_ty (fst pre) in
              let? post' = readback_ty body in
              let c = C_ST {u=u''; res=res'; pre=pre';post=post'} in
              assume (elab_universe u'' == u);
              Some (c <: c:Pulse.Syntax.comp{ elab_comp c == Some t })
            | _ -> None)
         | _ -> None
    else if fv_lid = stt_atomic_lid || fv_lid = stt_ghost_lid
    then match args with
         | [res; opened; pre; post] ->
           (match inspect_ln (fst post) with
            | Tv_Abs b body ->
              let bv, (aq, attrs) = inspect_binder b in    
              RT.pack_inspect_binder b;  // This does not have SMTPat
              let bv_view = inspect_bv bv in
              let l = [fst res; fst opened; fst pre; mk_abs (fst res) R.Q_Explicit body] in
              let? u'' = readback_universe u in
              let? res' = readback_ty (fst res) in
              let? opened' = readback_ty (fst opened) in
              let? pre' = readback_ty (fst pre) in
              let? post' = readback_ty body in
              if fv_lid = stt_atomic_lid
              then begin
                assume (t == mk_stt_atomic_app u l);
                let c = C_STAtomic opened' ({u=u''; res=res'; pre=pre';post=post'}) in
                assume (elab_universe u'' == u);
                Some (c <: c:Pulse.Syntax.comp{ elab_comp c == Some t })
              end
              else begin
                assume (t == mk_stt_ghost_app u l);
                let c = C_STGhost opened' ({u=u''; res=res'; pre=pre';post=post'}) in
                assume (elab_universe u'' == u);
                Some (c <: c:Pulse.Syntax.comp{ elab_comp c == Some t })
              end
            | _ -> None)
         | _ -> None
    else None  
  | _ -> None
#pop-options

let readback_qual = function
  | R.Q_Implicit -> Some Implicit
  | _ -> None

let rec readback_ty (t:R.term)
  : T.Tac (option (ty:pure_term { elab_term ty == Some t })) =

  let open T in
  let open R in

  match inspect_ln t with
  | Tv_Var bv ->
    let bv_view = inspect_bv bv in
    assume (bv_view.bv_index >= 0);
    let r = Tm_Var {nm_index=bv_view.bv_index;nm_ppname=bv_view.bv_ppname} in
    // Needs some tweaks to how names are designed in the DSL,
    //   e.g. may need to expose ppname, what happens to tun bv sort?
    assume (elab_term r == Some t);
    Some r

  | Tv_BVar bv ->
    let bv_view = inspect_bv bv in
    assume (bv_view.bv_index >= 0);
    let r = Tm_BVar {bv_index=bv_view.bv_index;bv_ppname=bv_view.bv_ppname} in
    // Similar to the name case
    assume (elab_term r == Some t);
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
    else Some (Tm_FVar (inspect_fv fv))

  | Tv_UInst fv us -> (
    let fv = inspect_fv fv in
    match readback_universes us with
    | None -> None
    | Some us' -> Some (Tm_UInst fv us')
    )


  | Tv_App hd (a, q) -> 
    let aux () = 
      let? hd' = readback_ty hd in
      match q with
      | R.Q_Meta _ -> None
      | _ -> 
        let? arg' = readback_ty a in
        Some (Tm_PureApp hd' (readback_qual q) arg' <: ty:pure_term {elab_term ty == Some t})
    in
    let head, args = R.collect_app t in
    begin
    match inspect_ln head, args with
    | Tv_FVar fv, [(a1,_); (a2,_)] -> 
      if inspect_fv fv = star_lid
      then (
        let? t1 = readback_ty a1 in
        let? t2 = readback_ty a2 in
        assume (elab_term (Tm_Star t1 t2) == Some t);
        Some #(t':Pulse.Syntax.term {elab_term t' == Some t}) (Tm_Star t1 t2)
      )
      else aux ()
    | Tv_FVar fv, [(a, _)] ->
      if inspect_fv fv = pure_lid
      then (
        let? t1 = readback_ty a in
        assume (elab_term (Tm_Pure t1) == Some t);
        Some #(t':Pulse.Syntax.term {elab_term t' == Some t}) (Tm_Pure t1)
      )
      else aux ()
    | _ -> aux ()
    end
  
  | Tv_Refine bv phi ->
    let bv_view = inspect_bv bv in
    let? ty = readback_ty bv_view.bv_sort in
    let? phi = readback_ty phi in
    let r = Tm_Refine {binder_ty=ty;binder_ppname=bv_view.bv_ppname} phi in
    assume (elab_term r == Some t);
    Some (r <: ty:pure_term {elab_term ty == Some t})

  | Tv_Abs _ _ -> T.fail "readback_ty: unexpected Tv_Abs"

  | Tv_Arrow b c -> (
    let bv, (aq, attrs) = inspect_binder b in
    assume (attrs == []);
    match aq with
    | R.Q_Meta _ -> None
    | _ -> 
      let q = readback_qual aq in
      RT.pack_inspect_binder b;  // This does not have SMTPat
      let bv_view = inspect_bv bv in
      assume (bv_view.bv_ppname == "x" /\ bv_view.bv_index == 0);
      let c_view = inspect_comp c in
      (match c_view with
       | C_Total c_t ->
         let? b_ty' = readback_ty bv_view.bv_sort in
         let? c' = readback_comp c_t in
         Some (Tm_Arrow {binder_ty=b_ty';binder_ppname=bv_view.bv_ppname} q c' <: ty:pure_term{ elab_term ty == Some t})
      | _ -> None)
    )

  | Tv_Type u -> (
    match readback_universe u with
    | None -> None
    | Some u' -> Some (Tm_Type u' <: ty:pure_term{ elab_term ty == Some t })
    )

  | Tv_Const c ->
    (match c with
     | C_Unit -> Some (Tm_Constant Pulse.Syntax.Unit)
     | C_True -> Some (Tm_Constant (Bool true))
     | C_False -> Some (Tm_Constant (Bool false))
     | C_Int n -> Some (Tm_Constant (Int n))
     | _ -> T.fail "readback_ty: constant not supported")

  | Tv_Uvar _ _ -> T.fail "readback_ty: unexpected Tv_Uvar"

  | Tv_Let recf attrs bv def body ->
    if recf
    then T.fail "readback_ty: unexpected recursive Tv_Let"
    else begin
      assume (attrs == []);
      let bv_view = inspect_bv bv in
      assume (bv_view.bv_ppname == "x" /\ bv_view.bv_index == 0);
      let? bv_t' = readback_ty bv_view.bv_sort in
      let? def' = readback_ty def in
      let? body' = readback_ty body in
      Some (Tm_Let bv_t' def' body' <: ty:pure_term { elab_term ty == Some t })
    end

  | Tv_Match _ _ _ -> T.fail "readbackty: Tv_Match not yet implemented"

  | Tv_AscribedT _ _ _ _
  | Tv_AscribedC _ _ _ _ -> T.fail "readbackty: ascription nodes not supported"

  | Tv_Unknown -> T.fail "readbackty: unexpected Tv_Unknown"
  
  
and readback_comp (t:R.term)
  : T.Tac (option (c:comp{ elab_comp c == Some t})) =

  let ropt = try_readback_st_comp t readback_ty in
  match ropt with
  | Some _ -> ropt
  | _ ->
    let? t' = readback_ty t in
    Some (C_Tot t' <: c:comp{ elab_comp c == Some t })
