module Pulse.Checker
module RT = Refl.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing
module P = Pulse.Syntax.Printer
module RTB = FStar.Tactics.Builtins

let tc_meta_callback (f:R.env) (e:R.term) 
  : T.Tac (option (t:R.term & RT.typing f e t))
  = let topt = RTB.tc_term f e in
    match topt with
    | None -> None
    | Some t ->
      Some (| t, RT.T_Token _ _ _ (FStar.Squash.get_proof _) |)

let (let?) (f:option 'a) (g:'a -> T.Tac (option 'b)) : T.Tac (option 'b) =
  match f with
  | None -> None
  | Some x -> g x

let is_stt (t:R.term)
  : Pure (option (R.universe & R.typ & R.term & R.term))
         (requires True)
         (ensures fun r ->
            Some? r ==> (let u, res, pre, post = Some?.v r in
                       let args = [res; pre; mk_abs res post] in
                       t == mk_stt_app u args)) =
          
  let open R in
  let hd, args = collect_app t in
  match inspect_ln hd with
  | Tv_UInst fv [u] ->
    if inspect_fv fv = stt_lid
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
                      bv_view.bv_ppname == "_"   /\
                      bv_view.bv_index == 0      /\
                      bv_view.bv_sort == fst res /\
                      snd res == Q_Explicit      /\
                      snd pre == Q_Explicit      /\
                      snd post == Q_Explicit);

              let l = [fst res; fst pre; mk_abs (fst res) body] in
              assume (args_of l == args);
              // probably need some lemma for R.mk_app and R.collect_app
              assume (t == mk_stt_app u l);
              Some (u, fst res, fst pre, body)
            | _ -> None)
         | _ -> None
    else None
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
    else Some (Tm_FVar (inspect_fv fv))

  | Tv_UInst _ _ ->
    T.fail ("readback_ty: Tv_UInst is not yet handled: " ^ T.term_to_ast_string t)

  | Tv_App hd arg ->
    let? hd' = readback_ty hd in
    // R.aqualv is noeq, we should add implicits to mini steel
    assume (snd arg == R.Q_Explicit);
    let? arg' = readback_ty (fst arg) in
    Some (Tm_PureApp hd' arg' <: ty:pure_term {elab_term ty == Some t})

  | Tv_Refine bv phi ->
    let bv_view = inspect_bv bv in
    let? ty = readback_ty bv_view.bv_sort in
    let? phi = readback_ty phi in
    let r = Tm_Refine {binder_ty=ty;binder_ppname=bv_view.bv_ppname} phi in
    assume (elab_term r == Some t);
    Some (r <: ty:pure_term {elab_term ty == Some t})

  | Tv_Abs _ _ -> T.fail "readback_ty: unexpected Tv_Abs"

  | Tv_Arrow b c ->
    let bv, (aq, attrs) = inspect_binder b in
    assume (attrs == []);
    assume (aq == R.Q_Explicit);
    RT.pack_inspect_binder b;  // This does not have SMTPat
    let bv_view = inspect_bv bv in
    assume (bv_view.bv_ppname == "_" /\ bv_view.bv_index == 0);
     
    let c_view = inspect_comp c in
    (match c_view with
     | C_Total c_t ->
      let? b_ty' = readback_ty bv_view.bv_sort in
      let? c' = readback_comp c_t in
      Some (Tm_Arrow {binder_ty=b_ty';binder_ppname=bv_view.bv_ppname} c' <: ty:pure_term{ elab_term ty == Some t})
     | _ -> None)

  | Tv_Type u ->
    let? u' = readback_universe u in
    Some (Tm_Type u' <: ty:pure_term{ elab_term ty == Some t })

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
      assume (bv_view.bv_ppname == "_" /\ bv_view.bv_index == 0);
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

  let is_stt_opt = is_stt t in
  match is_stt_opt with
  | Some (u', res, pre, post) ->
    let? u'' = readback_universe u' in
    let? res' = readback_ty res in
    let? pre' = readback_ty pre in
    let? post' = readback_ty post in
    Some (C_ST ({u=u''; res=res'; pre=pre';post=post'}) <: c:comp{ elab_comp c == Some t })

  | _ ->
    let? t' = readback_ty t in
    Some (C_Tot t' <: c:comp{ elab_comp c == Some t })

and readback_universe (u:R.universe)
  : T.Tac (option (u':universe{ elab_universe u' == u })) =

  match R.inspect_universe u with
  | R.Uv_Zero -> Some U_zero
  | R.Uv_Succ u' ->
    let? u' = readback_universe u' in
    Some (U_succ u' <: u':universe{ elab_universe u' == u })
  | R.Uv_Name (s, r) ->
    assume (r == Refl.Typing.Builtins.dummy_range);
    Some (U_var s)
  | R.Uv_Max [u1; u2] ->
    let? u1' = readback_universe u1 in
    let? u2' = readback_universe u2 in
    Some (U_max u1' u2' <: u':universe{ elab_universe u' == u })

  | _ -> T.fail "readback_universe: unexpected universe"

let check_universe (f0:RT.fstar_top_env) (g:env) (t:term)
  : T.Tac (_:(u:universe & universe_of f0 g t u) { is_pure_term t })
  = let f = extend_env_l f0 g in
    match elab_term t with
    | None ->
      T.fail ("Not a syntactically pure term: " ^ P.term_to_string t)
    | Some rt ->
      let ru_opt = RTB.universe_of f rt in
      match ru_opt  with
      | None -> T.fail "Not typable as a universe"
      | Some ru ->
        let uopt = readback_universe ru in
        let proof : squash (RTB.typing_token f rt (R.pack_ln (R.Tv_Type ru))) =
          FStar.Squash.get_proof _ in
        let proof : RT.typing f rt (R.pack_ln (R.Tv_Type ru)) = RT.T_Token _ _ _ proof in
        match uopt with
        | None -> T.fail "check_universe: failed to readback the universe"
        | Some u ->
          let proof : tot_typing f0 g t (Tm_Type u) =
            E (T_Tot g _ _ proof) in
          (| u, proof |)
      
let check_tot_univ (f:RT.fstar_top_env) (g:env) (t:term)
  : T.Tac (_:(u:universe &
              ty:pure_term &
              universe_of f g ty u &
              src_typing f g t (C_Tot ty)) { is_pure_term t } )
  = let fg = extend_env_l f g in
    match elab_term t with
    | None ->
      T.fail ("Not a syntactically pure term: " ^ P.term_to_string t)
    | Some rt -> 
      match tc_meta_callback fg rt with
      | None -> T.fail "Not typeable"
      | Some (| ty', tok |) ->
        match readback_ty ty' with
        | None -> T.fail "Inexpressible type"
        | Some ty -> 
          let (| u, uty |) = check_universe f g ty in
          (| u, ty, uty, T_Tot g t ty tok |)

let check_tot (f:RT.fstar_top_env) (g:env) (t:term)
  : T.Tac (_:(ty:pure_term &
              src_typing f g t (C_Tot ty)) { is_pure_term t })
  = let fg = extend_env_l f g in
    match elab_term t with
    | None ->
      T.fail ("Not a syntactically pure term: " ^ P.term_to_string t)
    | Some rt -> 
      match tc_meta_callback fg rt with
      | None -> T.fail "Not typeable"
      | Some (| ty', tok |) ->
        match readback_ty ty' with
        | None -> T.fail "Inexpressible type"
        | Some ty -> 
          (| ty, T_Tot g t ty tok |)

let rec vprop_as_list (vp:pure_term)
  : list pure_term
  = match vp with
    | Tm_Star vp0 vp1 -> vprop_as_list vp0 @ vprop_as_list vp1
    | _ -> [vp]

let rec list_as_vprop (vps:list pure_term)
  : pure_term
  = match vps with
    | [] -> Tm_Emp
    | hd::tl -> Tm_Star hd (list_as_vprop tl)

let canon_vprop (vp:pure_term)
  : pure_term
  = list_as_vprop (vprop_as_list vp)

let rec list_as_vprop_append f g (vp0 vp1:list pure_term)
  : GTot (vprop_equiv f g (list_as_vprop (vp0 @ vp1))
                          (Tm_Star (list_as_vprop vp0) 
                                   (list_as_vprop vp1)))
         (decreases vp0)
  = match vp0 with
    | [] -> 
      let v : vprop_equiv f g (list_as_vprop vp1)
                              (Tm_Star Tm_Emp (list_as_vprop vp1)) = VE_Sym _ _ _ (VE_Unit _ _)
      in
      v
    | hd::tl ->
      let tl_vp1 = list_as_vprop_append f g tl vp1 in
      let d : vprop_equiv f g (list_as_vprop (vp0 @ vp1))
                              (Tm_Star hd (Tm_Star (list_as_vprop tl) (list_as_vprop vp1)))
            = VE_Ctxt _ _ _ _ _ (VE_Refl _ _) tl_vp1
      in
      let d : vprop_equiv f g (list_as_vprop (vp0 @ vp1))
                              (Tm_Star (Tm_Star hd (list_as_vprop tl)) (list_as_vprop vp1))
            = VE_Trans _ _ _ _ d (VE_Assoc _ _ _ _) in
      d

let list_as_vprop_comm f g (vp0 vp1:list pure_term)
  : GTot (vprop_equiv f g (list_as_vprop (vp0 @ vp1))
                          (list_as_vprop (vp1 @ vp0)))
  = let d1 : _ = list_as_vprop_append f g vp0 vp1 in
    let d2 : _ = VE_Sym _ _ _ (list_as_vprop_append f g vp1 vp0) in
    let d1 : _ = VE_Trans _ _ _ _ d1 (VE_Comm _ _ _) in
    VE_Trans _ _ _ _ d1 d2

let list_as_vprop_assoc f g (vp0 vp1 vp2:list pure_term)
  : GTot (vprop_equiv f g (list_as_vprop (vp0 @ (vp1 @ vp2)))
                          (list_as_vprop ((vp0 @ vp1) @ vp2)))
  = List.Tot.append_assoc vp0 vp1 vp2;
    VE_Refl _ _

let list_as_vprop_ctx f g (vp0 vp1 vp2:list pure_term)
  (d:vprop_equiv f g (list_as_vprop vp0) (list_as_vprop vp1))
  : GTot (vprop_equiv f g (list_as_vprop (vp0 @ vp2)) (list_as_vprop (vp1 @ vp2)))
  = admit ()

let list_as_vprop_singleton f g
  (p q:pure_term)
  (d:vprop_equiv f g p q)
  : GTot (vprop_equiv f g (list_as_vprop [p]) (list_as_vprop [q]))
  = admit ()

let rec vprop_list_equiv (f:RT.fstar_top_env)
                         (g:env)
                         (vp:pure_term)
  : GTot (vprop_equiv f g vp (canon_vprop vp))
         (decreases vp)
  = match vp with
    | Tm_Star vp0 vp1 ->
      let eq0 = vprop_list_equiv f g vp0 in
      let eq1 = vprop_list_equiv f g vp1 in      
      let app_eq
        : vprop_equiv _ _ (canon_vprop vp) (Tm_Star (canon_vprop vp0) (canon_vprop vp1))
        = list_as_vprop_append f g (vprop_as_list vp0) (vprop_as_list vp1)
      in
      let step
        : vprop_equiv _ _ vp (Tm_Star (canon_vprop vp0) (canon_vprop vp1))
        = VE_Ctxt _ _ _ _ _ eq0 eq1
      in
      VE_Trans _ _ _ _ step (VE_Sym _ _ _ app_eq)
      
    | _ -> 
      VE_Sym _ _ _
        (VE_Trans _ _ _ _ (VE_Comm g vp Tm_Emp) (VE_Unit _ vp))

module L = FStar.List.Tot.Base
let rec maybe_split_one_vprop f g (p:pure_term) (qs:list pure_term)
  : option (l:list pure_term & q:pure_term & vprop_equiv f g p q & list pure_term)
  = match qs with
    | [] -> None
    | q::qs -> 
      if p = q
      then Some (| [], q, VE_Refl g p, qs |)
      else match maybe_split_one_vprop f g p qs with
           | None -> None
           | Some (| l, q', d, r |) -> Some (| q::l, q', d, r |)
    
let can_split_one_vprop f g p qs = Some? (maybe_split_one_vprop f g p qs)

let split_one_vprop_l f g
  (p:pure_term) 
  (qs:list pure_term { can_split_one_vprop f g p qs })
  : list pure_term
  = let Some (| l, _, _, _ |) = maybe_split_one_vprop f g p qs in
    l

let split_one_vprop_r f g
  (p:pure_term) 
  (qs:list pure_term { can_split_one_vprop f g p qs })
  : list pure_term
  = let Some (| _, _, _, r |) = maybe_split_one_vprop f g p qs in
    r

let split_one_vprop_q f g
  (p:pure_term)
  (qs:list pure_term { can_split_one_vprop f g p qs })
  : q:pure_term & vprop_equiv f g p q
  = let Some (| _, q, d, _ |) = maybe_split_one_vprop f g p qs in
    (| q, d |)

let vprop_equiv_swap_equiv (f:_) (g:_) (l0 l2:list pure_term)
  (p q:pure_term) (d_p_q:vprop_equiv f g p q)
  : GTot (vprop_equiv f g (list_as_vprop ((l0 @ [q]) @ l2))
                          (list_as_vprop ([p] @ (l0 @ l2)))) =
  let d : vprop_equiv f g (list_as_vprop ((l0 @ [q]) @ l2))
                          (list_as_vprop (([q] @ l0) @ l2))
    = list_as_vprop_ctx f g (l0 @ [q]) ([q] @ l0) l2 (list_as_vprop_comm f g l0 [q]) in
  let d' : vprop_equiv f g (list_as_vprop (([q] @ l0) @ l2))
                           (list_as_vprop ([q] @ (l0 @ l2)))
    = List.Tot.append_assoc [q] l0 l2;
      VE_Refl _ _ in
  let d : vprop_equiv f g (list_as_vprop ((l0 @ [q]) @ l2))
                          (list_as_vprop ([q] @ (l0 @ l2)))
    = VE_Trans _ _ _ _ d d' in
  let d_q_p = VE_Sym _ _ _ d_p_q in
  let d' : vprop_equiv f g (list_as_vprop [q]) (list_as_vprop [p]) =
    list_as_vprop_singleton _ _ _ _ d_q_p in
  let d' : vprop_equiv f g (list_as_vprop ([q] @ (l0 @ l2)))
                           (list_as_vprop ([p] @ (l0 @ l2)))
    = list_as_vprop_ctx f g [q] [p] (l0 @ l2) d' in
  VE_Trans _ _ _ _ d d'

let vprop_equiv_swap (f:_) (g:_) (l0 l1 l2:list pure_term)
  : GTot (vprop_equiv f g (list_as_vprop ((l0 @ l1) @ l2))
                          (list_as_vprop (l1 @ (l0 @ l2))))
  = let d1 : _ = list_as_vprop_append f g (l0 @ l1) l2 in
    let d2 = VE_Trans _ _ _ _ d1 (VE_Ctxt _ _ _ _ _ (list_as_vprop_comm _ _ _ _) (VE_Refl _ _)) in
    let d3 = VE_Sym _ _ _ (list_as_vprop_append f g (l1 @ l0) l2) in
    let d4 = VE_Trans _ _ _ _ d2 d3 in
    List.Tot.append_assoc l1 l0 l2;
    d4

let split_one_vprop f g
  (p:pure_term) 
  (qs:list pure_term { can_split_one_vprop f g p qs })
  : list pure_term
  = split_one_vprop_l f g p qs @ split_one_vprop_r f g p qs

let split_one_vprop_equiv f g (p:pure_term) (qs:list pure_term { can_split_one_vprop f g p qs })
  : vprop_equiv f g (list_as_vprop qs) (Tm_Star p (list_as_vprop (split_one_vprop f g p qs)))
  = // let rec aux (qs:list pure_term { can_split_one_vprop f g p qs })
    //   : Lemma (qs == ((split_one_vprop_l f g p qs @ [p]) @ split_one_vprop_r f g p qs))
    //   = match qs with
    //     | q :: qs ->
    //       if p = q then ()
    //       else aux qs
    // in
    // aux qs;
    let Some (| l, q, d, r |) = maybe_split_one_vprop f g p qs in
    assume (qs == (l @ [q]) @ r);
    vprop_equiv_swap_equiv f g l r p q d

let rec try_split_vprop f g (req:list pure_term) (ctxt:list pure_term)
  : option (frame:list pure_term &
            vprop_equiv f g (list_as_vprop (req @ frame)) (list_as_vprop ctxt))
  = match req with
    | [] -> Some (| ctxt, VE_Refl g _ |)
    | hd::tl ->
      match maybe_split_one_vprop f g hd ctxt with
      | None -> None
      | Some (| l, _, _, r |) -> 
        let d1 : vprop_equiv f g (list_as_vprop ctxt) (list_as_vprop (hd :: (l@r))) = split_one_vprop_equiv _ _ hd ctxt in
        match try_split_vprop f g tl (l @ r) with
        | None -> None
        | Some (| frame, d |) ->
          let d : vprop_equiv f g (list_as_vprop (tl @ frame)) (list_as_vprop (l @ r)) = d in
          let dd : vprop_equiv f g (list_as_vprop (req @ frame)) (list_as_vprop (hd :: (l @ r))) = 
              VE_Ctxt _ _ _ _ _ (VE_Refl _ hd) d
          in
          let ddd = VE_Trans _ _ _ _ dd (VE_Sym _ _ _ d1) in
          Some (| frame, ddd |)
                       
let split_vprop (f:RT.fstar_top_env)
                (g:env)
                (ctxt:pure_term)
                (ctxt_typing: tot_typing f g ctxt Tm_VProp)
                (req:pure_term)
   : T.Tac (frame:pure_term &
            tot_typing f g frame Tm_VProp &
            vprop_equiv f g (Tm_Star req frame) ctxt)
   = let ctxt_l = vprop_as_list ctxt in
     let req_l = vprop_as_list req in
     match try_split_vprop f g req_l ctxt_l with
     | None -> T.fail (Printf.sprintf "Could not find frame: \n\tcontext = %s\n\trequires = %s\n"
                                            (P.term_to_string ctxt)
                                            (P.term_to_string req))
     | Some (| frame, veq |) ->
       let d1 
         : vprop_equiv _ _ (Tm_Star (canon_vprop req) (list_as_vprop frame))
                           (list_as_vprop (req_l @ frame))
         = VE_Sym _ _ _ (list_as_vprop_append f g req_l frame)
       in
       let d1 
         : vprop_equiv _ _ (Tm_Star req (list_as_vprop frame))
                           (list_as_vprop (req_l @ frame))
         = VE_Trans _ _ _ _ (VE_Ctxt _ _ _ _ _ (vprop_list_equiv f g req) (VE_Refl _ _)) d1
       in
       let d : vprop_equiv _ _ (Tm_Star req (list_as_vprop frame))
                               (canon_vprop ctxt) =
           VE_Trans _ _ _ _ d1 veq
       in
       let d : vprop_equiv _ _ (Tm_Star req (list_as_vprop frame))
                               ctxt =
         VE_Trans _ _ _ _ d (VE_Sym _ _ _ (vprop_list_equiv f g ctxt))
       in
       let typing : tot_typing f g (list_as_vprop frame) Tm_VProp = 
         let fwd, bk = vprop_equiv_typing _ _ _ _ d in
         let star_typing = bk ctxt_typing in
         snd (star_typing_inversion _ _ _ _ star_typing)
       in
       (| list_as_vprop frame, typing, d |)

let rec check_equiv_emp (f:RT.fstar_top_env) (g:env) (vp:pure_term)
  : option (vprop_equiv f g vp Tm_Emp)
  = match vp with
    | Tm_Emp -> Some (VE_Refl _ _)
    | Tm_Star vp1 vp2 ->
      (match check_equiv_emp f g vp1, check_equiv_emp f g vp2 with
       | Some d1, Some d2 ->
         let d3 : vprop_equiv f g (Tm_Star vp1 vp2) (Tm_Star Tm_Emp Tm_Emp)
           = VE_Ctxt _ _ _ _ _ d1 d2 in
         let d4 : vprop_equiv f g (Tm_Star Tm_Emp Tm_Emp) Tm_Emp =
           VE_Unit _ _ in
         Some (VE_Trans _ _ _ _ d3 d4)
       | _, _ -> None)
     | _ -> None

#push-options "--z3rlimit_factor 2"
let check_vprop_equiv
  (f:RT.fstar_top_env)
  (g:env)
  (vp1 vp2:pure_term)
  (vp1_typing:tot_typing f g vp1 Tm_VProp)

  : T.Tac (vprop_equiv f g vp1 vp2) =

  let (| frame, _, d |) = split_vprop f g vp1 vp1_typing vp2 in
  match check_equiv_emp f g frame with
  | Some d_frame_equiv_emp ->
    let d : vprop_equiv f g (Tm_Star vp2 frame) vp1 = d in
    let d : vprop_equiv f g vp1 (Tm_Star vp2 frame) =
      VE_Sym _ _ _ d in
    let d' : vprop_equiv f g (Tm_Star vp2 frame) (Tm_Star vp2 Tm_Emp) =
      VE_Ctxt _ _ _ _ _ (VE_Refl _ vp2) d_frame_equiv_emp in
    let d : vprop_equiv f g vp1 (Tm_Star vp2 Tm_Emp) =
      VE_Trans _ _ _ _ d d' in
    let d' : vprop_equiv f g (Tm_Star vp2 Tm_Emp) (Tm_Star Tm_Emp vp2) = VE_Comm _ _ _ in
    let d  : vprop_equiv f g vp1 (Tm_Star Tm_Emp vp2) = VE_Trans _ _ _ _ d d' in
    let d' : vprop_equiv f g (Tm_Star Tm_Emp vp2) vp2 = VE_Unit _ _ in
    VE_Trans _ _ _ _ d d'
  | None ->
    T.fail (Printf.sprintf "check_vprop_equiv: %s and %s are not equivalent, frame: %s\n"
                 (P.term_to_string vp1)
                 (P.term_to_string vp2)
                 (P.term_to_string frame))
#pop-options

#push-options "--query_stats --fuel 1 --ifuel 2 --z3rlimit_factor 4"
let check_vprop (f:RT.fstar_top_env)
                (g:env)
                (t:pure_term)
  : T.Tac (tot_typing f g t Tm_VProp)
  = let (| ty, d |) = check_tot f g t in
    match ty with
    | Tm_VProp -> E d
    | _ -> T.fail "Expected a vprop"
                 
let try_frame_pre (#f:RT.fstar_top_env)
                  (#g:env)
                  (#t:term)
                  (#pre:pure_term)
                  (pre_typing: tot_typing f g pre Tm_VProp)
                  (#c:pure_comp { C_ST? c })
                  (t_typing: src_typing f g t c)
  : T.Tac (c':pure_comp_st { comp_pre c' == pre } &
           src_typing f g t c')
  = let C_ST s = c in
    let (| frame, frame_typing, ve |) = split_vprop f g pre pre_typing s.pre in
    let t_typing
      : src_typing f g t (add_frame c frame)
      = T_Frame g t c frame frame_typing t_typing in
    let x = fresh g in
    let c' = add_frame c frame in
    let C_ST s' = c' in
    let ve: vprop_equiv f g s'.pre pre = ve in
    let s'' = { s' with pre = pre } in
    let c'' = C_ST s'' in
    assert (is_pure_comp (C_ST s'));
    assert (is_pure_comp (C_ST s''));
    assert (comp_post c' == comp_post c'');
    opening_pure_term_with_pure_term
      (comp_post c')
      (null_var x)
      0;
    opening_pure_term_with_pure_term
      (comp_post c'')
      (null_var x)
      0;    
    assert (is_pure_term (open_term (comp_post c') x));
    let g' = ((x, Inl (comp_res c'))::g) in
    let ve: vprop_equiv f g (comp_pre c') (comp_pre c'') = ve in    
    let ve' 
      : vprop_equiv f g'
                      (open_term (comp_post c') x)
                      (open_term (comp_post c'') x)
      = VE_Refl _ _
    in
    let pre_typing = check_vprop f g (comp_pre c') in
    let post_typing = check_vprop f g' (open_term (comp_post c') x) in
    let (| u, res_typing |) = check_universe f g (comp_res c') in
    if u <> comp_u c' 
    then T.fail "Unexpected universe"
    else (
      let st_equiv = ST_VPropEquiv g c' c'' x pre_typing res_typing post_typing ve ve' in
      let t_typing = T_Equiv _ _ _ _ t_typing st_equiv in
      (| C_ST s'', t_typing |)
    )
#pop-options

#push-options "--z3rlimit_factor 2"
let frame_empty (f:RT.fstar_top_env)
                (g:env)
                (pre:pure_term)
                (pre_typing: tot_typing f g pre Tm_VProp)
                (u:universe)
                (ty:pure_term) 
                (ut:universe_of f g ty u)
                (t:term)
                (c0:pure_comp_st{ comp_pre c0 == Tm_Emp })
                (d:src_typing f g t c0)
  : T.Tac (c:pure_comp_st { comp_pre c == pre} &
           src_typing f g t c)
  = let d = T_Frame g t c0 pre pre_typing d in
    let c = add_frame c0 pre in
    let C_ST s = c in
    let d : src_typing f g t c = d in
    let s' = { s with pre = pre } in
    let c' = C_ST s' in
    let x = fresh g in
    let pre_typing = check_vprop f g (comp_pre c) in
    let (| u, res_typing |) = check_universe f g (comp_res c) in
    if u <> comp_u c
    then T.fail "Unexpected universe"
    else (
      let post_typing = check_vprop f ((x, Inl (comp_res c))::g) 
                                      (open_term (comp_post c) x) in
      let eq
        : st_equiv f g c c'
        = ST_VPropEquiv g c c' x
                        pre_typing
                        res_typing
                        post_typing
                        (VE_Unit g pre)
                        (VE_Refl _ _)
      in
      (| c', T_Equiv _ _ _ _ d eq |)
    )
#pop-options

#push-options "--query_stats --fuel 2 --ifuel 1 --z3rlimit_factor 20"
#push-options "--print_implicits --print_universes --print_full_names"
let rec check (f:RT.fstar_top_env)
              (g:env)
              (t:term)
              (pre:pure_term)
              (pre_typing: tot_typing f g pre Tm_VProp)
  : T.Tac (c:pure_comp { C_ST? c ==> comp_pre c == pre } &
           src_typing f g t c)
  = let repack #g #pre #t (x:(c:pure_comp_st { comp_pre c == pre } & src_typing f g t c))
      : (c:pure_comp { C_ST? c ==> comp_pre c == pre } & src_typing f g t c)
      = let (| c, d_c |) = x in (|c, d_c|)
    in
    let force_st #g #t (#pre:pure_term)
                 (pre_typing:tot_typing f g pre Tm_VProp)
                 (x:(c:pure_comp { C_ST? c ==> comp_pre c == pre } & src_typing f g t c))
      : T.Tac (c:pure_comp_st { comp_pre c == pre } & src_typing f g t c)
      = let (| c, d_c |) = x in
        match c with
        | C_Tot ty ->
          let (| ures, ures_ty |) = check_universe f g ty in
          let c = return_comp_noeq ures ty in
          let d = T_ReturnNoEq _ _ _ _ d_c ures_ty in
          frame_empty f g pre pre_typing ures ty ures_ty _ c d        

        | C_ST _ -> (|c, d_c|)
    in
    let frame_empty = frame_empty f g pre pre_typing in
    match t with
    | Tm_BVar _ -> T.fail "not locally nameless"
    | Tm_Var _
    | Tm_FVar _ 
    | Tm_Constant _
    | Tm_PureApp _ _
    | Tm_Let _ _ _ ->
      let (| u, ty, uty, d |) = check_tot_univ f g t in
      let c = return_comp u ty t in
      let d = T_Return _ _ _ _ (E d) uty in
      repack (frame_empty u ty uty t c d)

    | Tm_Emp
    | Tm_Pure _
    | Tm_Star _ _ 
    | Tm_ExistsSL _ _
    | Tm_ForallSL _ _
    | Tm_Arrow _ _
    | Tm_Type _
    | Tm_VProp
    | Tm_Refine _ _ ->
      let (| ty, d_ty |) = check_tot f g t in
      (| C_Tot ty, d_ty |)

    | Tm_Abs {binder_ty=t;binder_ppname=ppname} pre_hint body post_opt ->  (* {pre}  (fun (x:t) -> body) : ? { pre } *)
      let (| u, t_typing |) = check_universe f g t in
      let x = fresh g in
      let g' = (x, Inl t) :: g in
      let pre = open_term pre_hint x in
      (
        match check_tot f g' pre with
        | (| Tm_VProp, pre_typing |) ->
          let (| c_body, body_typing |) = check f g' (open_term body x) pre (E pre_typing) in
          if post_opt = None
          then 
            let tt = T_Abs g ppname x t u body c_body pre_hint post_opt t_typing body_typing in
            let tres = Tm_Arrow {binder_ty=t;binder_ppname=ppname} (close_comp c_body x) in
            (| C_Tot tres, tt |)
          else if C_ST? c_body
          then
            //
            // Post is annotatated
            // Check that it is equivalent to the inferred post,
            //   and replace the inferred post with it
            //
            let C_ST {u=u_c; res=res_c; pre=pre_c; post=post_c} = c_body in
            let y = fresh g' in
            let g_post = (y, Inl (comp_res c_body))::g' in
            //
            // we need to open post with x first
            //   (the binder of the lambda)
            // but since post is implicitly abstracted over
            //   the return value, we have to manually
            //   open the db index 1 to open with x :/
            //
            let post = open_term'
              (Some?.v post_opt)
              (Tm_Var {nm_ppname="_";nm_index=x})
              1 in
            let post_opened = open_term post y in

            (
             match check_tot f g_post post_opened with
             | (| Tm_VProp, post_typing |) ->

               let post_c = comp_post c_body in
               let post_c_opened = open_term post_c y in
               let post_c_typing : tot_typing f g_post post_c_opened Tm_VProp =
                 check_vprop f g_post post_c_opened in
               let post_c_post_eq : vprop_equiv f g_post post_c_opened post_opened =
                check_vprop_equiv f g_post post_c_opened post_opened post_c_typing in
               let c_body_with_post = C_ST {u=u_c;res=res_c;pre=pre_c;post=post} in

               let pre_c_typing : tot_typing f g' (comp_pre c_body) Tm_VProp =
                 check_vprop f g' pre_c in
               let res_c_typing : tot_typing f g' (comp_res c_body) (Tm_Type (comp_u c_body)) =
                 let (| u, ty |) = check_universe f g' res_c in
                 if u = u_c
                 then ty
                 else T.fail "T_Abs: re-typechecking the return type returned different universe" in
               let post_c_typing
                 : tot_typing f ((y, Inl (comp_res c_body))::g') (open_term (comp_post c_body) y) Tm_VProp
                 = post_c_typing in
               let c_and_c_with_post_pre_equiv
                 : vprop_equiv f g' (comp_pre c_body) (comp_pre c_body_with_post)
                 = VE_Refl g' _ in
               let c_and_c_with_post_post_equiv
                 : vprop_equiv f ((y, Inl (comp_res c_body))::g')
                                 (open_term (comp_post c_body) y)
                                 (open_term (comp_post c_body_with_post) y)
                 = post_c_post_eq in
               assume (is_pure_comp c_body_with_post);
               let st_eq: st_equiv f g' c_body c_body_with_post =
                 ST_VPropEquiv g' c_body c_body_with_post y pre_c_typing res_c_typing post_c_typing
                   c_and_c_with_post_pre_equiv c_and_c_with_post_post_equiv in

               let body_typing
                 : src_typing f g' (open_term body x) c_body_with_post
                 = T_Equiv g' (open_term body x) c_body c_body_with_post body_typing st_eq in
                 
               let tt = T_Abs g ppname x t u body c_body_with_post pre_hint post_opt t_typing body_typing in
               let tres = Tm_Arrow {binder_ty=t;binder_ppname=ppname} (close_comp c_body_with_post x) in
               (| C_Tot tres, tt |)
               
             | _ -> T.fail "T_Abs: failed to typecheck annotated post"
            )

          else T.fail "T_Abs: expected a stateful function (since post is annotated), found total"
          // (* could avoid this re-checking call if we had a lemma about arrow typing *)
          // let (| ures, ures_ty |) = check_universe f g tres in
          // let c = return_comp_noeq ures tres in
          // let d = T_ReturnNoEq _ _ _ _ tt ures_ty in
          // frame_empty ures tres ures_ty _ c d
          
        | _ -> T.fail "bad hint"
      )

    | Tm_STApp head arg ->
      let (| ty_head, dhead |) = check_tot f g head in
      let (| ty_arg, darg |) = check_tot f g arg in      
      begin
      match ty_head with
      | Tm_Arrow {binder_ty=formal;binder_ppname=ppname} (C_ST res) ->
        if ty_arg <> formal
        then T.fail "Type of formal parameter does not match type of argument"
        else let d = T_STApp g head ppname formal (C_ST res) arg dhead (E darg) in
             opening_pure_comp_with_pure_term (C_ST res) arg 0;
             repack (try_frame_pre pre_typing d)
      | _ -> T.fail "Unexpected head type in impure application"
      end

    | Tm_Bind t e1 e2 ->
      let (| c1, d1 |) = force_st pre_typing (check f g e1 pre pre_typing) in
      let C_ST s1 = c1 in
      if t <> s1.res 
      then T.fail "Annotated type of let-binding is incorrect"
      else (
        match check_tot f g t with
        | (| Tm_Type u, t_typing |) ->
          if u <> s1.u then T.fail "incorrect universe"
          else (
            let x = fresh g in
            let next_pre = open_term s1.post x in
            let g' = (x, Inl s1.res)::g in
            let next_pre_typing : tot_typing f g' next_pre Tm_VProp =
                //would be nice to prove that this is typable as a lemma,
                //without having to re-check it
                match check_tot f g' next_pre with
                | (| Tm_VProp, nt |) -> E nt
                | _ -> T.fail "next pre is not typable"
            in
            let (| c2, d2 |) = force_st next_pre_typing (check f g' (open_term e2 x) next_pre next_pre_typing) in
            let C_ST s2 = c2 in
            let (| u, res_typing |) = check_universe f g s2.res in
            if u <> s2.u
            then T.fail "Unexpected universe for result type"
            else if x `Set.mem` freevars s2.post
            then T.fail (Printf.sprintf "Bound variable %d escapes scope in postcondition %s" x (P.term_to_string s2.post))
            else (
              match check_tot f ((x, Inl s2.res)::g) (open_term s2.post x) with
              | (| Tm_VProp, post_typing |) ->
                let bc : bind_comp f g x c1 c2 _ = (Bind_comp g x c1 c2 res_typing x (E post_typing)) in
              (| _, T_Bind _ _ _ _ _ _ _ d1 (E t_typing) d2 bc |)
            | _ -> T.fail "Ill-typed postcondition in bind"
            )
          )
        | (| ty, _ |) -> 
          T.fail (Printf.sprintf "Ill-typed annotated type %s on `bind`; has type %s\n"
                                 (P.term_to_string t)
                                 (P.term_to_string ty))
                                     
      )
    | Tm_If _ _ _ ->
      T.fail "Not handling if yet"
#pop-options
