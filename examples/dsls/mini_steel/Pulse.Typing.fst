module Pulse.Typing
module RT = Refl.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure

module FTB = FStar.Tactics

// let fstar_env =
//   g:R.env { 
//     RT.lookup_fvar g RT.bool_fv == Some (RT.tm_type RT.u_zero) /\
//     RT.lookup_fvar g vprop_fv == Some (RT.tm_type (elab_universe (U_succ (U_succ U_zero)))) /\
//     (forall (u1 u2:R.universe). RT.lookup_fvar_uinst g bind_fv [u1; u2] == Some (bind_type u1 u2))
//     ///\ star etc
//   }

let tm_unit : pure_term = Tm_FVar unit_lid
let tm_bool : pure_term = Tm_FVar bool_lid
let tm_true : pure_term = Tm_Constant (Bool true)
let tm_false : pure_term = Tm_Constant (Bool false)

let mk_eq2 (u:universe)
           (t:pure_term)
           (e0 e1:pure_term) 
  : pure_term
  = Tm_PureApp
         (Tm_PureApp (Tm_PureApp (Tm_UInst R.eq2_qn [u]) (Some Implicit) t)
                     None e0) None e1

let mk_vprop_eq (e0 e1:pure_term) : pure_term =
  mk_eq2 (U_succ (U_succ U_zero)) Tm_VProp e0 e1

let return_comp (u:universe) (t:pure_term) (e:pure_term)
  : pure_comp 
  = C_ST { u;
           res = t;
           pre = Tm_Emp;
           post = Tm_Pure (mk_eq2 u t (null_bvar 0) e) }

let return_comp_noeq (u:universe) (t:pure_term)
  : pure_comp 
  = C_ST { u;
           res = t;
           pre = Tm_Emp;
           post = Tm_Emp }

let eqn = pure_term & pure_term & pure_term
let binding = either pure_term eqn
let env = list (var & binding)

//
// THIS IS BROKEN:
//
// It is always setting universe to 0
// But we are also not using it currently
//
let elab_eqn (e:eqn)
  : R.term
  = let ty, l, r = e in
    let ty = elab_pure ty in
    let l = elab_pure l in
    let r = elab_pure r in
    RT.eq2 (R.pack_universe R.Uv_Zero) ty l r

let elab_binding (b:binding)
  : R.term 
  = match b with
    | Inl t -> elab_pure t
    | Inr eqn -> elab_eqn eqn

module L = FStar.List.Tot
let extend_env_l (f:R.env) (g:env) : R.env = 
  L.fold_right 
    (fun (x, b) g ->  
      let t = elab_binding b in
      RT.extend_env g x t)
     g
     f

let rec lookup (e:list (var & 'a)) (x:var)
  : option 'a
  = match e with
    | [] -> None
    | (y, v) :: tl -> if x = y then Some v else lookup tl x

let lookup_ty (e:env) (x:var)
  : option pure_term
  = match lookup e x with
    | Some (Inl t) -> Some t
    | _ -> None

let max (n1 n2:nat) = if n1 < n2 then n2 else n1

let rec fresh (e:list (var & 'a))
  : var
  = match e with
    | [] -> 0
    | (y, _) :: tl ->  max (fresh tl) y + 1
    | _ :: tl -> fresh tl

let rec fresh_not_mem (e:list (var & 'a)) (elt: (var & 'a))
  : Lemma (ensures L.memP elt e ==> fresh e > fst elt)
  = match e with
    | [] -> ()
    | hd :: tl -> fresh_not_mem tl elt
  
let rec lookup_mem (e:list (var & 'a)) (x:var)
  : Lemma
    (requires Some? (lookup e x))
    (ensures exists elt. L.memP elt e /\ fst elt == x)
  = match e with
    | [] -> ()
    | hd :: tl -> 
      match lookup tl x with
      | None -> assert (L.memP hd e)
      | _ -> 
        lookup_mem tl x;
        eliminate exists elt. L.memP elt tl /\ fst elt == x
        returns _
        with _ . ( 
          introduce exists elt. L.memP elt e /\ fst elt == x
          with elt
          and ()
        )

let fresh_is_fresh (e:env)
  : Lemma (None? (lookup e (fresh e)))
          [SMTPat (lookup e (fresh e))]
  =  match lookup e (fresh e) with
     | None -> ()
     | Some _ ->
       lookup_mem e (fresh e);
       FStar.Classical.forall_intro (fresh_not_mem e)

[@@ erasable; no_auto_projectors]
noeq
type vprop_equiv (f:RT.fstar_top_env) : env -> pure_term -> pure_term -> Type =
  | VE_Refl:
     g:env ->
     t:pure_term ->
     vprop_equiv f g t t

  | VE_Sym:
     g:env ->
     t1:pure_term -> 
     t2:pure_term -> 
     vprop_equiv f g t1 t2 ->
     vprop_equiv f g t2 t1

  | VE_Trans:
     g:env ->
     t0:pure_term ->
     t1:pure_term ->
     t2:pure_term ->
     vprop_equiv f g t0 t1 ->
     vprop_equiv f g t1 t2 ->
     vprop_equiv f g t0 t2

  | VE_Ctxt:
     g:env ->
     t0:pure_term -> 
     t1:pure_term -> 
     t0':pure_term -> 
     t1':pure_term ->
     vprop_equiv f g t0 t0' ->
     vprop_equiv f g t1 t1' ->
     vprop_equiv f g (Tm_Star t0 t1) (Tm_Star t0' t1')
     
  | VE_Unit: (*   *)
     g:env ->
     t:pure_term ->
     vprop_equiv f g (Tm_Star Tm_Emp t) t

  | VE_Comm:
     g:env ->
     t0:pure_term ->
     t1:pure_term ->
     vprop_equiv f g (Tm_Star t0 t1) (Tm_Star t1 t0)
     
  | VE_Assoc:
     g:env ->
     t0:pure_term ->
     t1:pure_term ->
     t2:pure_term ->
     vprop_equiv f g (Tm_Star t0 (Tm_Star t1 t2)) (Tm_Star (Tm_Star t0 t1) t2)

  | VE_Ext:
     g:env ->
     t0:pure_term ->
     t1:pure_term ->
     FTB.prop_validity_token (extend_env_l f g) (elab_pure (mk_vprop_eq t0 t1)) ->
     vprop_equiv f g t0 t1

  // | VE_Ex:
  //    g:env ->
  //    x:var { None? (lookup_ty g x) } ->
  //    ty:pure_term ->
  //    t0:pure_term ->
  //    t1:pure_term ->
  //    vprop_equiv f ((x, Inl ty)::g) (open_term t0 x) (open_term t1 x) ->
  //    vprop_equiv f g (Tm_ExistsSL ty t0) (Tm_ExistsSL ty t1)

  // | VE_Fa:
  //    g:env ->
  //    x:var { None? (lookup_ty g x) } ->
  //    ty:pure_term ->
  //    t0:pure_term ->
  //    t1:pure_term ->
  //    vprop_equiv f ((x, Inl ty)::g) (open_term t0 x) (open_term t1 x) ->
  //    vprop_equiv f g (Tm_ForallSL ty t0) (Tm_ForallSL ty t1)


let add_frame (s:pure_comp_st) (frame:pure_term)
  : pure_comp_st =

  let add_frame_s (s:st_comp) : st_comp =
    { s with pre = Tm_Star s.pre frame;
             post = Tm_Star s.post frame } in

  match s with
  | C_ST s -> C_ST (add_frame_s s)
  | C_STAtomic inames s -> C_STAtomic inames (add_frame_s s)
  | C_STGhost inames s -> C_STGhost inames (add_frame_s s)

let close_pure_comp (c:pure_comp) (x:var) : pure_comp = close_comp c x

//
// TODO: there is a observability flag upcoming in the underlying steel framework
//       the bind will then also allow for (statomic unobservable, statomic observable)
//       and the symmetric one
//
let bind_comp_compatible (c1 c2:pure_comp_st) : prop =
  match c1, c2 with
  | C_STGhost inames1 _, C_STGhost inames2 _ -> inames1 == inames2
  | C_ST _, C_ST _ -> True
  | _, _ -> False

let bind_comp_pre (x:var) (c1 c2:pure_comp_st) : prop =
  open_term (comp_post c1) x == comp_pre c2 /\
  (~ (x `Set.mem` freevars (comp_post c2))) /\  //x doesn't escape in the result type
  bind_comp_compatible c1 c2

let bind_comp_out (c1:pure_comp_st) (c2:pure_comp_st{bind_comp_compatible c1 c2})
  : pure_comp_st =
  let s = {u=comp_u c2; res=comp_res c2; pre=comp_pre c1; post=comp_post c2} in
  match c1, c2 with
  | C_STGhost inames _, C_STGhost _ _ -> C_STGhost inames s
  | C_ST _, C_ST _ -> C_ST s

let bind_comp_ghost_l_compatible (c1 c2:pure_comp_st) : prop =
  match c1, c2 with
  | C_STGhost inames1 _, C_STAtomic inames2 _ -> inames1 == inames2
  | _, _ -> False

let bind_comp_ghost_l_pre (x:var) (c1 c2:pure_comp_st) : prop =
  open_term (comp_post c1) x == comp_pre c2 /\
  (~ (x `Set.mem` freevars (comp_post c2))) /\  //x doesn't escape in the result type
  bind_comp_ghost_l_compatible c1 c2

let bind_comp_ghost_l_out (c1:pure_comp_st) (c2:pure_comp_st{bind_comp_ghost_l_compatible c1 c2})
  : pure_comp_st =
  let s = {u=comp_u c2; res=comp_res c2; pre=comp_pre c1; post=comp_post c2} in
  match c1, c2 with
  | C_STGhost inames _, C_STAtomic _ _ -> C_STAtomic inames s

let bind_comp_ghost_r_compatible (c1 c2:pure_comp_st) : prop =
  match c1, c2 with
  | C_STAtomic inames1 _, C_STGhost inames2 _ -> inames1 == inames2
  | _, _ -> False

let bind_comp_ghost_r_pre (x:var) (c1 c2:pure_comp_st) : prop =
  open_term (comp_post c1) x == comp_pre c2 /\
  (~ (x `Set.mem` freevars (comp_post c2))) /\  //x doesn't escape in the result type
  bind_comp_ghost_r_compatible c1 c2

let bind_comp_ghost_r_out (c1:pure_comp_st) (c2:pure_comp_st{bind_comp_ghost_r_compatible c1 c2})
  : pure_comp_st =
  let s = {u=comp_u c2; res=comp_res c2; pre=comp_pre c1; post=comp_post c2} in
  match c1, c2 with
  | C_STAtomic inames _, C_STGhost _ _ -> C_STAtomic inames s

let st_equiv_pre (c1 c2:pure_comp_st) : prop =
  comp_u c1 == comp_u c2 /\ comp_res c1 == comp_res c2 /\
  (match c1, c2 with
   | C_ST _, C_ST _ -> True
   | C_STAtomic inames1 _, C_STAtomic inames2 _ ->
     inames1 == inames2
   | C_STGhost inames1 _, C_STGhost inames2 _ ->
     inames1 == inames2
   | _, _ -> False)

let non_informative_witness_t (u:universe) (t:pure_term) : pure_term =
  Tm_PureApp (Tm_UInst non_informative_witness_lid [u])
             None
             t

let comp_elim_exists (u:universe) (t:pure_term) (p:pure_term)
  : pure_comp =

  C_STGhost Tm_EmpInames {
    u=u;
    res=t;
    pre=Tm_ExistsSL u t p;
    post=p
  }

let comp_intro_exists (u:universe) (t:pure_term) (p:pure_term) (e:pure_term)
  : pure_comp =

  assert (is_pure_term (open_term' p e 0));
  C_STGhost Tm_EmpInames {
    u=U_zero;
    res=tm_unit;
    pre=open_term' p e 0;
    post=Tm_ExistsSL u t p
  }

[@@erasable]
noeq
type my_erased (a:Type) = | E of a

#push-options "--z3rlimit_factor 2"
[@@ no_auto_projectors]
noeq
type src_typing (f:RT.fstar_top_env) : env -> term -> pure_comp -> Type =
  | T_Tot: 
      g:env ->
      e:pure_term ->
      ty:pure_term ->
      RT.typing (extend_env_l f g) (elab_pure e) (elab_pure ty) ->
      src_typing f g e (C_Tot ty)

  | T_Abs: 
      g:env ->
      ppname:ppname ->
      x:var { None? (lookup g x) } ->
      q:option qualifier ->
      ty:pure_term ->
      u:universe ->
      body:term {~ (x `Set.mem` freevars body) } ->
      c:pure_comp ->
      tot_typing f g ty (Tm_Type u) ->
      src_typing f ((x, Inl ty)::g) (open_term body x) c ->
      src_typing f g (Tm_Abs {binder_ty=ty;binder_ppname=ppname} q None body None)
                     (C_Tot (Tm_Arrow {binder_ty=ty;binder_ppname=ppname} q (close_pure_comp c x)))
  
  | T_STApp :
      g:env ->
      head:term ->
      ppname:ppname ->
      formal:pure_term ->
      q:option qualifier ->
      res:pure_comp {stateful_comp res} ->
      arg:pure_term ->
      src_typing f g head (C_Tot (Tm_Arrow {binder_ty=formal;binder_ppname=ppname} q res)) ->
      tot_typing f g arg formal ->
      src_typing f g (Tm_STApp head q arg) (open_comp_with res arg)

  | T_Return:
      g:env ->
      e:pure_term -> 
      t:pure_term -> 
      u:universe ->
      tot_typing f g e t ->
      universe_of f g t u ->
      src_typing f g e (return_comp u t e)

  | T_ReturnNoEq:
      g:env ->
      e:term -> 
      t:pure_term -> 
      u:universe ->
      src_typing f g e (C_Tot t) ->
      universe_of f g t u ->
      src_typing f g e (return_comp_noeq u t)

  | T_Lift:
      g:env ->
      e:term ->
      c1:pure_comp_st ->
      c2:pure_comp_st ->
      src_typing f g e c1 ->
      lift_comp f g c1 c2 ->
      src_typing f g e c2

  | T_Bind:
      g:env ->
      e1:term ->
      e2:term ->
      c1:pure_comp_st ->
      c2:pure_comp_st ->
      x:var { None? (lookup g x)  /\ ~(x `Set.mem` freevars e2) } ->
      c:pure_comp ->
      src_typing f g e1 c1 ->
      tot_typing f g (comp_res c1) (Tm_Type (comp_u c1)) -> //type-correctness; would be nice to derive it instead      
      src_typing f ((x, Inl (comp_res c1))::g) (open_term e2 x) c2 ->
      bind_comp f g x c1 c2 c ->
      src_typing f g (Tm_Bind e1 e2) c

  | T_If:
      g:env ->
      b:pure_term -> 
      e1:term ->
      e2:term ->
      c:pure_comp_st ->
      hyp:var { None? (lookup g hyp) } ->
      tot_typing f g b tm_bool ->
      src_typing f ((hyp, Inl (mk_eq2 U_zero tm_bool b tm_true)) :: g) e1 c ->
      src_typing f ((hyp, Inl (mk_eq2 U_zero tm_bool b tm_false)) :: g) e2 c ->
      src_typing f g (Tm_If b e1 e2 None) c

  | T_Frame:
      g:env ->
      e:term ->
      c:pure_comp_st ->
      frame:pure_term ->
      tot_typing f g frame Tm_VProp ->
      src_typing f g e c ->
      src_typing f g e (add_frame c frame)

  | T_Equiv:
      g:env ->
      e:term ->
      c:pure_comp ->
      c':pure_comp ->      
      src_typing f g e c ->
      st_equiv f g c c' ->
      src_typing f g e c'

  | T_ElimExists:
      g:env ->
      u:universe ->
      t:pure_term ->
      p:pure_term ->
      tot_typing f g t (Tm_Type u) ->
      tot_typing f g (Tm_ExistsSL u t p) Tm_VProp ->
      src_typing f g (Tm_ElimExists (Tm_ExistsSL u t p))
                     (comp_elim_exists u t p)

  | T_IntroExists:
      g:env ->
      u:universe ->
      t:pure_term ->
      p:pure_term ->
      e:pure_term ->
      tot_typing f g t (Tm_Type u) ->
      tot_typing f g (Tm_ExistsSL u t p) Tm_VProp ->
      tot_typing f g e t ->
      src_typing f g (Tm_IntroExists e (Tm_ExistsSL u t p))
                     (comp_intro_exists u t p e)

and tot_typing (f:RT.fstar_top_env) (g:env) (e:term) (t:pure_term) =
  my_erased (src_typing f g e (C_Tot t))

and universe_of (f:RT.fstar_top_env) (g:env) (t:term) (u:universe) =
  tot_typing f g t (Tm_Type u)

and bind_comp (f:RT.fstar_top_env) : env -> var -> pure_comp -> pure_comp -> pure_comp -> Type =
  | Bind_comp :  // (C_ST and C_ST) or (C_STGhost and C_STGhost)
    g:env ->
    x:var { None? (lookup g x) } ->
    c1:pure_comp_st ->
    c2:pure_comp_st {bind_comp_pre x c1 c2} ->
    universe_of f g (comp_res c2) (comp_u c2) ->
    //or in the result post; free var check isn't enough; we need typability
    y:var { None? (lookup g y) /\ ~(y `Set.mem` freevars (comp_post c2)) } ->      
    tot_typing f ((y, Inl (comp_res c2)) :: g) (open_term (comp_post c2) y) Tm_VProp ->
    bind_comp f g x c1 c2 (bind_comp_out c1 c2)

  | Bind_comp_ghost_l :  // (C_STGhost and C_STAtomic)
    g:env ->
    x:var { None? (lookup g x) } ->
    c1:pure_comp_st ->
    c2:pure_comp_st {bind_comp_ghost_l_pre x c1 c2} ->
    non_informative_c1:(w:pure_term & src_typing f g w (C_Tot (non_informative_witness_t (comp_u c1) (comp_res c1)))) ->
    universe_of f g (comp_res c2) (comp_u c2) ->
    //or in the result post; free var check isn't enough; we need typability
    y:var { None? (lookup g y) /\ ~(y `Set.mem` freevars (comp_post c2)) } ->
    tot_typing f ((y, Inl (comp_res c2)) :: g) (open_term (comp_post c2) y) Tm_VProp ->
    bind_comp f g x c1 c2 (bind_comp_ghost_l_out c1 c2)

  | Bind_comp_ghost_r :  // (C_STAtomic and C_STGhost)
    g:env ->
    x:var { None? (lookup g x) } ->
    c1:pure_comp_st ->
    c2:pure_comp_st {bind_comp_ghost_r_pre x c1 c2} ->
    non_informative_c2:(w:pure_term & src_typing f g w (C_Tot (non_informative_witness_t (comp_u c2) (comp_res c2)))) ->
    universe_of f g (comp_res c2) (comp_u c2) ->
    //or in the result post; free var check isn't enough; we need typability
    y:var { None? (lookup g y) /\ ~(y `Set.mem` freevars (comp_post c2)) } ->
    tot_typing f ((y, Inl (comp_res c2)) :: g) (open_term (comp_post c2) y) Tm_VProp ->
    bind_comp f g x c1 c2 (bind_comp_ghost_r_out c1 c2)

and lift_comp (f:RT.fstar_top_env) : env -> pure_comp -> pure_comp -> Type =
  | Lift_STAtomic_ST :
    g:env ->
    c:pure_comp_st{C_STAtomic? c /\ comp_inames c == Tm_EmpInames} ->
    lift_comp f g c (C_ST (st_comp_of_comp c))

  | Lift_STGhost_STAtomic :
    g:env ->
    c:pure_comp_st{C_STGhost? c} ->
    non_informative_c:(w:pure_term & src_typing f g w (C_Tot (non_informative_witness_t (comp_u c) (comp_res c)))) ->
    lift_comp f g c (C_STAtomic (comp_inames c) (st_comp_of_comp c))

and st_equiv (f:RT.fstar_top_env) : env -> pure_comp -> pure_comp -> Type =
  | ST_VPropEquiv :
      g:env ->
      c1:pure_comp_st ->
      c2:pure_comp_st { st_equiv_pre c1 c2 } -> 
      x:var { None? (lookup g x) } ->
      tot_typing f g (comp_pre c1) Tm_VProp ->
      tot_typing f g (comp_res c1) (Tm_Type (comp_u c1)) ->
      tot_typing f ((x, Inl (comp_res c1))::g) (open_term (comp_post c1) x) Tm_VProp ->
      vprop_equiv f g (comp_pre c1) (comp_pre c2) ->
      vprop_equiv f ((x, Inl (comp_res c1))::g) 
                    (open_term (comp_post c1) x)
                    (open_term (comp_post c2) x) ->      
      st_equiv f g c1 c2
#pop-options

(* this requires some metatheory on Refl.Typing

     G |- fv e : t

    G(fv) = t0 -> t1

     G |- e : t0
     G |- t1 <: t



    G |- e0 e1 : t ==>

   exists t0 t1.
    G |- e0 : t0 -> t1 /\
    G |- e1 : t0

*)
let star_typing_inversion (f:_) (g:_) (t0 t1:term) (d:tot_typing f g (Tm_Star t0 t1) Tm_VProp)
  : (tot_typing f g t0 Tm_VProp &
     tot_typing f g t1 Tm_VProp)
  = admit()

let vprop_eq_typing_inversion (f:RT.fstar_top_env) g (t0 t1:pure_term)
  (token:FTB.prop_validity_token (extend_env_l f g) (elab_pure (mk_vprop_eq t0 t1)))
  : (tot_typing f g t0 Tm_VProp &
     tot_typing f g t1 Tm_VProp)
  = admit ()

(* These I can easily prove *)
let star_typing (#f:_) (#g:_) (#t0 #t1:term)
                (d0:tot_typing f g t0 Tm_VProp)
                (d1:tot_typing f g t1 Tm_VProp)
  : tot_typing f g (Tm_Star t0 t1) Tm_VProp
  = admit()

let emp_typing (#f:_) (#g:_) 
  : tot_typing f g Tm_Emp Tm_VProp
  = admit()

let rec vprop_equiv_typing (f:_) (g:_) (t0 t1:pure_term) (v:vprop_equiv f g t0 t1)
  : GTot ((tot_typing f g t0 Tm_VProp -> tot_typing f g t1 Tm_VProp) &
          (tot_typing f g t1 Tm_VProp -> tot_typing f g t0 Tm_VProp))
        (decreases v)
  = match v with
    | VE_Refl _ _ -> (fun x -> x), (fun x -> x)

    | VE_Sym _ _ _ v' -> 
      let f, g = vprop_equiv_typing f g t1 t0 v' in
      g, f

    | VE_Trans g t0 t2 t1 v02 v21 ->
      let f02, f20 = vprop_equiv_typing _ _ _ _ v02 in
      let f21, f12 = vprop_equiv_typing _ _ _ _ v21 in
      (fun x -> f21 (f02 x)), 
      (fun x -> f20 (f12 x))

    | VE_Ctxt g s0 s1 s0' s1' v0 v1 ->
      let f0, f0' = vprop_equiv_typing _ _ _ _ v0 in
      let f1, f1' = vprop_equiv_typing _ _ _ _ v1 in      
      let ff (x:tot_typing f g (Tm_Star s0 s1) Tm_VProp)
        : tot_typing f g (Tm_Star s0' s1') Tm_VProp
        = let s0_typing, s1_typing = star_typing_inversion _ _ _ _ x in
          let s0'_typing, s1'_typing = f0 s0_typing, f1 s1_typing in
          star_typing s0'_typing s1'_typing
      in
      let gg (x:tot_typing f g (Tm_Star s0' s1') Tm_VProp)
        : tot_typing f g (Tm_Star s0 s1) Tm_VProp
        = let s0'_typing, s1'_typing = star_typing_inversion _ _ _ _ x in
          star_typing (f0' s0'_typing) (f1' s1'_typing)        
      in
      ff, gg

    | VE_Unit g t ->
      let fwd (x:tot_typing f g (Tm_Star Tm_Emp t) Tm_VProp)
        : tot_typing f g t Tm_VProp
        = let _, r = star_typing_inversion _ _ _ _ x in
          r
      in
      let bk (x:tot_typing f g t Tm_VProp)
        : tot_typing f g (Tm_Star Tm_Emp t) Tm_VProp
        = star_typing emp_typing x
      in
      fwd, bk

    | VE_Comm g t0 t1 ->
      let f t0 t1 (x:tot_typing f g (Tm_Star t0 t1) Tm_VProp)
        : tot_typing f g (Tm_Star t1 t0) Tm_VProp
        = let tt0, tt1 = star_typing_inversion _ _ _ _ x in
          star_typing tt1 tt0
      in
      f t0 t1, f t1 t0

    | VE_Assoc g t0 t1 t2 ->
      let fwd (x:tot_typing f g (Tm_Star t0 (Tm_Star t1 t2)) Tm_VProp)
        : tot_typing f g (Tm_Star (Tm_Star t0 t1) t2) Tm_VProp
        = let tt0, tt12 = star_typing_inversion _ _ _ _ x in
          let tt1, tt2 = star_typing_inversion _ _ _ _ tt12 in
          star_typing (star_typing tt0 tt1) tt2
      in
      let bk (x : tot_typing f g (Tm_Star (Tm_Star t0 t1) t2) Tm_VProp)
        : tot_typing f g (Tm_Star t0 (Tm_Star t1 t2)) Tm_VProp
        = let tt01, tt2 = star_typing_inversion _ _ _ _ x in
          let tt0, tt1 = star_typing_inversion _ _ _ _ tt01 in
          star_typing tt0 (star_typing tt1 tt2)
      in
      fwd, bk
   
    | VE_Ext g t0 t1 token ->
      let d1, d2 = vprop_eq_typing_inversion f g t0 t1 token in
      (fun _ -> d2),
      (fun _ -> d1)
