module Pulse.Typing
module RT = FStar.Reflection.Typing
module R = FStar.Reflection
open Pulse.Reflection.Util
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

let tm_unit = Tm_FVar unit_lid
let tm_bool = Tm_FVar bool_lid
let tm_true = Tm_Constant (Bool true)
let tm_false = Tm_Constant (Bool false)

let mk_erased (u:universe) (t:term) : term =
  let hd = Tm_UInst erased_lid [u] in
  Tm_PureApp hd None t

let mk_reveal (u:universe) (t:term) (e:term) : term =
  let hd = Tm_UInst reveal_lid [u] in
  let hd = Tm_PureApp hd (Some Implicit) t in
  Tm_PureApp hd None e

let mk_eq2 (u:universe)
           (t:term)
           (e0 e1:term) 
  : term
  = Tm_PureApp
         (Tm_PureApp (Tm_PureApp (Tm_UInst R.eq2_qn [u]) (Some Implicit) t)
                     None e0) None e1

let mk_eq2_prop (u:universe)
           (t:term)
           (e0 e1:term) 
  : term
  = Tm_PureApp
         (Tm_PureApp (Tm_PureApp (Tm_UInst (mk_steel_wrapper_lid "eq2_prop") [u]) (Some Implicit) t)
                     None e0) None e1


let mk_vprop_eq (e0 e1:term) : term =
  mk_eq2 (U_succ (U_succ U_zero)) Tm_VProp e0 e1

let comp_return (c:ctag) (use_eq:bool) (u:universe) (t:term) (e:term) (post:term) (x:var)
  : comp =

  let post_maybe_eq =
    if use_eq
    then let post = open_term' post (null_var x) 0 in
         let post = Tm_Star post (Tm_Pure (mk_eq2_prop u t (null_var x) e)) in
         close_term post x
    else post in

  match c with
  | STT ->
    C_ST { u; res = t; pre = open_term' post e 0; post = post_maybe_eq }
  | STT_Atomic ->
    C_STAtomic Tm_EmpInames
      { u; res = t; pre = open_term' post e 0; post = post_maybe_eq }
  | STT_Ghost ->
    C_STGhost Tm_EmpInames
      { u; res = t; pre = open_term' post e 0; post = post_maybe_eq }

let eqn = term & term & term
let binding = either term eqn
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
    let ty = elab_term ty in
    let l = elab_term l in
    let r = elab_term r in
    RT.eq2 (R.pack_universe R.Uv_Zero) ty l r

let elab_binding (b:binding)
  : R.term 
  = match b with
    | Inl t -> elab_term t
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
  : option term
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
type vprop_equiv (f:RT.fstar_top_env) : env -> term -> term -> Type =
  | VE_Refl:
     g:env ->
     t:term ->
     vprop_equiv f g t t

  | VE_Sym:
     g:env ->
     t1:term -> 
     t2:term -> 
     vprop_equiv f g t1 t2 ->
     vprop_equiv f g t2 t1

  | VE_Trans:
     g:env ->
     t0:term ->
     t1:term ->
     t2:term ->
     vprop_equiv f g t0 t1 ->
     vprop_equiv f g t1 t2 ->
     vprop_equiv f g t0 t2

  | VE_Ctxt:
     g:env ->
     t0:term -> 
     t1:term -> 
     t0':term -> 
     t1':term ->
     vprop_equiv f g t0 t0' ->
     vprop_equiv f g t1 t1' ->
     vprop_equiv f g (Tm_Star t0 t1) (Tm_Star t0' t1')
     
  | VE_Unit: (*   *)
     g:env ->
     t:term ->
     vprop_equiv f g (Tm_Star Tm_Emp t) t

  | VE_Comm:
     g:env ->
     t0:term ->
     t1:term ->
     vprop_equiv f g (Tm_Star t0 t1) (Tm_Star t1 t0)
     
  | VE_Assoc:
     g:env ->
     t0:term ->
     t1:term ->
     t2:term ->
     vprop_equiv f g (Tm_Star t0 (Tm_Star t1 t2)) (Tm_Star (Tm_Star t0 t1) t2)

  | VE_Ext:
     g:env ->
     t0:term ->
     t1:term ->
     FTB.equiv_token (extend_env_l f g) (elab_term t0) (elab_term t1) ->
     vprop_equiv f g t0 t1

  // | VE_Ex:
  //    g:env ->
  //    x:var { None? (lookup_ty g x) } ->
  //    ty:term ->
  //    t0:term ->
  //    t1:term ->
  //    vprop_equiv f ((x, Inl ty)::g) (open_term t0 x) (open_term t1 x) ->
  //    vprop_equiv f g (Tm_ExistsSL ty t0) (Tm_ExistsSL ty t1)

  // | VE_Fa:
  //    g:env ->
  //    x:var { None? (lookup_ty g x) } ->
  //    ty:term ->
  //    t0:term ->
  //    t1:term ->
  //    vprop_equiv f ((x, Inl ty)::g) (open_term t0 x) (open_term t1 x) ->
  //    vprop_equiv f g (Tm_ForallSL ty t0) (Tm_ForallSL ty t1)


let add_frame (s:comp_st) (frame:term)
  : comp_st
  = let add_frame_s (s:st_comp) : x:st_comp =
        { s with pre = Tm_Star s.pre frame;
                 post = Tm_Star s.post frame }
    in
    match s with
    | C_ST s -> C_ST (add_frame_s s)
    | C_STAtomic inames s -> C_STAtomic inames (add_frame_s s)
    | C_STGhost inames s -> C_STGhost inames (add_frame_s s)

//
// TODO: there is a observability flag upcoming in the underlying steel framework
//       the bind will then also allow for (statomic unobservable, statomic observable)
//       and the symmetric one
//
let bind_comp_compatible (c1 c2:comp_st)
  : prop
  = match c1, c2 with
    | C_STGhost inames1 _, C_STGhost inames2 _ -> inames1 == inames2
    | C_ST _, C_ST _ -> True
    | _, _ -> False

let bind_comp_pre (x:var) (c1 c2:comp_st)
  : prop
  = open_term (comp_post c1) x == comp_pre c2 /\
    (~ (x `Set.mem` freevars (comp_post c2))) /\  //x doesn't escape in the result type
    bind_comp_compatible c1 c2

let bind_comp_out (c1:comp_st) (c2:comp_st{bind_comp_compatible c1 c2})
  : comp_st
  = let s = {u=comp_u c2; res=comp_res c2; pre=comp_pre c1; post=comp_post c2} in
    match c1, c2 with
    | C_STGhost inames _, C_STGhost _ _ -> C_STGhost inames s
    | C_ST _, C_ST _ -> C_ST s

let bind_comp_ghost_l_compatible (c1 c2:comp_st)
  : prop
  = match c1, c2 with
    | C_STGhost inames1 _, C_STAtomic inames2 _ -> inames1 == inames2
    | _, _ -> False

let bind_comp_ghost_l_pre (x:var) (c1 c2:comp_st)
  : prop
  = open_term (comp_post c1) x == comp_pre c2 /\
    (~ (x `Set.mem` freevars (comp_post c2))) /\  //x doesn't escape in the result type
    bind_comp_ghost_l_compatible c1 c2

let bind_comp_ghost_l_out (c1:comp_st) (c2:comp_st{bind_comp_ghost_l_compatible c1 c2})
  : comp_st
  = let s = {u=comp_u c2; res=comp_res c2; pre=comp_pre c1; post=comp_post c2} in
    match c1, c2 with
    | C_STGhost inames _, C_STAtomic _ _ -> C_STAtomic inames s
  
let bind_comp_ghost_r_compatible (c1 c2:comp_st)
  : prop
  = match c1, c2 with
    | C_STAtomic inames1 _, C_STGhost inames2 _ -> inames1 == inames2
    | _, _ -> False

let bind_comp_ghost_r_pre (x:var) (c1 c2:comp_st)
  : prop
  = open_term (comp_post c1) x == comp_pre c2 /\
    (~ (x `Set.mem` freevars (comp_post c2))) /\  //x doesn't escape in the result type
    bind_comp_ghost_r_compatible c1 c2

let bind_comp_ghost_r_out (c1:comp_st) (c2:comp_st{bind_comp_ghost_r_compatible c1 c2})
  : comp_st
  = let s = {u=comp_u c2; res=comp_res c2; pre=comp_pre c1; post=comp_post c2} in
    match c1, c2 with
    | C_STAtomic inames _, C_STGhost _ _ -> C_STAtomic inames s

let st_equiv_pre (c1 c2:comp_st)
  : prop
  = comp_u c1 == comp_u c2 /\ comp_res c1 == comp_res c2 /\
    (match c1, c2 with
    | C_ST _, C_ST _ -> True
    | C_STAtomic inames1 _, C_STAtomic inames2 _ ->
      inames1 == inames2
    | C_STGhost inames1 _, C_STGhost inames2 _ ->
      inames1 == inames2
    | _, _ -> False)

let non_informative_witness_t (u:universe) (t:term)
  : term
  = Tm_PureApp (Tm_UInst non_informative_witness_lid [u])
               None
               t

let elim_exists_post (u:universe) (t:term) (p:term) (x:var)
  : term
  = let x_tm = null_var x in
    let p = open_term' p (mk_reveal u t x_tm) 0 in
    close_term p x

let comp_elim_exists (u:universe) (t:term) (p:term) (x:var)
  : comp
  = C_STGhost Tm_EmpInames 
              {
                u=u;
                res=mk_erased u t;
                pre=Tm_ExistsSL u t p should_elim_true;
                post=elim_exists_post u t p x
              }

let comp_intro_exists (u:universe) (t:term) (p:term) (e:term)
  : comp
  = C_STGhost Tm_EmpInames
              {
                u=U_zero;
                res=tm_unit;
                pre=open_term' p e 0;
                post=Tm_ExistsSL u t p should_elim_false
              }

let comp_intro_exists_erased (u:universe) (t:term) (p:term) (e:term)
  : comp
  = C_STGhost Tm_EmpInames
              {
                u=U_zero;
                res=tm_unit;
                pre=open_term' p (mk_reveal u t e) 0;
                post=Tm_ExistsSL u t p should_elim_false
              }

let comp_while_cond (inv:term)
  : comp
  = C_ST {
           u=U_zero;
           res=tm_bool;
           pre=Tm_ExistsSL U_zero tm_bool inv should_elim_false;
           post=inv
         }

let comp_while_body (inv:term)
  : comp
  = C_ST {
           u=U_zero;
           res=tm_unit;
           pre=open_term' inv tm_true 0;
           post=Tm_ExistsSL U_zero tm_bool inv should_elim_true
         }

let comp_while (inv:term)
  : comp
  = C_ST {
           u=U_zero;
           res=tm_unit;
           pre=Tm_ExistsSL U_zero tm_bool inv should_elim_true;
           post=open_term' inv tm_false 0
         }

let mk_tuple2 (u1 u2:universe) (t1 t2:term) : term =
  Tm_PureApp (Tm_PureApp (Tm_UInst tuple2_lid [u1; u2])
                         None
                         t1)
             None t2

let mk_fst (u1 u2:universe) (a1 a2 e:term) : term =
  Tm_PureApp (Tm_PureApp (Tm_PureApp (Tm_UInst fst_lid [u1; u2]) (Some Implicit) a1)
                         (Some Implicit) a2)
             None
             e

let mk_snd (u1 u2:universe) (a1 a2 e:term) : term =
  Tm_PureApp (Tm_PureApp (Tm_PureApp (Tm_UInst snd_lid [u1; u2]) (Some Implicit) a1)
                         (Some Implicit) a2)
             None
             e

let par_post (uL uR:universe) (aL aR postL postR:term) (x:var) : term =
  let x_tm = term_of_var x in
  
  let postL = open_term' postL (mk_fst uL uR aL aR x_tm) 0 in
  let postR = open_term' postR (mk_snd uL uR aL aR x_tm) 0 in
  let post = Tm_Star postL postR in
  close_term post x

let comp_par (cL:comp{C_ST? cL}) (cR:comp{C_ST? cR}) (x:var) : comp =
  let uL = comp_u cL in
  let uR = comp_u cR in
  let aL = comp_res cL in
  let aR = comp_res cR in

  let post = par_post uL uR aL aR (comp_post cL) (comp_post cR) x in

  C_ST {
    u = uL;
    res = mk_tuple2 uL uR aL aR;
    pre = Tm_Star (comp_pre cL) (comp_pre cR);
    post
  }

let comp_rewrite (p q:vprop) : comp =
  C_STGhost Tm_EmpInames {
			u = U_zero;
			res = tm_unit;
			pre = p;
			post = q;
		}

let comp_admit (c:ctag) (s:st_comp) : comp =
  match c with
  | STT -> C_ST s
  | STT_Atomic -> C_STAtomic Tm_EmpInames s
  | STT_Ghost -> C_STGhost Tm_EmpInames s

[@@erasable]
noeq
type my_erased (a:Type) = | E of a


let typing (f:RT.fstar_top_env) (g:env) (e:term) (t:term) =
    RT.typing (extend_env_l f g) (elab_term e) (elab_term t)

let tot_typing (f:RT.fstar_top_env) (g:env) (e:term) (t:term) =
    my_erased (typing f g e t)

let universe_of (f:RT.fstar_top_env) (g:env) (t:term) (u:universe) =
    tot_typing f g t (Tm_Type u)

let non_informative_t (f:RT.fstar_top_env) (g:env) (u:universe) (t:term) =
    w:term & tot_typing f g w (non_informative_witness_t u t)

let non_informative_c (f:RT.fstar_top_env) (g:env) (c:comp_st) =
    non_informative_t f g (comp_u c) (comp_res c)
     
let as_binder t = { binder_ty = t; binder_ppname = RT.pp_name_default }

[@@ no_auto_projectors]
noeq
type st_equiv (f:RT.fstar_top_env) : env -> comp -> comp -> Type =
  | ST_VPropEquiv :
      g:env ->
      c1:comp_st ->
      c2:comp_st { st_equiv_pre c1 c2 } -> 
      x:var { None? (lookup g x) /\ ~(x `Set.mem` freevars (comp_post c1)) /\ ~(x `Set.mem` freevars (comp_post c2)) } ->
      tot_typing f g (comp_pre c1) Tm_VProp ->
      tot_typing f g (comp_res c1) (Tm_Type (comp_u c1)) ->
      tot_typing f ((x, Inl (comp_res c1))::g) (open_term (comp_post c1) x) Tm_VProp ->
      vprop_equiv f g (comp_pre c1) (comp_pre c2) ->
      vprop_equiv f ((x, Inl (comp_res c1))::g) 
                    (open_term (comp_post c1) x)
                    (open_term (comp_post c2) x) ->      
      st_equiv f g c1 c2

[@@ no_auto_projectors]
noeq
type bind_comp (f:RT.fstar_top_env) : env -> var -> comp -> comp -> comp -> Type =
  | Bind_comp :  // (C_ST and C_ST) or (C_STGhost and C_STGhost)
      g:env ->
      x:var { None? (lookup g x) } ->
      c1:comp_st ->
      c2:comp_st {bind_comp_pre x c1 c2} ->
      universe_of f g (comp_res c2) (comp_u c2) ->
      //or in the result post; free var check isn't enough; we need typability
      y:var { None? (lookup g y) /\ ~(y `Set.mem` freevars (comp_post c2)) } ->      
      tot_typing f ((y, Inl (comp_res c2)) :: g) (open_term (comp_post c2) y) Tm_VProp ->
      bind_comp f g x c1 c2 (bind_comp_out c1 c2)

  | Bind_comp_ghost_l :  // (C_STGhost and C_STAtomic)
      g:env ->
      x:var { None? (lookup g x) } ->
      c1:comp_st ->
      c2:comp_st {bind_comp_ghost_l_pre x c1 c2} ->
      non_informative_c1:non_informative_c f g c1 ->
      universe_of f g (comp_res c2) (comp_u c2) ->
      //or in the result post; free var check isn't enough; we need typability
      y:var { None? (lookup g y) /\ ~(y `Set.mem` freevars (comp_post c2)) } ->
      tot_typing f ((y, Inl (comp_res c2)) :: g) (open_term (comp_post c2) y) Tm_VProp ->
      bind_comp f g x c1 c2 (bind_comp_ghost_l_out c1 c2)

  | Bind_comp_ghost_r :  // (C_STAtomic and C_STGhost)
      g:env ->
      x:var { None? (lookup g x) } ->
      c1:comp_st ->
      c2:comp_st {bind_comp_ghost_r_pre x c1 c2} ->
      non_informative_c2:non_informative_c f g c2 ->
      universe_of f g (comp_res c2) (comp_u c2) ->
      //or in the result post; free var check isn't enough; we need typability
      y:var { None? (lookup g y) /\ ~(y `Set.mem` freevars (comp_post c2)) } ->
      tot_typing f ((y, Inl (comp_res c2)) :: g) (open_term (comp_post c2) y) Tm_VProp ->
      bind_comp f g x c1 c2 (bind_comp_ghost_r_out c1 c2)

[@@ no_auto_projectors]
noeq
type lift_comp (f:RT.fstar_top_env) : env -> comp -> comp -> Type =
  | Lift_STAtomic_ST :
      g:env ->
      c:comp_st{C_STAtomic? c /\ comp_inames c == Tm_EmpInames} ->
      lift_comp f g c (C_ST (st_comp_of_comp c))

  | Lift_STGhost_STAtomic :
      g:env ->
      c:comp_st{C_STGhost? c} ->
      non_informative_c:non_informative_c f g c ->
      lift_comp f g c (C_STAtomic (comp_inames c) (st_comp_of_comp c))

[@@ no_auto_projectors]
noeq
type st_comp_typing (f:RT.fstar_top_env) : env -> st_comp -> Type =
  | STC:
      g:env -> 
      st:st_comp ->
      x:var { None? (lookup g x) /\ ~(x `Set.mem` freevars st.post) } ->
      universe_of f g st.res st.u ->
      tot_typing f g st.pre Tm_VProp ->
      tot_typing f ((x, Inl st.res)::g) (open_term st.post x) Tm_VProp ->
      st_comp_typing f g st

and comp_typing (f:RT.fstar_top_env) : env -> comp -> universe -> Type =
  | CT_Tot :
      g:env ->
      t:term ->
      u:universe ->
      universe_of f g t u ->
      comp_typing f g (C_Tot t) u

  | CT_ST :
      g:env -> 
      st:st_comp -> 
      st_comp_typing f g st ->
      comp_typing f g (C_ST st) st.u

  | CT_STAtomic :
      g:env -> 
      inames:term ->
      st:st_comp -> 
      tot_typing f g inames Tm_Inames ->
      st_comp_typing f g st ->
      comp_typing f g (C_STAtomic inames st) st.u

  | CT_STGhost :
      g:env -> 
      inames:term ->
      st:st_comp -> 
      tot_typing f g inames Tm_Inames ->      
      st_comp_typing f g st ->
      comp_typing f g (C_STGhost inames st) st.u

and st_typing (f:RT.fstar_top_env) : env -> st_term -> comp -> Type =
  // | T_Tot:
  //     g:env ->
  //     e:term ->
  //     ty:term ->
  //     tot_typing f g e ty ->
  //     st_typing f g (Tm_Return e) (C_Tot ty)

  | T_Abs: 
      g:env ->
      x:var { None? (lookup g x) } ->
      q:option qualifier ->
      ty:term ->
      u:universe ->
      body:st_term {~ (x `Set.mem` freevars_st body) } ->
      c:comp ->
      tot_typing f g ty (Tm_Type u) ->
      st_typing f ((x, Inl ty)::g) (open_st_term body x) c ->
      st_typing f g (Tm_Abs (as_binder ty) q None body None)
                    (C_Tot (Tm_Arrow (as_binder ty) q (close_comp c x)))
  
  | T_STApp :
      g:env ->
      head:term ->
      ty:term ->
      q:option qualifier ->
      res:comp_st ->
      arg:term ->
      tot_typing f g head (Tm_Arrow (as_binder ty) q res) ->
      tot_typing f g arg ty ->
      st_typing f g (Tm_STApp head q arg) (open_comp_with res arg)

  | T_Return:
      g:env ->
      c:ctag ->
      use_eq:bool ->
      u:universe ->
      t:term ->
      e:term ->
      post:term ->
      x:var { None? (lookup g x) /\ ~ (x `Set.mem` freevars post) } ->
      universe_of f g t u ->
      tot_typing f g e t ->
      tot_typing f ((x, Inl t)::g) (open_term post x) Tm_VProp ->
      st_typing f g (Tm_Return c use_eq e) (comp_return c use_eq u t e post x)

  | T_Lift:
      g:env ->
      e:st_term ->
      c1:comp_st ->
      c2:comp_st ->
      st_typing f g e c1 ->
      lift_comp f g c1 c2 ->
      st_typing f g e c2

  | T_Bind:
      g:env ->
      e1:st_term ->
      e2:st_term ->
      c1:comp_st ->
      c2:comp_st ->
      x:var { None? (lookup g x)  /\ ~(x `Set.mem` freevars_st e2) } ->
      c:comp ->
      st_typing f g e1 c1 ->
      tot_typing f g (comp_res c1) (Tm_Type (comp_u c1)) -> //type-correctness; would be nice to derive it instead      
      st_typing f ((x, Inl (comp_res c1))::g) (open_st_term e2 x) c2 ->
      bind_comp f g x c1 c2 c ->
      st_typing f g (Tm_Bind e1 e2) c

  | T_If:
      g:env ->
      b:term -> 
      e1:st_term ->
      e2:st_term ->
      c:comp_st ->
      uc:universe ->
      (* This is a little weird, we introduce a name hyp in the environment, 
         but the branches are not allowed to use it (except perhaps in a silent way for proofs).
         Maybe more natural to have one free var in e1,e2 and to open it with hyp?
         But that's also a change to FStar.Reflection.Typing
       *)
      hyp:var { None? (lookup g hyp) /\
               ~(hyp `Set.mem` (freevars_st e1 `Set.union` freevars_st e2))
              } ->
      tot_typing f g b tm_bool ->
      st_typing f ((hyp, Inl (mk_eq2 U_zero tm_bool b tm_true)) :: g) e1 c ->
      st_typing f ((hyp, Inl (mk_eq2 U_zero tm_bool b tm_false)) :: g) e2 c ->
      my_erased (comp_typing f g c uc) ->
      st_typing f g (Tm_If b e1 e2 None) c

  | T_Frame:
      g:env ->
      e:st_term ->
      c:comp_st ->
      frame:term ->
      tot_typing f g frame Tm_VProp ->
      st_typing f g e c ->
      st_typing f g e (add_frame c frame)

  | T_Equiv:
      g:env ->
      e:st_term ->
      c:comp ->
      c':comp ->      
      st_typing f g e c ->
      st_equiv f g c c' ->
      st_typing f g e c'

  | T_ElimExists:
      g:env ->
      u:universe ->
      t:term ->
      p:term ->
      x:var { None? (lookup g x) } ->
      tot_typing f g t (Tm_Type u) ->
      tot_typing f g (Tm_ExistsSL u t p should_elim_false) Tm_VProp ->
      st_typing f g (Tm_ElimExists (Tm_ExistsSL u t p should_elim_false))
                    (comp_elim_exists u t p x)

  | T_IntroExists:
      g:env ->
      u:universe ->
      t:term ->
      p:term ->
      e:term ->
      tot_typing f g t (Tm_Type u) ->
      tot_typing f g (Tm_ExistsSL u t p should_elim_false) Tm_VProp ->
      tot_typing f g e t ->
      st_typing f g (Tm_IntroExists false (Tm_ExistsSL u t p should_elim_false) [e])
                    (comp_intro_exists u t p e)

  | T_IntroExistsErased:
      g:env ->
      u:universe ->
      t:term ->
      p:term ->
      e:term ->
      tot_typing f g t (Tm_Type u) ->
      tot_typing f g (Tm_ExistsSL u t p should_elim_false) Tm_VProp ->
      tot_typing f g e (mk_erased u t)  ->
      st_typing f g (Tm_IntroExists true (Tm_ExistsSL u t p should_elim_false) [e])
                    (comp_intro_exists_erased u t p e)

  | T_While:
      g:env ->
      inv:term ->
      cond:st_term ->
      body:st_term ->
      tot_typing f g (Tm_ExistsSL U_zero tm_bool inv should_elim_false) Tm_VProp ->
      st_typing f g cond (comp_while_cond inv) ->
      st_typing f g body (comp_while_body inv) ->
      st_typing f g (Tm_While inv cond body) (comp_while inv)

  | T_Par:
      g:env ->
      eL:st_term ->
      cL:comp { C_ST? cL } ->
      eR:st_term ->
      cR:comp { C_ST? cR /\ comp_u cL == comp_u cR } ->
      x:var { None? (lookup g x) } ->
      // TODO: can comp_typing come from inversion of eL : cL and eR : cR?
      comp_typing f g cL (comp_u cL) ->
      comp_typing f g cR (comp_u cR) ->
      st_typing f g eL cL ->
      st_typing f g eR cR ->
      st_typing f g (Tm_Par Tm_Unknown eL Tm_Unknown Tm_Unknown eR Tm_Unknown)
                    (comp_par cL cR x)

  | T_Rewrite:
		    g:env ->
						p:vprop ->
						q:vprop ->
						tot_typing f g p Tm_VProp ->
						vprop_equiv f g p q ->
      st_typing f g (Tm_Rewrite p q) (comp_rewrite p q)

  | T_Admit:
      g:env ->
      s:st_comp ->
      c:ctag ->
      st_comp_typing f g s ->
      st_typing f g (Tm_Admit c s.u s.res None) (comp_admit c s)


(* this requires some metatheory on FStar.Reflection.Typing

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

let vprop_eq_typing_inversion (f:RT.fstar_top_env) g (t0 t1:term)
                              (token:FTB.equiv_token (extend_env_l f g)
                                                     (elab_term t0)
                                                     (elab_term t1))
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

let rec vprop_equiv_typing (f:_) (g:_) (t0 t1:term) (v:vprop_equiv f g t0 t1)
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
