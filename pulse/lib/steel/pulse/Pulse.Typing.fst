module Pulse.Typing
module RT = FStar.Reflection.Typing
module R = FStar.Reflection
open Pulse.Reflection.Util
module L = FStar.List.Tot
open FStar.List.Tot
open Pulse.Syntax
module FTB = FStar.Tactics

// let fstar_env =
//   g:R.env { 
//     RT.lookup_fvar g RT.bool_fv == Some (RT.tm_type RT.u_zero) /\
//     RT.lookup_fvar g vprop_fv == Some (RT.tm_type (elab_universe (U_succ (U_succ U_zero)))) /\
//     (forall (u1 u2:R.universe). RT.lookup_fvar_uinst g bind_fv [u1; u2] == Some (bind_type u1 u2))
//     ///\ star etc
//   }

let tm_unit = tm_fvar (as_fv unit_lid)
let tm_bool = tm_fvar (as_fv bool_lid)
let tm_true = tm_constant R.C_True
let tm_false = tm_constant R.C_False

let tm_prop = Tm_FStar FStar.Reflection.Typing.tm_prop Range.range_0

let mk_erased (u:universe) (t:term) : term =
  let hd = tm_uinst (as_fv erased_lid) [u] in
  tm_pureapp hd None t

let mk_reveal (u:universe) (t:term) (e:term) : term =
  let hd = tm_uinst (as_fv reveal_lid) [u] in
  let hd = tm_pureapp hd (Some Implicit) t in
  tm_pureapp hd None e

let mk_hide (u:universe) (t:term) (e:term) : term =
  let hd = tm_uinst (as_fv hide_lid) [u] in
  let hd = tm_pureapp hd (Some Implicit) t in
  tm_pureapp hd None e

let mk_eq2 (u:universe)
           (t:term)
           (e0 e1:term) 
  : term
  = tm_pureapp
         (tm_pureapp (tm_pureapp (tm_uinst (as_fv R.eq2_qn) [u]) (Some Implicit) t)
                     None e0) None e1

let mk_eq2_prop (u:universe) (t:term) (e0 e1:term)
  : term
  = tm_pureapp
         (tm_pureapp (tm_pureapp (tm_uinst (as_fv (mk_steel_wrapper_lid "eq2_prop")) [u]) (Some Implicit) t)
                     None e0) None e1

let mk_vprop_eq (e0 e1:term) : term =
  mk_eq2 u2 Tm_VProp e0 e1

let mk_ref (t:term) : term = tm_pureapp (tm_fvar (as_fv ref_lid)) None t

let mk_pts_to (ty:term) (r:term) (v:term) : term =
  let t = tm_fvar (as_fv pts_to_lid) in
  let t = tm_pureapp t (Some Implicit) ty in
  let t = tm_pureapp t None r in
  let t = tm_pureapp t None (tm_fvar (as_fv full_perm_lid)) in
  tm_pureapp t None v

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
let env_bindings = list (var & binding)
let context = FStar.Sealed.Inhabited.sealed #(list string) []
noeq
type env = {
  f: RT.fstar_top_env;
  g: env_bindings;
  ctxt: context
}



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
let extend_env_l (f:R.env) (g:env_bindings) : R.env = 
  L.fold_right 
    (fun (x, b) g ->  
      let t = elab_binding b in
      RT.extend_env g x t)
     g
     f
let elab_env (e:env) : R.env = extend_env_l e.f e.g

let rec lookup_binding (e:list (var & 'a)) (x:var)
  : option 'a
  = match e with
    | [] -> None
    | (y, v) :: tl -> if x = y then Some v else lookup_binding tl x

let lookup (e:env) (x:var)
  : option binding
  = lookup_binding e.g x

let lookup_ty (e:env) (x:var)
  : option term
  = match lookup e x with
    | Some (Inl t) -> Some t
    | _ -> None

let extend (x:var) (b:binding) (e:env) : env =
  { e with g = (x, b) :: e.g }

let max (n1 n2:nat) = if n1 < n2 then n2 else n1

let rec fresh_wrt_bindings (e:list (var & 'a))
  : var
  = match e with
    | [] -> 0
    | (y, _) :: tl ->  max (fresh_wrt_bindings tl) y + 1
    | _ :: tl -> fresh_wrt_bindings tl

let rec fresh_not_mem (e:list (var & 'a)) (elt: (var & 'a))
  : Lemma (ensures L.memP elt e ==> fresh_wrt_bindings e > fst elt)
  = match e with
    | [] -> ()
    | hd :: tl -> fresh_not_mem tl elt
  
let rec lookup_mem (e:list (var & 'a)) (x:var)
  : Lemma
    (requires Some? (lookup_binding e x))
    (ensures exists elt. L.memP elt e /\ fst elt == x)
  = match e with
    | [] -> ()
    | hd :: tl -> 
      match lookup_binding tl x with
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
let fresh (e:env)
  : var
  = fresh_wrt_bindings e.g

let fresh_is_fresh (e:env)
  : Lemma (None? (lookup e (fresh e)))
          [SMTPat (lookup e (fresh e))]
  =  match lookup e (fresh e) with
     | None -> ()
     | Some _ ->
       lookup_mem e.g (fresh e);
       FStar.Classical.forall_intro (fresh_not_mem e.g)

[@@ erasable; no_auto_projectors]
noeq
type vprop_equiv : env -> term -> term -> Type =
  | VE_Refl:
     g:env ->
     t:term ->
     vprop_equiv g t t

  | VE_Sym:
     g:env ->
     t1:term -> 
     t2:term -> 
     vprop_equiv g t1 t2 ->
     vprop_equiv g t2 t1

  | VE_Trans:
     g:env ->
     t0:term ->
     t1:term ->
     t2:term ->
     vprop_equiv g t0 t1 ->
     vprop_equiv g t1 t2 ->
     vprop_equiv g t0 t2

  | VE_Ctxt:
     g:env ->
     t0:term -> 
     t1:term -> 
     t0':term -> 
     t1':term ->
     vprop_equiv g t0 t0' ->
     vprop_equiv g t1 t1' ->
     vprop_equiv g (Tm_Star t0 t1) (Tm_Star t0' t1')
     
  | VE_Unit: (*   *)
     g:env ->
     t:term ->
     vprop_equiv g (Tm_Star Tm_Emp t) t

  | VE_Comm:
     g:env ->
     t0:term ->
     t1:term ->
     vprop_equiv g (Tm_Star t0 t1) (Tm_Star t1 t0)
     
  | VE_Assoc:
     g:env ->
     t0:term ->
     t1:term ->
     t2:term ->
     vprop_equiv g (Tm_Star t0 (Tm_Star t1 t2)) (Tm_Star (Tm_Star t0 t1) t2)

  | VE_Ext:
     g:env ->
     t0:term ->
     t1:term ->
     FTB.equiv_token (elab_env g) (elab_term t0) (elab_term t1) ->
     vprop_equiv g t0 t1

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
  = let add_frame_s (s:st_comp) : st_comp =
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
  = let s : st_comp = {u=comp_u c2; res=comp_res c2; pre=comp_pre c1; post=comp_post c2} in
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
  = let s : st_comp = {u=comp_u c2; res=comp_res c2; pre=comp_pre c1; post=comp_post c2} in
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
  = let s : st_comp = {u=comp_u c2; res=comp_res c2; pre=comp_pre c1; post=comp_post c2} in
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
  = tm_pureapp (tm_uinst (as_fv non_informative_witness_lid) [u])
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
                pre=Tm_ExistsSL u (as_binder t) p;
                post=elim_exists_post u t p x
              }

let comp_intro_pure (p:term) =
  C_STGhost Tm_EmpInames 
            {
              u=u_zero;
              res=tm_unit;
              pre=Tm_Emp;
              post=Tm_Pure p
            }

let comp_intro_exists (u:universe) (t:term) (p:term) (e:term)
  : comp
  = C_STGhost Tm_EmpInames
              {
                u=u0;
                res=tm_unit;
                pre=open_term' p e 0;
                post=Tm_ExistsSL u (as_binder t) p
              }

let comp_intro_exists_erased (u:universe) (t:term) (p:term) (e:term)
  : comp
  = C_STGhost Tm_EmpInames
              {
                u=u0;
                res=tm_unit;
                pre=open_term' p (mk_reveal u t e) 0;
                post=Tm_ExistsSL u (as_binder t) p
              }

let comp_while_cond (inv:term)
  : comp
  = C_ST {
           u=u0;
           res=tm_bool;
           pre=Tm_ExistsSL u0 (as_binder tm_bool) inv;
           post=inv
         }

let comp_while_body (inv:term)
  : comp
  = C_ST {
           u=u0;
           res=tm_unit;
           pre=open_term' inv tm_true 0;
           post=Tm_ExistsSL u0 (as_binder tm_bool) inv
         }

let comp_while (inv:term)
  : comp
  = C_ST {
           u=u0;
           res=tm_unit;
           pre=Tm_ExistsSL u0 (as_binder tm_bool) inv;
           post=open_term' inv tm_false 0
         }

let mk_tuple2 (u1 u2:universe) (t1 t2:term) : term =
  tm_pureapp (tm_pureapp (tm_uinst (as_fv tuple2_lid) [u1; u2])
                         None
                         t1)
             None t2

let mk_fst (u1 u2:universe) (a1 a2 e:term) : term =
  tm_pureapp (tm_pureapp (tm_pureapp (tm_uinst (as_fv fst_lid) [u1; u2]) (Some Implicit) a1)
                         (Some Implicit) a2)
             None
             e

let mk_snd (u1 u2:universe) (a1 a2 e:term) : term =
  tm_pureapp (tm_pureapp (tm_pureapp (tm_uinst (as_fv snd_lid) [u1; u2]) (Some Implicit) a1)
                         (Some Implicit) a2)
             None
             e

let par_post (uL uR:universe) (aL aR postL postR:term) (x:var) : term =
  let x_tm = term_of_no_name_var x in
  
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

let comp_withlocal_body_pre (pre:vprop) (init_t:term) (r:term) (init:term) : vprop =
  Tm_Star pre (mk_pts_to init_t r init)

let comp_withlocal_body_post (post:term) (init_t:term) (r:term) : term =
  Tm_Star post (Tm_ExistsSL u0 (as_binder init_t) (mk_pts_to init_t r (null_bvar 0)))  

let comp_withlocal_body (r:var) (init_t:term) (init:term) (c:comp{C_ST? c}) : comp =
  let r = null_var r in
  C_ST {
    u = comp_u c;
    res = comp_res c;
    pre = comp_withlocal_body_pre (comp_pre c) init_t r init;
    post = comp_withlocal_body_post (comp_post c) init_t r
  }

let comp_rewrite (p q:vprop) : comp =
  C_STGhost Tm_EmpInames {
			u = u0;
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


let typing (g:env) (e:term) (t:term) =
    RT.tot_typing (elab_env g) (elab_term e) (elab_term t)

let tot_typing (g:env) (e:term) (t:term) =
    my_erased (typing g e t)

let universe_of (g:env) (t:term) (u:universe) =
    tot_typing g t (tm_type u)

let non_informative_t (g:env) (u:universe) (t:term) =
    w:term & tot_typing g w (non_informative_witness_t u t)

let non_informative_c (g:env) (c:comp_st) =
    non_informative_t g (comp_u c) (comp_res c)

let as_binder t = { binder_ty = t; binder_ppname = RT.pp_name_default }

[@@ no_auto_projectors]
noeq
type st_equiv : env -> comp -> comp -> Type =
  | ST_VPropEquiv :
      g:env ->
      c1:comp_st ->
      c2:comp_st { st_equiv_pre c1 c2 } -> 
      x:var { None? (lookup g x) /\
              ~(x `Set.mem` freevars (comp_post c1)) /\
              ~(x `Set.mem` freevars (comp_post c2)) } ->
      tot_typing g (comp_pre c1) Tm_VProp ->
      tot_typing g (comp_res c1) (tm_type (comp_u c1)) ->
      tot_typing (extend x (Inl (comp_res c1)) g) (open_term (comp_post c1) x) Tm_VProp ->
      vprop_equiv g (comp_pre c1) (comp_pre c2) ->
      vprop_equiv (extend x (Inl (comp_res c1)) g) 
                  (open_term (comp_post c1) x)
                  (open_term (comp_post c2) x) ->      
      st_equiv g c1 c2

[@@ no_auto_projectors]
noeq
type bind_comp  : env -> var -> comp -> comp -> comp -> Type =
  | Bind_comp :  // (C_ST and C_ST) or (C_STGhost and C_STGhost)
      g:env ->
      x:var { None? (lookup g x) } ->
      c1:comp_st ->
      c2:comp_st {bind_comp_pre x c1 c2} ->
      universe_of g (comp_res c2) (comp_u c2) ->
      //or in the result post; free var check isn't enough; we need typability
      y:var { None? (lookup g y) /\ ~(y `Set.mem` freevars (comp_post c2)) } ->      
      tot_typing (extend y (Inl (comp_res c2)) g) (open_term (comp_post c2) y) Tm_VProp ->
      bind_comp g x c1 c2 (bind_comp_out c1 c2)

  | Bind_comp_ghost_l :  // (C_STGhost and C_STAtomic)
      g:env ->
      x:var { None? (lookup g x) } ->
      c1:comp_st ->
      c2:comp_st {bind_comp_ghost_l_pre x c1 c2} ->
      non_informative_c1:non_informative_c g c1 ->
      universe_of g (comp_res c2) (comp_u c2) ->
      //or in the result post; free var check isn't enough; we need typability
      y:var { None? (lookup g y) /\ ~(y `Set.mem` freevars (comp_post c2)) } ->
      tot_typing (extend y (Inl (comp_res c2)) g) (open_term (comp_post c2) y) Tm_VProp ->
      bind_comp g x c1 c2 (bind_comp_ghost_l_out c1 c2)

  | Bind_comp_ghost_r :  // (C_STAtomic and C_STGhost)
      g:env ->
      x:var { None? (lookup g x) } ->
      c1:comp_st ->
      c2:comp_st {bind_comp_ghost_r_pre x c1 c2} ->
      non_informative_c2:non_informative_c g c2 ->
      universe_of g (comp_res c2) (comp_u c2) ->
      //or in the result post; free var check isn't enough; we need typability
      y:var { None? (lookup g y) /\ ~(y `Set.mem` freevars (comp_post c2)) } ->
      tot_typing (extend y (Inl (comp_res c2)) g) (open_term (comp_post c2) y) Tm_VProp ->
      bind_comp g x c1 c2 (bind_comp_ghost_r_out c1 c2)

[@@ no_auto_projectors]
noeq
type lift_comp : env -> comp -> comp -> Type =
  | Lift_STAtomic_ST :
      g:env ->
      c:comp_st{C_STAtomic? c /\ comp_inames c == Tm_EmpInames} ->
      lift_comp g c (C_ST (st_comp_of_comp c))

  | Lift_STGhost_STAtomic :
      g:env ->
      c:comp_st{C_STGhost? c} ->
      non_informative_c:non_informative_c g c ->
      lift_comp g c (C_STAtomic (comp_inames c) (st_comp_of_comp c))

let wr (t:st_term') : st_term = { term = t; range = FStar.Range.range_0 }

[@@ no_auto_projectors]
noeq
type st_comp_typing : env -> st_comp -> Type =
  | STC:
      g:env -> 
      st:st_comp ->
      x:var { None? (lookup g x) /\ ~(x `Set.mem` freevars st.post) } ->
      universe_of g st.res st.u ->
      tot_typing g st.pre Tm_VProp ->
      tot_typing (extend x (Inl st.res) g) (open_term st.post x) Tm_VProp ->
      st_comp_typing g st

[@@ no_auto_projectors]
noeq
type comp_typing : env -> comp -> universe -> Type =
  | CT_Tot :
      g:env ->
      t:term ->
      u:universe ->
      universe_of g t u ->
      comp_typing g (C_Tot t) u

  | CT_ST :
      g:env -> 
      st:st_comp -> 
      st_comp_typing g st ->
      comp_typing g (C_ST st) st.u

  | CT_STAtomic :
      g:env -> 
      inames:term ->
      st:st_comp -> 
      tot_typing g inames Tm_Inames ->
      st_comp_typing g st ->
      comp_typing g (C_STAtomic inames st) st.u

  | CT_STGhost :
      g:env -> 
      inames:term ->
      st:st_comp -> 
      tot_typing g inames Tm_Inames ->      
      st_comp_typing g st ->
      comp_typing g (C_STGhost inames st) st.u

let prop_validity (g:env) (t:term) =
  FTB.prop_validity_token (elab_env g) (elab_term t)

[@@ no_auto_projectors]
noeq
type st_typing : env -> st_term -> comp -> Type =
  | T_Abs: 
      g:env ->
      x:var { None? (lookup g x) } ->
      q:option qualifier ->
      b:binder ->
      u:universe ->
      body:st_term {~ (x `Set.mem` freevars_st body) } ->
      c:comp ->
      tot_typing g b.binder_ty (tm_type u) ->
      st_typing (extend x (Inl b.binder_ty) g) (open_st_term_nv body (b.binder_ppname, x)) c ->
      st_typing g (wr (Tm_Abs { b; q; pre=None; body; ret_ty=None; post=None }))
                  (C_Tot (tm_arrow b q (close_comp c x)))
  | T_STApp :
      g:env ->
      head:term ->
      ty:term ->
      q:option qualifier ->
      res:comp_st ->
      arg:term ->
      tot_typing g head (tm_arrow (as_binder ty) q res) ->
      tot_typing g arg ty ->
      st_typing g (wr (Tm_STApp {head; arg_qual=q; arg}))
                  (open_comp_with res arg)

  | T_Return:
      g:env ->
      c:ctag ->
      use_eq:bool ->
      u:universe ->
      t:term ->
      e:term ->
      post:term ->
      x:var { None? (lookup g x) /\ ~ (x `Set.mem` freevars post) } ->
      universe_of g t u ->
      tot_typing g e t ->
      tot_typing (extend x (Inl t) g) (open_term post x) Tm_VProp ->
      st_typing g (wr (Tm_Return { ctag=c; insert_eq=use_eq; term=e }))
                  (comp_return c use_eq u t e post x)

  | T_Lift:
      g:env ->
      e:st_term ->
      c1:comp_st ->
      c2:comp_st ->
      st_typing g e c1 ->
      lift_comp g c1 c2 ->
      st_typing g e c2

  | T_Bind:
      g:env ->
      e1:st_term ->
      e2:st_term ->
      c1:comp_st ->
      c2:comp_st ->
      b:binder { b.binder_ty == comp_res c1 }->
      x:var { None? (lookup g x)  /\ ~(x `Set.mem` freevars_st e2) } ->
      c:comp ->
      st_typing g e1 c1 ->
      tot_typing g (comp_res c1) (tm_type (comp_u c1)) -> //type-correctness; would be nice to derive it instead      
      st_typing (extend x (Inl (comp_res c1)) g) (open_st_term_nv e2 (b.binder_ppname, x)) c2 ->
      bind_comp g x c1 c2 c ->
      st_typing g (wr (Tm_Bind { binder=b; head=e1; body=e2 })) c

  | T_TotBind:
      g:env ->
      e1:term ->
      e2:st_term ->
      t1:term ->
      c2:comp_st ->
      x:var { None? (lookup g x) /\ ~ (x `Set.mem` freevars_st e2) } ->
      tot_typing g e1 t1 ->
      st_typing (extend x (Inl t1) g) (open_st_term_nv e2 (v_as_nv x)) c2 ->
      st_typing g (wr (Tm_TotBind { head = e1; body = e2 }))
                    (open_comp_with (close_comp c2 x) e1)

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
      tot_typing g b tm_bool ->
      st_typing (extend hyp (Inl (mk_eq2 u0 tm_bool b tm_true)) g) e1 c ->
      st_typing (extend hyp (Inl (mk_eq2 u0 tm_bool b tm_false)) g) e2 c ->
      my_erased (comp_typing g c uc) ->
      st_typing g (wr (Tm_If { b; then_=e1; else_=e2; post=None })) c

  | T_Frame:
      g:env ->
      e:st_term ->
      c:comp_st ->
      frame:term ->
      tot_typing g frame Tm_VProp ->
      st_typing g e c ->
      st_typing g e (add_frame c frame)

  | T_Equiv:
      g:env ->
      e:st_term ->
      c:comp ->
      c':comp ->      
      st_typing g e c ->
      st_equiv g c c' ->
      st_typing g e c'

  | T_IntroPure:
      g:env ->
      p:term ->
      tot_typing g p tm_prop ->
      prop_validity g p -> 
      st_typing g (wr (Tm_IntroPure { p; should_check=should_check_true }))
                  (comp_intro_pure p)

  | T_ElimExists:
      g:env ->
      u:universe ->
      t:term ->
      p:term ->
      x:var { None? (lookup g x) } ->
      tot_typing g t (tm_type u) ->
      tot_typing g (Tm_ExistsSL u (as_binder t) p) Tm_VProp ->
      st_typing g (wr (Tm_ElimExists { p = Tm_ExistsSL u (as_binder t) p }))
                    (comp_elim_exists u t p x)

  | T_IntroExists:
      g:env ->
      u:universe ->
      t:term ->
      p:term ->
      e:term ->
      tot_typing g t (tm_type u) ->
      tot_typing g (Tm_ExistsSL u (as_binder t) p) Tm_VProp ->
      tot_typing g e t ->
      st_typing g (wr (Tm_IntroExists { erased = false;
                                        p = Tm_ExistsSL u (as_binder t) p;
                                        witnesses= [e];
                                        should_check=should_check_true }))
                  (comp_intro_exists u t p e)
      
  | T_IntroExistsErased:
      g:env ->
      u:universe ->
      t:term ->
      p:term ->
      e:term ->
      tot_typing g t (tm_type u) ->
      tot_typing g (Tm_ExistsSL u (as_binder t) p) Tm_VProp ->
      tot_typing g e (mk_erased u t)  ->
      st_typing g (wr (Tm_IntroExists { erased = true;
                                        p = Tm_ExistsSL u (as_binder t) p;
                                        witnesses= [e];
                                        should_check=should_check_true }))
                  (comp_intro_exists_erased u t p e)

  | T_While:
      g:env ->
      inv:term ->
      cond:st_term ->
      body:st_term ->
      tot_typing g (Tm_ExistsSL u0 (as_binder tm_bool) inv) Tm_VProp ->
      st_typing g cond (comp_while_cond inv) ->
      st_typing g body (comp_while_body inv) ->
      st_typing g (wr (Tm_While { invariant = inv;
                                  condition = cond;
                                  body;
                                  condition_var = RT.pp_name_default } ))
                  (comp_while inv)

  | T_Par:
      g:env ->
      eL:st_term ->
      cL:comp { C_ST? cL } ->
      eR:st_term ->
      cR:comp { C_ST? cR /\ comp_u cL == comp_u cR } ->
      x:var { None? (lookup g x) } ->
      // TODO: can comp_typing come from inversion of eL : cL and eR : cR?
      comp_typing g cL (comp_u cL) ->
      comp_typing g cR (comp_u cR) ->
      st_typing g eL cL ->
      st_typing g eR cR ->
      st_typing g (wr (Tm_Par { pre1=Tm_Unknown; body1=eL; post1=Tm_Unknown;
                                pre2=Tm_Unknown; body2=eR; post2=Tm_Unknown }))
                  (comp_par cL cR x)

  | T_WithLocal:
      g:env ->
      init:term ->
      body:st_term ->
      init_t:term ->
      c:comp { C_ST? c } ->
      x:var { None? (lookup g x) /\ ~(x `Set.mem` freevars_st body) } ->
      tot_typing g init init_t ->
      universe_of g init_t u0 ->
      comp_typing g c (comp_u c) ->
      st_typing (extend x (Inl (mk_ref init_t)) g)
                (open_st_term_nv body (v_as_nv x))
                (comp_withlocal_body x init_t init c) ->
      st_typing g (wr (Tm_WithLocal { initializer=init; body } )) c

  | T_Rewrite:
      g:env ->
      p:vprop ->
      q:vprop ->
      tot_typing g p Tm_VProp ->
      vprop_equiv g p q ->
      st_typing g (wr (Tm_Rewrite { t1=p; t2=q } ))
                  (comp_rewrite p q)

  | T_Admit:
      g:env ->
      s:st_comp ->
      c:ctag ->
      st_comp_typing g s ->
      st_typing g (wr (Tm_Admit { ctag=c; u=s.u; typ=s.res; post=None }))
                  (comp_admit c s)


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
let star_typing_inversion_l (#g:_) (#t0 #t1:term) (d:tot_typing g (Tm_Star t0 t1) Tm_VProp)
  : tot_typing g t0 Tm_VProp
  = admit ()

let star_typing_inversion_r (#g:_) (#t0 #t1:term) (d:tot_typing g (Tm_Star t0 t1) Tm_VProp)
  : tot_typing g t1 Tm_VProp
  = admit ()

let star_typing_inversion (#g:_) (#t0 #t1:term) (d:tot_typing g (Tm_Star t0 t1) Tm_VProp)
  : GTot (tot_typing g t0 Tm_VProp & tot_typing g t1 Tm_VProp)
  = admit ()

let vprop_eq_typing_inversion g (t0 t1:term)
                              (token:FTB.equiv_token (elab_env g)
                                                     (elab_term t0)
                                                     (elab_term t1))
  : GTot (tot_typing g t0 Tm_VProp &
          tot_typing g t1 Tm_VProp)
  = admit ()

(* These I can easily prove *)
let star_typing (#g:_) (#t0 #t1:term)
                (d0:tot_typing g t0 Tm_VProp)
                (d1:tot_typing g t1 Tm_VProp)
  : tot_typing g (Tm_Star t0 t1) Tm_VProp
  = admit ()

let emp_typing (#g:_) 
  : tot_typing g Tm_Emp Tm_VProp
  = admit ()
