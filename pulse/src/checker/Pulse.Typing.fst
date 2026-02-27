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

module Pulse.Typing

module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
open Pulse.Reflection.Util
open FStar.List.Tot
open Pulse.Syntax

module L = FStar.List.Tot
module FTB = FStar.Tactics.V2
module S = Pulse.Syntax
module RU = Pulse.RuntimeUtils
module T= FStar.Tactics.V2

include Pulse.Typing.Env

let debug_log (level:string)  (g:env) (f: unit -> T.Tac string) : T.Tac unit =
  if RU.debug_at_level (fstar_env g) level
  then T.print (Printf.sprintf "Debug@%s:{ %s }\n" level (f ()))

let tm_unit = tm_fvar (as_fv unit_lid)
let unit_const = tm_constant R.C_Unit
let tm_bool = RT.bool_ty
let tm_int  = tm_fvar (as_fv int_lid)
let tm_nat  = tm_fvar (as_fv nat_lid)
let tm_szt  = szt_tm
let tm_true = tm_constant R.C_True
let tm_false = tm_constant R.C_False
let tm_l_false = tm_fvar (as_fv R.false_qn)
include Pulse.Reflection.Util { tm_is_unreachable }

let tm_prop = RU.set_range FStar.Reflection.Typing.tm_prop Range.range_0

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

let mk_sq_eq2 (u:universe)
              (t:term)
              (e0 e1:term) 
  : term
  = let eq = mk_eq2 u t e0 e1 in
    (tm_pureapp (tm_uinst (as_fv R.squash_qn) [u_zero]) None eq)

let mk_slprop_eq (e0 e1:term) : term =
  mk_eq2 u2 tm_slprop e0 e1

let rewrites_to_p_lid = Pulse.Reflection.Util.mk_pulse_lib_core_lid "rewrites_to_p"

let mk_sq_rewrites_to_p u t x y =
  let open R in
  let hd = pack_fv rewrites_to_p_lid in
  let hd = pack_ln (Tv_UInst hd [u]) in
  let args = [(t, Q_Implicit); (x, Q_Explicit); (y, Q_Explicit)] in
  mk_squash u_zero (R.mk_app hd args)


let mk_ref (t:term) : term = tm_pureapp (tm_uinst (as_fv ref_lid) [u0]) None t

let mk_pts_to (ty:term) (r:term) (v:term) : term =
  let t = tm_uinst (as_fv pts_to_lid) [u0] in
  let t = tm_pureapp t (Some Implicit) ty in
  let t = tm_pureapp t None r in
  let t = tm_pureapp t (Some Implicit) tm_full_perm in
  tm_pureapp t None v

let mk_pts_to_uninit (ty:term) (r:term) : term =
  let t = tm_uinst (as_fv pts_to_uninit_lid) [u0] in
  let t = tm_pureapp t (Some Implicit) ty in
  let t = tm_pureapp t None r in
  t

let comp_return (c:ctag) (use_eq:bool) (u:universe) (t:term) (e:term) (post:term) (x:var)
  : comp =

  let post_maybe_eq =
    if use_eq
    then let post = open_term' post (null_var x) 0 in
         let post = tm_star post (tm_pure (mk_eq2 u t (null_var x) e)) in
         close_term post x
    else post in

  match c with
  | STT ->
    C_ST { u; res = t; pre = open_term' post e 0; post = post_maybe_eq }
  | STT_Atomic ->
    C_STAtomic tm_emp_inames Neutral
      { u; res = t; pre = open_term' post e 0; post = post_maybe_eq }
  | STT_Ghost ->
    C_STGhost
      tm_emp_inames
      { u; res = t; pre = open_term' post e 0; post = post_maybe_eq }

let rec all_fresh (g:env) (xs:list var_binding) : Tot prop (decreases xs) =
  match xs with
  | [] -> True
  | x::xs -> freshv g x.x /\ all_fresh (push g (BindingVar x)) xs

let rec push_bindings (g:env) (bs:list var_binding {all_fresh g bs}) : Tot (g':env{env_extends g' g}) (decreases bs) =
  match bs with
  | [] -> g
  | x::bs -> push_bindings (push g (BindingVar x)) bs

let elab_push_binding (g:env) (x:var { ~ (Set.mem x (dom g)) }) (t:typ)
  : Lemma (elab_env (push_binding g x ppname_default t) ==
           RT.extend_env (elab_env g) x t) = ()

[@@ erasable; no_auto_projectors]
noeq
type slprop_equiv : env -> term -> term -> Type =
  | VE_Refl:
     g:env ->
     t:term ->
     slprop_equiv g t t

  | VE_Sym:
     g:env ->
     t1:term -> 
     t2:term -> 
     slprop_equiv g t1 t2 ->
     slprop_equiv g t2 t1

  | VE_Trans:
     g:env ->
     t0:term ->
     t1:term ->
     t2:term ->
     slprop_equiv g t0 t1 ->
     slprop_equiv g t1 t2 ->
     slprop_equiv g t0 t2

  | VE_Ctxt:
     g:env ->
     t0:term -> 
     t1:term -> 
     t0':term -> 
     t1':term ->
     slprop_equiv g t0 t0' ->
     slprop_equiv g t1 t1' ->
     slprop_equiv g (tm_star t0 t1) (tm_star t0' t1')
     
  | VE_Unit: (*   *)
     g:env ->
     t:term ->
     slprop_equiv g (tm_star tm_emp t) t

  | VE_Comm:
     g:env ->
     t0:term ->
     t1:term ->
     slprop_equiv g (tm_star t0 t1) (tm_star t1 t0)
     
  | VE_Assoc:
     g:env ->
     t0:term ->
     t1:term ->
     t2:term ->
     slprop_equiv g (tm_star t0 (tm_star t1 t2)) (tm_star (tm_star t0 t1) t2)

  | VE_Ext:
     g:env ->
     t0:term ->
     t1:term ->
     RT.equiv (elab_env g) t0 t1 ->
     slprop_equiv g t0 t1

  // | VE_Ex:
  //    g:env ->
  //    x:var { None? (lookup_ty g x) } ->
  //    ty:term ->
  //    t0:term ->
  //    t1:term ->
  //    slprop_equiv f ((x, Inl ty)::g) (open_term t0 x) (open_term t1 x) ->
  //    slprop_equiv f g (tm_exists_sl ty t0) (tm_exists_sl ty t1)

  | VE_Fa:
     g:env ->
     x:var { freshv g x } ->
     u:universe ->
     b:binder ->
     t0:term { ~(x `Set.mem` freevars t0 ) } ->
     t1:term { ~(x `Set.mem` freevars t1 ) } ->
     slprop_equiv (push_binding g x ppname_default b.binder_ty) (open_term t0 x) (open_term t1 x) ->
     slprop_equiv g (tm_forall_sl u b t0) (tm_forall_sl u b t1)


let add_frame (s:comp_st) (frame:term)
  : comp_st
  = let add_frame_s (s:st_comp) : st_comp =
        { s with pre = tm_star s.pre frame;
                 post = tm_star s.post frame }
    in
    match s with
    | C_ST s -> C_ST (add_frame_s s)
    | C_STAtomic inames obs s -> C_STAtomic inames obs (add_frame_s s)
    | C_STGhost inames s -> C_STGhost inames (add_frame_s s)

let add_frame_l (s:comp_st) (frame:term)
  : comp_st
  = let add_frame_s (s:st_comp) : st_comp =
        { s with pre = tm_star frame s.pre;
                 post = tm_star frame s.post }
    in
    match s with
    | C_ST s -> C_ST (add_frame_s s)
    | C_STAtomic inames obs s -> C_STAtomic inames obs (add_frame_s s)
    | C_STGhost inames s -> C_STGhost inames (add_frame_s s)

let add_frame_later_l (s:comp_st) (frame:term)
  : comp_st
  = add_frame_l s (tm_later frame)

let add_inv (s:comp_st) (v:slprop)
  : comp_st
  = add_frame s v

let at_most_one_observable o1 o2 =
  match o1, o2 with
  | Observable, Observable -> false
  | _ -> true

let join_obs (o1 o2:observability) : observability =
  if o1 = o2 then o1
  else Observable

let comp_with_inv (s:comp_st {C_STAtomic? s || C_STGhost? s}) (i p:term) =
  let add_inv inames = tm_add_inv inames i in
  let add_inv_st_comp (s:st_comp) =
    let frame = tm_inv i p in
    { s with pre = tm_star frame s.pre;
             post = tm_star frame s.post} in
  match s with
  | C_STAtomic inames obs s ->
    C_STAtomic (add_inv inames) obs (add_inv_st_comp s)
  | C_STGhost inames s ->
    C_STGhost (add_inv inames) (add_inv_st_comp s)

let bind_comp_compatible (c1 c2:comp_st)
  : prop
  = match c1, c2 with
    | C_ST _, C_ST _ -> True
    | C_STGhost inames1 _, C_STGhost inames2 _ -> inames1 == inames2
    | C_STAtomic inames1 obs1 _, C_STAtomic inames2 obs2 _ ->
      inames1 == inames2 /\ at_most_one_observable obs1 obs2
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
    | C_STAtomic inames obs1 _, C_STAtomic _ obs2 _ ->
      C_STAtomic inames (join_obs obs1 obs2) s
    | C_ST _, C_ST _ -> C_ST s

let st_equiv_pre (c1 c2:comp_st)
  : prop
  = comp_u c1 == comp_u c2 /\
    (match c1, c2 with
    | C_ST _, C_ST _ -> True
    | C_STAtomic inames1 obs1 _, C_STAtomic inames2 obs2 _ ->
      inames1 == inames2 /\ obs1 == obs2
    | C_STGhost inames1 _, C_STGhost inames2 _ -> inames1 == inames2
    | _, _ -> False)

let non_informative_class (u:universe) (t:term)
  : term
  = tm_pureapp (tm_uinst (as_fv non_informative_lid) [u])
               None
               t

let elim_exists_post (u:universe) (t:term) (p:term) (x:nvar)
  : term
  = let x_tm = term_of_nvar x in
    let p = open_term' p (mk_reveal u t x_tm) 0 in
    close_term p (snd x)

let comp_elim_exists (u:universe) (t:term) (p:term) (x:nvar)
  : comp
  = C_STGhost tm_emp_inames
      {
        u=u;
        res=mk_erased u t;
        pre=tm_exists_sl u (as_binder t) p;
        post=elim_exists_post u t p x
      }

let comp_intro_pure (p:term) =
  C_STGhost tm_emp_inames
    {
      u=u_zero;
      res=tm_unit;
      pre=tm_emp;
      post=tm_pure p
    }

let named_binder (x:ppname) (t:term) = mk_binder_ppname t x

let comp_intro_exists (u:universe) (b:binder) (p:term) (e:term)
  : comp
  = C_STGhost tm_emp_inames
      {
        u=u0;
        res=tm_unit;
        pre=open_term' p e 0;
        post=tm_exists_sl u b p
      }

let comp_intro_exists_erased (u:universe) (b:binder) (p:term) (e:term)
  : comp
  = C_STGhost tm_emp_inames
      {
        u=u0;
        res=tm_unit;
        pre=open_term' p (mk_reveal u b.binder_ty e) 0;
        post=tm_exists_sl u b p
      }


let comp_while_cond (x:ppname) (inv:term)
  : comp
  = C_ST {
           u=u0;
           res=tm_bool;
           pre=tm_exists_sl u0 (named_binder x tm_bool) inv;
           post=inv
         }

let comp_while_body (x:ppname) (inv:term)
  : comp
  = C_ST {
           u=u0;
           res=tm_unit;
           pre=open_term' inv tm_true 0;
           post=tm_exists_sl u0 (named_binder x tm_bool) inv
         }

let comp_while (x:ppname) (inv:term)
  : comp
  = C_ST {
           u=u0;
           res=tm_unit;
           pre=tm_exists_sl u0 (named_binder x tm_bool) inv;
           post=open_term' inv tm_false 0
         }

let comp_nuwhile_cond (inv:term) (post_cond:term)
  : comp
  = C_ST {
           u=u0;
           res=tm_bool;
           pre=inv;
           post=post_cond
         }

let mk_precedes u ty a b =
  R.mk_app (R.pack_ln <| R.Tv_UInst (R.pack_fv ["Prims"; "precedes"]) [u; u]) [
    ty, R.Q_Implicit;
    ty, R.Q_Implicit;
    a, R.Q_Explicit;
    b, R.Q_Explicit;
  ]

let comp_nuwhile_body u_meas ty_meas is_tot (dec_formula:term) x (inv:term) (post_cond:term)
  : comp
  = C_ST {
           u=u0;
           res=tm_unit;
           pre=open_term' post_cond tm_true 0;
           post=
            tm_exists_sl u_meas (as_binder ty_meas)
              (if is_tot then
                close_term inv (snd x) `tm_star` tm_pure dec_formula
              else
                close_term inv (snd x))
         }

let comp_nuwhile u_meas ty_meas (x:nvar) (inv:term) (post_cond:term)
  : comp
  = C_ST {
           u=u0;
           res=tm_unit;
           pre=tm_exists_sl u_meas (as_binder ty_meas) (close_term inv (snd x));
           post=tm_exists_sl u_meas (as_binder ty_meas) (close_term (open_term' post_cond tm_false 0) (snd x));
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

let mk_mktuple2 (u1 u2:universe) (a1 a2 v1 v2:term) : term =
  tm_pureapp (tm_pureapp (tm_pureapp (tm_pureapp (tm_uinst (as_fv mktuple2_lid) [u1; u2])
                                                  (Some Implicit) a1)
                                     (Some Implicit) a2)
                         None v1)
             None v2

let par_post (uL uR:universe) (aL aR postL postR:term) (x:var) : term =
  let x_tm = term_of_no_name_var x in
  
  let postL = open_term' postL (mk_fst uL uR aL aR x_tm) 0 in
  let postR = open_term' postR (mk_snd uL uR aL aR x_tm) 0 in
  let post = tm_star postL postR in
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
    pre = tm_star (comp_pre cL) (comp_pre cR);
    post
  }

let comp_withlocal_body_pre (pre:slprop) (init_t:term) (r:term) (init:option term) : slprop =
  tm_star pre (match init with | Some init -> mk_pts_to init_t r init | None -> mk_pts_to_uninit init_t r)

let withlocal_post (init_t: term) (r: term) : term =
  mk_pts_to_uninit init_t r

let comp_withlocal_body_post (post:term) (init_t:term) (r:term) : term =
  tm_star post (withlocal_post init_t r)

let comp_withlocal_body (r:var) (init_t:term) (init:option term) (c:comp{C_ST? c}) : comp =
  let r = null_var r in
  C_ST {
    u = comp_u c;
    res = comp_res c;
    pre = comp_withlocal_body_pre (comp_pre c) init_t r init;
    post = comp_withlocal_body_post (comp_post c) init_t r
  }

let mk_array (a:term) : term =
  tm_pureapp (tm_uinst (as_fv array_lid) [u0]) None a

let mk_array_length (a:term) (arr:term) : term =
  let t = tm_uinst (as_fv array_length_lid) [u0] in
  let t = tm_pureapp t (Some Implicit) a in
  tm_pureapp t None arr

let mk_array_pts_to (a:term) (arr:term) (v:term) : term =
  let t = tm_uinst (as_fv array_pts_to_lid) [u0] in
  let t = tm_pureapp t (Some Implicit) a in
  let t = tm_pureapp t None arr in
  let t = tm_pureapp t (Some Implicit) tm_full_perm in
  tm_pureapp t None v

let mk_array_pts_to_uninit (a:term) (arr:term) (len:term) : term =
  let t = tm_uinst (as_fv array_pts_to_uninit_lid) [u0] in
  let t = tm_pureapp t (Some Implicit) a in
  let t = tm_pureapp t None arr in
  tm_pureapp t None len

let mk_array_pts_to_uninit_post (a:term) (arr:term) : term =
  let t = tm_uinst (as_fv array_pts_to_uninit_post_lid) [u0] in
  let t = tm_pureapp t (Some Implicit) a in
  let t = tm_pureapp t None arr in
  t

// let mk_array_is_full (a:term) (arr:term) : term =
//   let t = tm_uinst (as_fv array_is_full_lid) [u0] in
//   let t = tm_pureapp t (Some Implicit) a in
//   tm_pureapp t None arr

let mk_seq_create (u:universe) (a:term) (len:term) (v:term) : term =
  let t = tm_uinst (as_fv seq_create_lid) [u] in
  let t = tm_pureapp t (Some Implicit) a in
  let t = tm_pureapp t None len in
  tm_pureapp t None v

let mk_szv (n:term) : term =
  let t = tm_fvar (as_fv szv_lid) in
  tm_pureapp t None n

let comp_withlocal_array_body_pre (pre:slprop) (a:term) (arr:term) (init:option term) (len:term) : slprop =
  let arr_pre =
    match init with
    | Some init -> mk_array_pts_to a arr (mk_seq_create u0 a (mk_szv len) init)
    | None -> mk_array_pts_to_uninit a arr (mk_szv len)
  in
  tm_star pre (tm_star arr_pre (tm_pure (mk_eq2 u0 tm_nat (mk_array_length a arr) (mk_szv len))))

let mk_seq (u:universe) (a:term) : term =
  let t = tm_uinst (as_fv seq_lid) [u] in
  tm_pureapp t None a

let withlocal_array_post (a:term) (arr:term) (init: option term) : term =
  match init with
  | Some _ -> tm_exists_sl u0 (as_binder (mk_seq u0 a)) (mk_array_pts_to a arr (null_bvar 0))
  | None -> mk_array_pts_to_uninit_post a arr

let comp_withlocal_array_body_post (post:term) (a:term) (arr:term) (init: option term) : term =
  tm_star post (withlocal_array_post a arr init)

let comp_withlocal_array_body (arr:var) (a:term) (init:option term) (len:term) (c:comp{C_ST? c}) : comp =
  let arr = null_var arr in
  C_ST {
    u = comp_u c;
    res = comp_res c;
    pre = comp_withlocal_array_body_pre (comp_pre c) a arr init len;
    post = comp_withlocal_array_body_post (comp_post c) a arr init;
  }

let comp_rewrite (p q:slprop) : comp =
  C_STGhost tm_emp_inames
    {
			u = u0;
			res = tm_unit;
			pre = p;
			post = q;
		}

[@@erasable]
noeq
type my_erased (a:Type) = | E of a

let typing (g:env) (e:term) (eff:T.tot_or_ghost) (t:term) =
  my_erased (RT.typing (elab_env g) e (eff, t))

let tot_typing (g:env) (e:term) (t:term) =
  typing g e T.E_Total t

let ghost_typing (g:env) (e:term) (t:typ) =
  typing g e T.E_Ghost t

let lift_typing_to_ghost_typing (#g:env) (#e:term) (#eff:T.tot_or_ghost) (#t:term)
  (d:typing g e eff t)
  : ghost_typing g e t =
  if eff = T.E_Ghost
  then d
  else let E d = d in
       E (RT.T_Sub _ _ _ _ d (RT.Relc_total_ghost _ _))

let universe_of (g:env) (t:term) (u:universe) =
  tot_typing g t (tm_type u)

let non_informative_t (g:env) (u:universe) (t:term) =
  w:term & tot_typing g w (non_informative_class u t)

let non_informative_c (g:env) (c:comp_st) =
  non_informative_t g (comp_u c) (comp_res c)

// TODO: move
let tm_join_inames (inames1 inames2 : term) : term =
  if eq_tm inames1 tm_emp_inames then inames2 else
  if eq_tm inames2 tm_emp_inames then inames1 else
  if eq_tm inames1 inames2 then inames1 else

  let join_lid = Pulse.Reflection.Util.mk_pulse_lib_core_lid "join_inames" in
  let join : R.term = R.pack_ln (R.Tv_FVar (R.pack_fv join_lid)) in
  wr (R.mk_e_app join [inames1; inames2])
     (T.range_of_term inames1)

let tm_inames_subset (inames1 inames2 : term) : term =
  let join_lid = Pulse.Reflection.Util.mk_pulse_lib_core_lid "inames_subset" in
  let join : R.term = R.pack_ln (R.Tv_FVar (R.pack_fv join_lid)) in
  wr (R.mk_e_app join [inames1; inames2])
     (T.range_of_term inames1)

let tm_inames_subset_typing (g:env) (inames1 inames2 : term) : tot_typing g (tm_inames_subset inames1 inames2) tm_prop =
  (* Need to add the typing hypothesis for `inames_subset` to
  the env and a precondition that the inames have type Pulse.Lib.Core.inames in g,
  which the caller should get from an inversion lemma *)
  RU.magic()

let prop_validity (g:env) (t:term) =
  FTB.prop_validity_token (elab_env g) t

[@@ erasable; no_auto_projectors]
noeq
type st_equiv : env -> comp -> comp -> Type =
  | ST_SLPropEquiv :
      g:env ->
      c1:comp_st ->
      c2:comp_st { st_equiv_pre c1 c2 } ->
      x:var { freshv g x /\
              ~(x `Set.mem` freevars (comp_post c1)) /\
              ~(x `Set.mem` freevars (comp_post c2)) } ->
      tot_typing g (comp_pre c1) tm_slprop ->
      tot_typing g (comp_res c1) (tm_type (comp_u c1)) ->
      tot_typing (push_binding g x ppname_default (comp_res c1)) (open_term (comp_post c1) x) tm_slprop ->
      RT.equiv (elab_env g) (comp_res c1) (comp_res c2) ->
      slprop_equiv g (comp_pre c1) (comp_pre c2) ->
      slprop_equiv (push_binding g x ppname_default (comp_res c1))
                  (open_term (comp_post c1) x)
                  (open_term (comp_post c2) x) ->      
      st_equiv g c1 c2
    
  | ST_TotEquiv :
      g:env -> 
      t1:term ->
      t2:term ->
      u:_ ->
      universe_of g t1 u ->
      Ghost.erased (RT.equiv (elab_env g) t1 t2) ->
      st_equiv g (C_Tot t1) (C_Tot t2)

let sub_observability (o1 o2:observability) = o1 = Neutral || o1 = o2 || o2 = Observable

[@@ erasable; no_auto_projectors]
noeq
type st_sub : env -> comp -> comp -> Type =
  | STS_Refl :
    g:env ->
    c:comp ->
    st_sub g c c

  | STS_Trans :
    g:env ->
    c1:comp ->
    c2:comp ->
    c3:comp ->
    st_sub g c1 c2 ->
    st_sub g c2 c3 ->
    st_sub g c1 c3

  | STS_GhostInvs :
    g:env ->
    stc:st_comp ->
    is1:term ->
    is2:term ->
    prop_validity g (tm_inames_subset is1 is2) ->
    st_sub g (C_STGhost is1 stc) (C_STGhost is2 stc)

  | STS_AtomicInvs :
    g:env ->
    stc:st_comp ->
    is1:term ->
    is2:term ->
    obs1:observability ->
    obs2:observability { sub_observability obs1 obs2 } ->
    prop_validity g (tm_inames_subset is1 is2) ->
    st_sub g (C_STAtomic is1 obs1 stc) (C_STAtomic is2 obs2 stc)

[@@ erasable; no_auto_projectors]
noeq
type lift_comp : env -> comp -> comp -> Type =
  | Lift_STAtomic_ST :
      g:env ->
      c:comp_st{C_STAtomic? c} -> // Note: we have to reflect a univerese bound here!
      lift_comp g c (C_ST (st_comp_of_comp c))

  | Lift_Observability:
      g:env ->
      c:comp_st{C_STAtomic? c } ->
      o2:observability { sub_observability (C_STAtomic?.obs c) o2 } ->
      lift_comp g
        (C_STAtomic (comp_inames c) (C_STAtomic?.obs c) (st_comp_of_comp c))
        (C_STAtomic (comp_inames c) o2 (st_comp_of_comp c))

  | Lift_Ghost_Neutral:
      g:env ->
      c:comp_st{C_STGhost? c} ->
      non_informative_c:non_informative_c g c ->
      lift_comp g c (C_STAtomic (comp_inames c) Neutral (st_comp_of_comp c))

  | Lift_Neutral_Ghost:
      g:env ->
      c:comp_st{C_STAtomic? c /\ C_STAtomic?.obs c == Neutral } ->
      lift_comp g c (C_STGhost (comp_inames c) (st_comp_of_comp c))

let wrst (ct:comp_st) (t:st_term') : st_term =
  { term = t;
    range = FStar.Range.range_0;
    effect_tag = as_effect_hint (ctag_of_comp_st ct);
    source = Sealed.seal false;
    seq_lhs = Sealed.seal false;
  }
let wtag (ct:option ctag)  (t:st_term') : st_term =
  { term = t;
    range = FStar.Range.range_0;
    effect_tag = FStar.Sealed.seal ct;
    source = Sealed.seal false;
    seq_lhs = Sealed.seal false;
  }

[@@ erasable; no_auto_projectors]
noeq
type st_comp_typing : env -> st_comp -> Type =
  | STC:
      g:env -> 
      st:st_comp ->
      x:var { freshv g x /\ ~(x `Set.mem` freevars st.post) } ->
      universe_of g st.res st.u ->
      tot_typing g st.pre tm_slprop ->
      tot_typing (push_binding g x ppname_default st.res) (open_term st.post x) tm_slprop ->
      st_comp_typing g st


[@@ erasable; no_auto_projectors]
noeq
type bind_comp  : env -> var -> comp -> comp -> comp -> Type =
  | Bind_comp :  // (C_ST and C_ST) or (C_STGhost and C_STGhost) or (C_STAtomic and C_STAtomic)
      g:env ->
      x:var { freshv g x } ->
      c1:comp_st ->
      c2:comp_st {bind_comp_pre x c1 c2} ->
      universe_of g (comp_res c2) (comp_u c2) ->
      //or in the result post; free var check isn't enough; we need typability
      y:var { freshv g y /\ ~(y `Set.mem` freevars (comp_post c2)) } ->      
      tot_typing (push_binding g y ppname_default (comp_res c2)) (open_term (comp_post c2) y) tm_slprop ->
      bind_comp g x c1 c2 (bind_comp_out c1 c2)

let tr_binding (vt : var & typ) : Tot R.binding =
  let v, t = vt in
  { 
    uniq = v;
    sort = t;
    ppname = ppname_default.name;
 }

let tr_bindings = L.map tr_binding

[@@ erasable; no_auto_projectors]
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
      comp_typing g (C_ST st) (universe_of_comp (C_ST st))

  | CT_STAtomic :
      g:env -> 
      inames:term ->
      obs:observability ->
      st:st_comp -> 
      tot_typing g inames tm_inames ->
      st_comp_typing g st ->
      comp_typing g (C_STAtomic inames obs st) (universe_of_comp (C_STAtomic inames obs st))

  | CT_STGhost :
      g:env ->
      inames:term ->
      st:st_comp ->
      tot_typing g inames tm_inames ->
      st_comp_typing g st ->
      comp_typing g (C_STGhost inames st) (universe_of_comp (C_STGhost inames st))

let comp_typing_u (e:env) (c:comp_st) = comp_typing e c (universe_of_comp c)

let subtyping_token g t1 t2 =
  T.subtyping_token (elab_env g) t1 t2

val readback_binding : R.binding -> var_binding
let readback_binding b = { n = { name = b.ppname; range = Range.range_0 }; x = b.uniq; ty = b.sort }

let non_informative (g:env) (c:comp) =
  my_erased (RT.non_informative (elab_env g) (elab_comp c))

let inv_disjointness (inames i:term) = 
  let g = Pulse.Reflection.Util.inv_disjointness_goal inames i in 
  S.wr g (RU.range_of_term i)

let eff_of_ctag = function
  | STT_Ghost -> T.E_Ghost
  | _ -> T.E_Total

let g_with_eq g hyp b (eq_v:term) =
  push_binding g hyp (mk_ppname_no_range "_if_hyp") (mk_sq_rewrites_to_p u0 tm_bool b eq_v)

let goto_comp_of_block_comp (c: comp_st) : comp_st =
  let {u;res;pre;post} = st_comp_of_comp c in
  with_st_comp c {
    u; res;
    pre = post;
    post = tm_is_unreachable;
  }

[@@ erasable; no_auto_projectors]
noeq
type st_typing : env -> st_term -> comp -> Type =
  | T_Abs: 
      g:env ->
      x:var { freshv g x } ->
      q:option qualifier ->
      b:binder ->
      u:universe ->
      body:st_term {~ (x `Set.mem` freevars_st body) } ->
      c:comp ->
      tot_typing g b.binder_ty (tm_type u) ->
      st_typing (push_binding (clear_goto g) x ppname_default b.binder_ty) (open_st_term_nv body (b.binder_ppname, x)) c ->
      st_typing g (wtag None (Tm_Abs { b; q; body; ascription=empty_ascription}))
                  (C_Tot (tm_arrow b q (close_comp c x)))
                
  | T_ST:
      g:env ->
      t:term ->
      c:comp_st ->
      tot_typing g t (elab_comp c) ->
      st_typing g (wrst c (Tm_ST { t; args=[] } )) c
 
  | T_STGhost:
      g:env ->
      t:term ->
      c:comp_st ->
      ghost_typing g t (elab_comp c) ->
      non_informative g c ->
      st_typing g (wrst c (Tm_ST { t; args=[] } )) c
 
  | T_Return:
      g:env ->
      c:ctag ->
      use_eq:bool ->
      u:universe ->
      t:term ->
      e:term ->
      post:term ->
      x:var { freshv g x /\ ~ (x `Set.mem` freevars post) } ->
      universe_of g t u ->
      typing g e (eff_of_ctag c) t ->
      tot_typing (push_binding g x ppname_default t) (open_term post x) tm_slprop ->
      st_typing g (wtag (Some c) (Tm_Return { expected_type=tm_unknown; insert_eq=use_eq; term=e }))
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
      x:var { freshv g x /\ ~(x `Set.mem` freevars_st e2) } ->
      c:comp ->
      st_typing g e1 c1 ->
      tot_typing g (comp_res c1) (tm_type (comp_u c1)) -> //type-correctness; would be nice to derive it instead      
      st_typing (push_binding g x ppname_default (comp_res c1)) (open_st_term_nv e2 (b.binder_ppname, x)) c2 ->
      bind_comp g x c1 c2 c ->
      st_typing g (wrst c (Tm_Bind { binder=b; head=e1; body=e2 })) c

  | T_BindFn:
      g:env ->
      e1:st_term ->
      e2:st_term ->
      c1:comp { C_Tot? c1 } ->
      c2:comp_st ->
      b:binder { b.binder_ty == comp_res c1 }->
      x:var { freshv g x /\ ~(x `Set.mem` freevars_st e2) } ->
      st_typing g e1 c1 ->
      u:Ghost.erased universe ->
      tot_typing g (comp_res c1) (tm_type u) -> //type-correctness; would be nice to derive it instead      
      st_typing (push_binding g x ppname_default (comp_res c1)) (open_st_term_nv e2 (b.binder_ppname, x)) c2 ->
      comp_typing_u g c2 ->
      st_typing g (wrst c2 (Tm_Bind { binder=b; head=e1; body=e2 })) c2

  | T_If:
      g:env ->
      b:term -> 
      e1:st_term ->
      e2:st_term ->
      c:comp_st ->
      (* This is a little weird, we introduce a name hyp in the environment, 
         but the branches are not allowed to use it (except perhaps in a silent way for proofs).
         Maybe more natural to have one free var in e1,e2 and to open it with hyp?
         But that's also a change to FStar.Reflection.Typing
       *)
      hyp:var { freshv g hyp /\
               ~(hyp `Set.mem` (freevars_st e1 `Set.union` freevars_st e2))
              } ->
      tot_typing g b tm_bool ->
      st_typing (g_with_eq g hyp b tm_true) e1 c ->
      st_typing (g_with_eq g hyp b tm_false) e2 c ->
      my_erased (comp_typing_u g c) ->
      st_typing g (wrst c (Tm_If { b; then_=e1; else_=e2; post=None })) c

  | T_Match :
      g:env ->
      sc_u:universe ->
      sc_ty:typ ->
      sc:term ->
      tot_typing g sc_ty (tm_type sc_u) ->
      tot_typing g sc sc_ty ->
      c:comp_st ->
      my_erased (comp_typing_u g c) ->
      brs:list branch ->
      brs_typing g sc_u sc_ty sc brs c ->
      pats_complete g sc sc_ty (L.map (fun b -> elab_pat b.pat) brs) ->
      st_typing g (wrst c (Tm_Match {sc; returns_=None; brs})) c

  | T_Frame:
      g:env ->
      e:st_term ->
      c:comp_st ->
      frame:term ->
      tot_typing g frame tm_slprop ->
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

  | T_Sub :
      g:env ->
      e:st_term ->
      c:comp ->
      c':comp ->
      st_typing g e c ->
      st_sub g c c' ->
      st_typing g e c'

  | T_IntroPure:
      g:env ->
      p:term ->
      tot_typing g p tm_prop ->
      prop_validity g p -> 
      st_typing g (wtag (Some STT_Ghost) (Tm_IntroPure { p }))
                  (comp_intro_pure p)

  | T_ElimExists:
      g:env ->
      u:universe ->
      t:term ->
      p:term ->
      x:var { freshv g x } ->
      tot_typing g t (tm_type u) ->
      tot_typing g (tm_exists_sl u (as_binder t) p) tm_slprop ->
      st_typing g (wtag (Some STT_Ghost) (Tm_ElimExists { p = tm_exists_sl u (as_binder t) p }))
                  (comp_elim_exists u t p (v_as_nv x))

  | T_IntroExists:
      g:env ->
      u:universe ->
      b:binder ->
      p:term ->
      e:term ->
      tot_typing g b.binder_ty (tm_type u) ->
      tot_typing g (tm_exists_sl u b p) tm_slprop ->
      ghost_typing g e b.binder_ty ->
      st_typing g (wtag (Some STT_Ghost) (Tm_IntroExists { p = tm_exists_sl u b p;
                                         witnesses= [e] }))
                  (comp_intro_exists u b p e)

  | T_While:
      g:env ->
      inv:term ->
      cond:st_term ->
      body:st_term ->
      tot_typing g (tm_exists_sl u0 (as_binder tm_bool) inv) tm_slprop ->
      st_typing g cond (comp_while_cond ppname_default inv) ->
      st_typing g body (comp_while_body ppname_default inv) ->
      st_typing g (wtag (Some STT) (Tm_While { invariant = inv;
                                              condition = cond;
                                              body;
                                              condition_var = ppname_default } ))
                  (comp_while ppname_default inv)

  | T_NuWhile:
      g:env ->
      inv:term ->
      post_cond:term ->
      cond:st_term ->
      body:st_term ->
      u_meas: universe -> ty_meas: term -> universe_of g ty_meas u_meas ->
      is_tot: bool ->
      dec_formula: term ->
      x:nvar { freshv g (snd x) /\ ~(snd x `Set.mem` freevars_st cond) /\ ~(snd x `Set.mem` freevars_st cond) } ->
      gx:env { gx == push_binding g (snd x) (fst x) ty_meas } ->
      tot_typing gx inv tm_slprop ->
      tot_typing gx (tm_exists_sl u0 (as_binder tm_bool) post_cond) tm_slprop ->
      st_typing gx cond (comp_nuwhile_cond inv post_cond) ->
      st_typing gx body (comp_nuwhile_body u_meas ty_meas is_tot dec_formula x inv post_cond) ->
      st_typing g (wtag (Some STT) (Tm_NuWhile { invariant = inv;
                                                loop_requires = tm_unknown;
                                                meas = [];
                                                condition = cond;
                                                body }))
                  (comp_nuwhile u_meas ty_meas x inv post_cond)

  | T_WithLocal:
      g:env ->
      binder_ppname:ppname ->
      init:term ->
      body:st_term ->
      init_t:term ->
      c:comp { C_ST? c } ->
      x:var { freshv g x /\ ~(x `Set.mem` freevars_st body) } ->
      tot_typing g init init_t ->
      universe_of g init_t u0 ->
      comp_typing_u g c ->
      st_typing (push_post (push_binding g x ppname_default (mk_ref init_t)) (withlocal_post init_t (null_var x)))
                (open_st_term_nv body (v_as_nv x))
                (comp_withlocal_body x init_t (Some init) c) ->
      st_typing g (wrst c (Tm_WithLocal { binder = mk_binder_ppname (mk_ref init_t) binder_ppname; initializer=Some init; body } )) c

  | T_WithLocalUninit:
      g:env ->
      binder_ppname:ppname ->
      body:st_term ->
      init_t:term ->
      c:comp { C_ST? c } ->
      x:var { freshv g x /\ ~(x `Set.mem` freevars_st body) } ->
      universe_of g init_t u0 ->
      comp_typing_u g c ->
      st_typing (push_post (push_binding g x ppname_default (mk_ref init_t)) (withlocal_post init_t (null_var x)))
                (open_st_term_nv body (v_as_nv x))
                (comp_withlocal_body x init_t None c) ->
      st_typing g (wrst c (Tm_WithLocal { binder = mk_binder_ppname (mk_ref init_t) binder_ppname; initializer=None; body } )) c

  | T_WithLocalArray:
      g:env ->
      binder_ppname:ppname ->
      initializer:term ->
      length:term ->
      body:st_term ->
      a:term ->
      c:comp { C_ST? c } ->
      x:var { freshv g x /\ ~(x `Set.mem` freevars_st body) } ->
      tot_typing g initializer a ->
      tot_typing g length tm_szt ->
      universe_of g a u0 ->
      comp_typing_u g c ->
      st_typing (push_post (push_binding g x ppname_default (mk_array a)) (withlocal_array_post a (null_var x) (Some initializer)))
                (open_st_term_nv body (v_as_nv x))
                (comp_withlocal_array_body x a (Some initializer) length c) ->
      st_typing g (wrst c (Tm_WithLocalArray { binder = mk_binder_ppname (mk_array a) binder_ppname; initializer = Some initializer; length; body } )) c

  | T_WithLocalArrayUninit:
      g:env ->
      binder_ppname:ppname ->
      length:term ->
      body:st_term ->
      a:term ->
      c:comp { C_ST? c } ->
      x:var { freshv g x /\ ~(x `Set.mem` freevars_st body) } ->
      tot_typing g length tm_szt ->
      universe_of g a u0 ->
      comp_typing_u g c ->
      st_typing (push_post (push_binding g x ppname_default (mk_array a)) (withlocal_array_post a (null_var x) None))
                (open_st_term_nv body (v_as_nv x))
                (comp_withlocal_array_body x a None length c) ->
      st_typing g (wrst c (Tm_WithLocalArray { binder = mk_binder_ppname (mk_array a) binder_ppname; initializer = None; length; body } )) c

  | T_Rewrite:
      g:env ->
      p:slprop ->
      q:slprop ->
      tot_typing g p tm_slprop ->
      slprop_equiv g p q ->
      (* Note: we always set the tactic to None. We already have a proof
      of slprop_equiv so we don't need the tactic, and we can just elaborate
      into a normal rewrite with the explicit proof that was constructed by the
      tactic during Pulse checking time.

      The alternative is taking an optional tactic + typing, which is quite annoying. *)
      st_typing g (wtag (Some STT_Ghost) (Tm_Rewrite { t1=p; t2=q; tac_opt=None; elaborated=true } ))
                  (comp_rewrite p q)

  | T_Admit:
      g:env ->
      c:comp_st ->
      comp_typing g c (universe_of_comp c) ->
      st_typing g (wtag (Some (ctag_of_comp_st c))
                        (Tm_Admit { ctag=ctag_of_comp_st c;
                                    u=comp_u c;
                                    typ=comp_res c;
                                    post=None }))
                  c

  | T_Unreachable:
      g:env ->
      c:comp_st { comp_pre c == tm_is_unreachable } ->
      comp_typing g c (universe_of_comp c) ->
      st_typing g (wtag (Some (ctag_of_comp_st c)) (Tm_Unreachable {c})) c

  | T_ForwardJumpLabel:
      g:env ->
      lbl:nvar { freshv g (snd lbl) } ->
      body:st_term ->
      c:comp_st ->
      st_typing (push_goto g (snd lbl) (fst lbl) (goto_comp_of_block_comp c)) (open_st_term' body (term_of_nvar lbl) 0) c ->
      st_typing g (wtag (Some (ctag_of_comp_st c)) (Tm_ForwardJumpLabel { lbl = fst lbl; body; post = c })) c

  | T_Goto:
      g:env ->
      lbl:nvar ->
      arg:term ->
      lbl_c:comp_st { lookup_goto g (snd lbl) == Some (fst lbl, lbl_c) } ->
      tot_typing g arg (comp_res lbl_c) ->
      u:universe -> res:typ -> universe_of g res u ->
      post:term -> post_x: var { freshv g post_x } -> tot_typing (push_binding_def g post_x res) (open_term post post_x) tm_slprop ->
      st_typing g (wtag (Some (ctag_of_comp_st lbl_c)) (Tm_Goto { lbl = term_of_nvar lbl; arg }))
        (with_st_comp lbl_c { u; res; pre = open_term' (comp_pre lbl_c) arg 0; post })

and pats_complete : env -> term -> typ -> list R.pattern -> Type0 =
  // just check the elaborated term with the core tc
  | PC_Elab :
    g:env ->
    sc:term ->
    sc_ty:typ ->
    pats:list R.pattern ->
    bnds:list (list R.binding) ->
    RT.match_is_complete (elab_env g) sc sc_ty pats bnds ->
    pats_complete g sc sc_ty pats

and brs_typing (g:env) (sc_u:universe) (sc_ty:typ) (sc:term) : list branch -> comp_st -> Type =
  | TBRS_0 :
      c:comp_st ->
      brs_typing g sc_u sc_ty sc [] c

  | TBRS_1 :
      c:comp_st ->
      pat:pattern ->
      e:st_term ->
      br_typing g sc_u sc_ty sc pat e c ->
      rest:list branch ->
      brs_typing g sc_u sc_ty sc rest c ->
      brs_typing g sc_u sc_ty sc ({pat;e;norw=Sealed.seal false}::rest) c

and br_typing : env -> universe -> typ -> term -> pattern -> st_term -> comp_st -> Type =
  | TBR :
      g:env ->
      sc_u : universe ->
      sc_ty : typ ->
      sc:term ->
      c:comp_st ->
      p:pattern ->
      e:st_term ->
      bs:(list R.binding){RT.bindings_ok_for_pat (fstar_env g) bs (elab_pat p)} ->
      _ : squash (all_fresh g (L.map readback_binding bs)) ->
      _ : squash (Some? (RT.elaborate_pat (elab_pat p) bs)) ->
      _ : squash (~(R.Tv_Unknown? (R.inspect_ln (fst (Some?.v (RT.elaborate_pat (elab_pat p) bs)))))) -> // should be provable from defn of elaborate_pat
      hyp:var {freshv (push_bindings g (L.map readback_binding bs)) hyp} ->
      st_typing (
         push_binding (push_bindings g (L.map readback_binding bs))
              hyp
              ({name=Sealed.seal "branch equality"; range=FStar.Range.range_0})
              (mk_sq_eq2 sc_u sc_ty sc (S.wr (fst (Some?.v (RT.elaborate_pat (elab_pat p) bs))) Range.range_0))
         ) e c ->
      br_typing g sc_u sc_ty sc p (close_st_term_n e (L.map (fun b -> (readback_binding b).x) bs)) c

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
let star_typing_inversion_l (#g:_) (#t0 #t1:term) (d:tot_typing g (tm_star t0 t1) tm_slprop)
  : tot_typing g t0 tm_slprop
  = admit ()

let star_typing_inversion_r (#g:_) (#t0 #t1:term) (d:tot_typing g (tm_star t0 t1) tm_slprop)
  : tot_typing g t1 tm_slprop
  = admit ()

let star_typing_inversion (#g:_) (#t0 #t1:term) (d:tot_typing g (tm_star t0 t1) tm_slprop)
  : GTot (tot_typing g t0 tm_slprop & tot_typing g t1 tm_slprop)
  = admit ()

let slprop_eq_typing_inversion g (t0 t1:term)
                              (token:RT.equiv (elab_env g)
                                                     t0
                                                     t1)
  : GTot (tot_typing g t0 tm_slprop &
          tot_typing g t1 tm_slprop)
  = admit ()

(* These I can easily prove *)
let star_typing (#g:_) (#t0 #t1:term)
                (d0:tot_typing g t0 tm_slprop)
                (d1:tot_typing g t1 tm_slprop)
  : tot_typing g (tm_star t0 t1) tm_slprop
  = admit ()

let emp_typing (#g:_) 
  : tot_typing g tm_emp tm_slprop
  = admit ()

let fresh_wrt (x:var) (g:env) (vars:_) = 
  freshv g x /\  ~(x `Set.mem` vars)


let effect_annot_typing (g:env) (e:effect_annot) =
  match e with
  | EffectAnnotGhost { opens }
  | EffectAnnotAtomic { opens }
  | EffectAnnotAtomicOrGhost { opens } ->
    tot_typing g opens tm_inames
  | _ -> unit

noeq
type post_hint_t = {
  g:env;
  effect_annot:effect_annot;
  effect_annot_typing:effect_annot_typing g effect_annot;
  ret_ty:term;
  u:universe;
  ty_typing:universe_of g ret_ty u;
  post:term;
  x:(x:FStar.Ghost.erased var { fresh_wrt x g (freevars post) });
  post_typing_src:tot_typing (push_binding g x ppname_default ret_ty) (open_term post x) tm_slprop;
  post_typing:
    FStar.Ghost.erased (RT.tot_typing (elab_env g)
                                      (RT.(mk_abs ret_ty T.Q_Explicit post))
                                      (RT.mk_arrow ret_ty T.Q_Explicit tm_slprop))
}

let post_hint_for_env_p (g:env) (p:post_hint_t) = g `env_extends` p.g

let post_hint_for_env_extends (g:env) (p:post_hint_t) (b:binding { dom g `Set.disjoint` binding_dom b })
  : Lemma
    (requires post_hint_for_env_p g p)
    (ensures post_hint_for_env_p (push g b) p)
    [SMTPat (post_hint_for_env_p (push g b) p)]
  = env_extends_push g b

let post_hint_for_env (g:env) = p:post_hint_t { post_hint_for_env_p g p }
noeq
type post_hint_opt_t =
| PostHint : v:post_hint_t -> post_hint_opt_t
| TypeHint of typ
| NoHint

let post_hint_opt (g:env) = p:post_hint_opt_t { PostHint? p ==> post_hint_for_env_p g (PostHint?.v p) }

noeq
type post_hint_typing_t (g:env) (p:post_hint_t) (x:var { ~ (Set.mem x (dom g)) }) = {
  effect_annot_typing:effect_annot_typing g p.effect_annot;
  ty_typing:universe_of g p.ret_ty p.u;
  post_typing:tot_typing (push_binding g x ppname_default p.ret_ty) (open_term p.post x) tm_slprop
}

irreducible
let post_hint_typing (g:env)
                     (p:post_hint_for_env g)
                     (x:var { fresh_wrt x g (freevars p.post) })
  : post_hint_typing_t g p x
  = let effect_annot_typing : effect_annot_typing g p.effect_annot = 
      match p.effect_annot with
      | EffectAnnotAtomic { opens }
      | EffectAnnotGhost { opens }
      | EffectAnnotAtomicOrGhost { opens } ->
        let opens_typing : tot_typing g opens tm_inames = RU.magic () in //weakening
        opens_typing
      | _ -> ()
    in
  {
    effect_annot_typing;
    ty_typing = RU.magic (); //weakening
    post_typing = RU.magic ();
  }


let effect_annot_matches (c:comp_st) (effect_annot:effect_annot) : prop =
  match c, effect_annot with
  | C_ST _, EffectAnnotSTT -> True
  | C_STGhost inames' _, EffectAnnotGhost { opens }
  | C_STAtomic inames' _ _, EffectAnnotAtomic { opens } ->
    inames' == opens
  | _, EffectAnnotAtomicOrGhost { opens } ->
    (C_STAtomic? c \/ C_STGhost? c)  /\ (comp_inames c == opens)
  | _ -> False

let comp_post_matches_hint (c:comp_st) (post_hint:post_hint_opt_t) =
  match post_hint with
  | PostHint post_hint ->
    comp_res c == post_hint.ret_ty /\
    comp_u c == post_hint.u /\
    comp_post c == post_hint.post /\
    effect_annot_matches c post_hint.effect_annot
  | _ -> True