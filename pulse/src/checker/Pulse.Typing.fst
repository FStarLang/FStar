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
let slprop_equiv (g:env) (t1:term) (t2:term) = unit


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

let comp_while_cond (inv:term) (post_cond:term)
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

let comp_while_body u_meas ty_meas is_tot x (inv:term) (post_cond:term)
  : comp
  = C_ST {
           u=u0;
           res=tm_unit;
           pre=open_term' post_cond tm_true 0;
           post=
            tm_exists_sl u_meas (as_binder ty_meas)
              (if is_tot then
                // TODO: this pretty prints like horse manure
                close_term inv (snd x) `tm_star` tm_pure (mk_precedes u_meas ty_meas (tm_bvar {bv_index=0;bv_ppname=fst x}) (term_of_nvar x))
              else
                close_term inv (snd x))
         }

let comp_while u_meas ty_meas (x:nvar) (inv:term) (post_cond:term)
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

let typing (g:env) (e:term) (eff:T.tot_or_ghost) (t:term) = unit

let tot_typing (g:env) (e:term) (t:term) = unit

let ghost_typing (g:env) (e:term) (t:typ) = unit

let lift_typing_to_ghost_typing (#g:env) (#e:term) (#eff:T.tot_or_ghost) (#t:term)
  (d:typing g e eff t)
  : ghost_typing g e t = ()

let universe_of (g:env) (t:term) (u:universe) = unit

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
let st_equiv (g:env) (c1:comp) (c2:comp) = unit

let sub_observability (o1 o2:observability) = o1 = Neutral || o1 = o2 || o2 = Observable

let st_sub (g:env) (c1:comp) (c2:comp) = unit

let lift_comp (g:env) (c1:comp) (c2:comp) = unit

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

let st_comp_typing (g:env) (st:st_comp) = unit


let bind_comp (g:env) (x:var) (c1:comp) (c2:comp) (c:comp) = unit

let tr_binding (vt : var & typ) : Tot R.binding =
  let v, t = vt in
  { 
    uniq = v;
    sort = t;
    ppname = ppname_default.name;
 }

let tr_bindings = L.map tr_binding

let comp_typing (g:env) (c:comp) (u:universe) = unit

let comp_typing_u (e:env) (c:comp_st) = comp_typing e c (universe_of_comp c)

let subtyping_token g t1 t2 =
  T.subtyping_token (elab_env g) t1 t2

val readback_binding : R.binding -> var_binding
let readback_binding b = { n = { name = b.ppname; range = Range.range_0 }; x = b.uniq; ty = b.sort }

let non_informative (g:env) (c:comp) = unit

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
let st_typing (g:env) (t:st_term) (c:comp) = unit

let pats_complete (g:env) (sc:term) (sc_ty:typ) (pats:list R.pattern) = unit

let brs_typing (g:env) (sc_u:universe) (sc_ty:typ) (sc:term) (brs:list branch) (c:comp_st) = unit

let br_typing (g:env) (sc_u:universe) (sc_ty:typ) (sc:term) (p:pattern) (e:st_term) (c:comp_st) = unit

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
  = ()

let star_typing_inversion_r (#g:_) (#t0 #t1:term) (d:tot_typing g (tm_star t0 t1) tm_slprop)
  : tot_typing g t1 tm_slprop
  = ()

let star_typing_inversion (#g:_) (#t0 #t1:term) (d:tot_typing g (tm_star t0 t1) tm_slprop)
  : GTot (tot_typing g t0 tm_slprop & tot_typing g t1 tm_slprop)
  = ((), ())

let slprop_eq_typing_inversion g (t0 t1:term)
                              (token:RT.equiv (elab_env g)
                                                     t0
                                                     t1)
  : GTot (tot_typing g t0 tm_slprop &
          tot_typing g t1 tm_slprop)
  = ((), ())

let star_typing (#g:_) (#t0 #t1:term)
                (d0:tot_typing g t0 tm_slprop)
                (d1:tot_typing g t1 tm_slprop)
  : tot_typing g (tm_star t0 t1) tm_slprop
  = ()

let emp_typing (#g:_) 
  : tot_typing g tm_emp tm_slprop
  = ()

let fresh_wrt (x:var) (g:env) (vars:_) = 
  freshv g x /\  ~(x `Set.mem` vars)


let effect_annot_typing (g:env) (e:effect_annot) = unit

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
  = {
    effect_annot_typing = ();
    ty_typing = ();
    post_typing = ();
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