module Pulse.Elaborate
module RT = FStar.Reflection.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Typing
open Pulse.Elaborate.Core

// let rec elab_term_bv_sort (t:term)
//   : Lemma
//     (ensures 
//       (R.Tv_Var? (R.inspect_ln (elab_term t)) \/
//        R.Tv_BVar? (R.inspect_ln (elab_term t))) ==>
//       (match R.inspect_ln (elab_term t) with
//        | R.Tv_Var bv
//        | R.Tv_BVar bv ->
//          let vv = R.inspect_bv bv in
//          vv.bv_sort == RT.tun))
//   = admit()
      
              
#push-options "--fuel 10 --ifuel 10 --z3rlimit_factor 30 --query_stats --z3cliopt 'smt.qi.eager_threshold=100'"          
let rec elab_open_commute' (e:term)
                           (v:term)
                           (n:index)
  : Lemma (ensures
              RT.subst_term (elab_term e) [ RT.DT n (elab_term v) ] ==
              elab_term (open_term' e v n))
          (decreases e)
  = match e with
    | Tm_Emp 
    | Tm_Inames
    | Tm_EmpInames
    | Tm_VProp
    | Tm_Unknown -> ()
    // | Tm_PureApp e1 _ e2 ->
    //   elab_open_commute' e1 v n;
    //   elab_open_commute' e2 v n
    | Tm_Pure p ->
      elab_open_commute' p v n
    | Tm_Star e1 e2 ->
      elab_open_commute' e1 v n;
      elab_open_commute' e2 v n
    | Tm_ExistsSL u t body
    | Tm_ForallSL u t body ->
      elab_open_commute' t.binder_ty v n;
      elab_open_commute' body v (n + 1)
    | Tm_FStar t _ -> ()

let elab_comp_open_commute' (c:comp) (v:term) (n:index)
  : Lemma (ensures
              RT.subst_term (elab_comp c) [ RT.DT n (elab_term v) ] ==
              elab_comp (open_comp' c v n))
  = match c with
    | C_Tot t -> elab_open_commute' t v n
    | C_ST s -> 
      elab_open_commute' s.res v n;
      elab_open_commute' s.pre v n;
      elab_open_commute' s.post v (n + 1)
    | C_STAtomic inames s
    | C_STGhost inames s ->
      elab_open_commute' inames v n;
      elab_open_commute' s.res v n;
      elab_open_commute' s.pre v n;
      elab_open_commute' s.post v (n + 1)

let rec elab_close_commute' (e:term)
                            (v:var)
                            (n:index)
  : Lemma (ensures (
              RT.subst_term (elab_term e) [ RT.ND v n ] ==
              elab_term (close_term' e v n)))
          (decreases e)
  = match e with
    | Tm_Emp 
    | Tm_Inames
    | Tm_EmpInames
    | Tm_VProp
    | Tm_Unknown -> ()
    | Tm_Pure p ->
      elab_close_commute' p v n
    | Tm_Star e1 e2 ->
      elab_close_commute' e1 v n;
      elab_close_commute' e2 v n
    | Tm_ExistsSL _ t body
    | Tm_ForallSL _ t body ->
      elab_close_commute' t.binder_ty v n;
      elab_close_commute' body v (n + 1)    
    | Tm_FStar _ _ -> ()
    
let elab_comp_close_commute' (c:comp) (v:var) (n:index)
  : Lemma (ensures
              RT.subst_term (elab_comp c) [ RT.ND v n ] ==
              elab_comp (close_comp' c v n))
          (decreases c)
  = match c with
    | C_Tot t -> elab_close_commute' t v n
    | C_ST s -> 
      elab_close_commute' s.res v n;
      elab_close_commute' s.pre v n;
      elab_close_commute' s.post v (n + 1)
   | C_STAtomic inames s
   | C_STGhost inames s ->
      elab_close_commute' inames v n;
      elab_close_commute' s.res v n;
      elab_close_commute' s.pre v n;
      elab_close_commute' s.post v (n + 1)

let elab_open_commute (t:term) (x:var)
  : Lemma (elab_term (open_term t x) == RT.open_term (elab_term t) x)
  = RT.open_term_spec (elab_term t) x;
    elab_open_commute' t (null_var x) 0

let elab_comp_close_commute (c:comp) (x:var)
  : Lemma (elab_comp (close_comp c x) == RT.close_term (elab_comp c) x)
  = RT.close_term_spec (elab_comp c) x;
    elab_comp_close_commute' c x 0

let elab_comp_open_commute (c:comp) (x:term)
  : Lemma (elab_comp (open_comp_with c x) == RT.open_with (elab_comp c) (elab_term x))
  = RT.open_with_spec (elab_comp c) (elab_term x);
    elab_comp_open_commute' c x 0

let rec elab_ln t i =
  match t with
  | Tm_Emp -> ()
  | Tm_Pure t -> elab_ln t i
  | Tm_Star l r ->
    elab_ln l i;
    elab_ln r i
  | Tm_ExistsSL _ t body
  | Tm_ForallSL _ t body ->
    elab_ln t.binder_ty i;
    elab_ln body (i + 1)
  | Tm_VProp
  | Tm_Inames
  | Tm_EmpInames
  | Tm_Unknown
  | Tm_FStar _ _ -> ()

let elab_ln_comp (c:comp) (i:int)
  : Lemma (requires ln_c' c i)
          (ensures RT.ln' (elab_comp c) i) =

  match c with
  | C_Tot t -> elab_ln t i
  | C_ST st ->
    elab_ln st.res i;
    elab_ln st.pre i;
    elab_ln st.post (i + 1)
  | C_STAtomic inames st
  | C_STGhost inames st ->
    elab_ln inames i;
    elab_ln st.res i;
    elab_ln st.pre i;
    elab_ln st.post (i + 1)

let rec elab_freevars_eq (e:term)
  : Lemma (Set.equal (freevars e) (RT.freevars (elab_term e))) =
  match e with
  | Tm_Emp -> ()
  | Tm_Pure t -> elab_freevars_eq t
  | Tm_Star l r ->
    elab_freevars_eq l;
    elab_freevars_eq r
  | Tm_ExistsSL _ t body
  | Tm_ForallSL _ t body ->
    elab_freevars_eq t.binder_ty;
    elab_freevars_eq body
  | Tm_VProp
  | Tm_Inames
  | Tm_EmpInames
  | Tm_Unknown
  | Tm_FStar _ _ -> ()

let elab_freevars_comp_eq (c:comp)
  : Lemma (Set.equal (freevars_comp c) (RT.freevars (elab_comp c))) =

  match c with
  | C_Tot t -> elab_freevars_eq t
  | C_ST st ->
    elab_freevars_eq st.res;
    elab_freevars_eq st.pre;
    elab_freevars_eq st.post
  | C_STAtomic inames st
  | C_STGhost inames st ->
    elab_freevars_eq inames;
    elab_freevars_eq st.res;
    elab_freevars_eq st.pre;
    elab_freevars_eq st.post
#pop-options

let elab_freevars e = elab_freevars_eq e
