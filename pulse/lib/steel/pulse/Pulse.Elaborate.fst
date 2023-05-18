module Pulse.Elaborate
module RT = FStar.Reflection.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Elaborate.Core

#push-options "--fuel 10 --ifuel 10 --z3rlimit_factor 5 --query_stats --z3cliopt 'smt.qi.eager_threshold=100'"

let rec elab_open_commute' (e:term)
                           (v:term)
                           (n:index)
  : Lemma (ensures
              RT.open_or_close_term' (elab_term e) (RT.OpenWith (elab_term v)) n ==
              elab_term (open_term' e v n))
          (decreases e)
  = match e with
    | Tm_UVar _
    | Tm_Var _
    | Tm_FVar _
    | Tm_UInst _ _
    | Tm_Constant _
    | Tm_Emp 
    | Tm_Type _
    | Tm_Inames
    | Tm_EmpInames
    | Tm_VProp
    | Tm_BVar _
    | Tm_Unknown -> ()
    | Tm_Refine b phi ->
      elab_open_commute' b.binder_ty v n;
      elab_open_commute' phi v (n + 1)
    | Tm_PureApp e1 _ e2 ->
      elab_open_commute' e1 v n;
      elab_open_commute' e2 v n
    | Tm_Let t e1 e2 ->
      elab_open_commute' t v n;    
      elab_open_commute' e1 v n;
      elab_open_commute' e2 v (n + 1)
    | Tm_Pure p ->
      elab_open_commute' p v n
    | Tm_Star e1 e2 ->
      elab_open_commute' e1 v n;
      elab_open_commute' e2 v n
    | Tm_ExistsSL u t body _
    | Tm_ForallSL u t body ->
      elab_open_commute' t v n;
      elab_open_commute' body v (n + 1)
    | Tm_Arrow b _ body ->
      elab_open_commute' b.binder_ty v n;
      elab_comp_open_commute' body v (n + 1)

and elab_comp_open_commute' (c:comp) (v:term) (n:index)
  : Lemma (ensures
              RT.open_or_close_term' (elab_comp c) (RT.OpenWith (elab_term v)) n ==
              elab_comp (open_comp' c v n))
          (decreases c)
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
              RT.open_or_close_term' (elab_term e) (RT.CloseVar v) n ==
              elab_term (close_term' e v n)))
          (decreases e)
  = match e with
    | Tm_UVar _
    | Tm_Var _
    | Tm_BVar _
    | Tm_FVar _
    | Tm_UInst _ _
    | Tm_Constant _
    | Tm_Emp 
    | Tm_Type _
    | Tm_Inames
    | Tm_EmpInames
    | Tm_VProp
    | Tm_Unknown -> ()
    | Tm_Refine b phi ->
      elab_close_commute' b.binder_ty v n;
      elab_close_commute' phi v (n + 1)
    | Tm_PureApp e1 _ e2 ->
      elab_close_commute' e1 v n;
      elab_close_commute' e2 v n
    | Tm_Let t e1 e2 ->
      elab_close_commute' t v n;    
      elab_close_commute' e1 v n;
      elab_close_commute' e2 v (n + 1)
    | Tm_Pure p ->
      elab_close_commute' p v n
    | Tm_Star e1 e2 ->
      elab_close_commute' e1 v n;
      elab_close_commute' e2 v n
    | Tm_ExistsSL _ t body _
    | Tm_ForallSL _ t body ->
      elab_close_commute' t v n;
      elab_close_commute' body v (n + 1)    
    | Tm_Arrow b _ body ->
      elab_close_commute' b.binder_ty v n;
      elab_comp_close_commute' body v (n + 1)

and elab_comp_close_commute' (c:comp) (v:var) (n:index)
  : Lemma (ensures
              RT.open_or_close_term' (elab_comp c) (RT.CloseVar v) n ==
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
#pop-options

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
  | Tm_BVar _
  | Tm_Var _
  | Tm_FVar _
  | Tm_UInst _ _
  | Tm_Constant _ -> ()
  | Tm_Refine b t ->
    elab_ln b.binder_ty i;
    elab_ln t (i + 1)
  | Tm_PureApp head _ arg ->
    elab_ln head i;
    elab_ln arg i
  | Tm_Let t e1 e2 ->
    elab_ln t i;
    elab_ln e1 i;
    elab_ln e2 (i + 1)
  | Tm_Emp -> ()
  | Tm_Pure t -> elab_ln t i
  | Tm_Star l r ->
    elab_ln l i;
    elab_ln r i
  | Tm_ExistsSL _ t body _
  | Tm_ForallSL _ t body ->
    elab_ln t i;
    elab_ln body (i + 1)
  | Tm_Arrow b _ c ->
    elab_ln b.binder_ty i;
    elab_ln_comp c (i + 1)
  | Tm_Type _
  | Tm_VProp
  | Tm_Inames
  | Tm_EmpInames
  | Tm_UVar _
  | Tm_Unknown -> ()

and elab_ln_comp (c:comp) (i:int)
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

#push-options "--z3rlimit_factor 8"
let rec elab_freevars_eq (e:term)
  : Lemma (Set.equal (freevars e) (RT.freevars (elab_term e))) =
  match e with
  | Tm_BVar _
  | Tm_Var _
  | Tm_FVar _
  | Tm_UInst _ _
  | Tm_Constant _ -> ()
  | Tm_Refine b t ->
    elab_freevars_eq b.binder_ty;
    elab_freevars_eq t
  | Tm_PureApp head _ arg ->
    elab_freevars_eq head;
    elab_freevars_eq arg
  | Tm_Let t e1 e2 ->
    elab_freevars_eq t;
    elab_freevars_eq e1;
    elab_freevars_eq e2
  | Tm_Emp -> ()
  | Tm_Pure t -> elab_freevars_eq t
  | Tm_Star l r ->
    elab_freevars_eq l;
    elab_freevars_eq r
  | Tm_ExistsSL _ t body _
  | Tm_ForallSL _ t body ->
    elab_freevars_eq t;
    elab_freevars_eq body
  | Tm_Arrow b _ c ->
    elab_freevars_eq b.binder_ty;
    elab_freevars_comp_eq c
  | Tm_Type _
  | Tm_VProp
  | Tm_Inames
  | Tm_EmpInames
  | Tm_UVar _
  | Tm_Unknown -> ()

and elab_freevars_comp_eq (c:comp)
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
