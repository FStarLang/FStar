module Pulse.Elaborate
module RT = Refl.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Elaborate.Core

#push-options "--ifuel 2"
let elab_pure_equiv (#f:RT.fstar_top_env)
                    (#g:env)
                    (#t:term)
                    (#c:comp { C_Tot? c })
                    (d:st_typing f g (Tm_Return t) c)
  : Lemma (ensures elab_st_typing d == elab_term t)
  = ()
#pop-options

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
    | Tm_ExistsSL u t body
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
    | Tm_ExistsSL _ t body
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
