module Pulse.Elaborate.Lemmas
module RT = Refl.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Elaborate
#push-options "--ifuel 2"
let elab_pure_equiv (#f:RT.fstar_top_env)
                    (#g:env)
                    (#t:pure_term)
                    (#c:pure_comp { C_Tot? c })
                    (d:src_typing f g t c)
  : Lemma (ensures elab_src_typing d == elab_pure t)
  = ()
#pop-options

#push-options "--fuel 10 --ifuel 6 --z3rlimit_factor 25 --query_stats --z3cliopt 'smt.qi.eager_threshold=100'"
let rec elab_open_commute' (e:pure_term)
                           (v:pure_term)
                           (n:index)
  : Lemma (ensures
              RT.open_or_close_term' (elab_pure e) (RT.OpenWith (elab_pure v)) n ==
              elab_pure (open_term' e v n))
          (decreases e)
  = match e with
    | Tm_Var _
    | Tm_FVar _
    | Tm_UInst _ _
    | Tm_Constant _
    | Tm_Emp 
    | Tm_Type _
    | Tm_Inames
    | Tm_EmpInames
    | Tm_VProp -> ()
    | Tm_BVar bv ->
      let rbv = R.pack_bv (RT.make_bv_with_name bv.bv_ppname bv.bv_index tun) in
      let re = R.pack_ln (R.Tv_BVar rbv) in
      assert (elab_pure e == re);
      if n <> bv.bv_index then ()
      else (
        assume (~(Tm_Var? v)); //the Var case is messy because of pp_name; this should go away with hiding names in meta
        ()
      )
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
    | Tm_ExistsSL t body
    | Tm_ForallSL t body ->
      elab_open_commute' t v n;
      elab_open_commute' body v (n + 1)    
    | Tm_Arrow b _ body ->
      elab_open_commute' b.binder_ty v n;
      elab_comp_open_commute' body v (n + 1)

and elab_comp_open_commute' (c:pure_comp) (v:pure_term) (n:index)
  : Lemma (ensures
              RT.open_or_close_term' (elab_pure_comp c) (RT.OpenWith (elab_pure v)) n ==
              elab_pure_comp (open_comp' c v n))
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

let rec elab_close_commute' (e:pure_term)
                            (v:var)
                            (n:index)
  : Lemma (ensures (
              closing_pure_term e v n;
              RT.open_or_close_term' (elab_pure e) (RT.CloseVar v) n ==
              elab_pure (close_term' e v n)))
          (decreases e)
  = closing_pure_term e v n;
    match e with
    | Tm_Var _
    | Tm_BVar _
    | Tm_FVar _
    | Tm_UInst _ _
    | Tm_Constant _
    | Tm_Emp 
    | Tm_Type _
    | Tm_Inames
    | Tm_EmpInames
    | Tm_VProp -> ()
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
    | Tm_ExistsSL t body
    | Tm_ForallSL t body ->
      elab_close_commute' t v n;
      elab_close_commute' body v (n + 1)    
    | Tm_Arrow b _ body ->
      elab_close_commute' b.binder_ty v n;
      elab_comp_close_commute' body v (n + 1)

and elab_comp_close_commute' (c:pure_comp) (v:var) (n:index)
  : Lemma (ensures
              RT.open_or_close_term' (elab_pure_comp c) (RT.CloseVar v) n ==
              elab_pure_comp (close_comp' c v n))
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

let elab_open_commute (t:pure_term) (x:var)
  : Lemma (elab_pure (open_term t x) == RT.open_term (elab_pure t) x)
  = RT.open_term_spec (elab_pure t) x;
    elab_open_commute' t (null_var x) 0

let elab_comp_close_commute (c:pure_comp) (x:var)
  : Lemma (elab_pure_comp (close_pure_comp c x) == RT.close_term (elab_pure_comp c) x)
  = RT.close_term_spec (elab_pure_comp c) x;
    elab_comp_close_commute' c x 0

let elab_comp_open_commute (c:pure_comp) (x:pure_term)
  : Lemma (elab_pure_comp (open_comp_with c x) == RT.open_with (elab_pure_comp c) (elab_pure x))
  = RT.open_with_spec (elab_pure_comp c) (elab_pure x);
    elab_comp_open_commute' c x 0
