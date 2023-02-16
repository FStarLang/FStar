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
  = admit()
  // = match e with
  //   | Tm_Var _
  //   | Tm_FVar _
  //   | Tm_UInst _ _
  //   | Tm_Constant _
  //   | Tm_Emp 
  //   | Tm_Type _
  //   | Tm_Inames
  //   | Tm_EmpInames
  //   | Tm_VProp
  //   | Tm_BVar _ -> ()
  //   | Tm_Refine b phi ->
  //     elab_open_commute' b.binder_ty v n;
  //     elab_open_commute' phi v (n + 1)
  //   | Tm_PureApp e1 _ e2 ->
  //     elab_open_commute' e1 v n;
  //     elab_open_commute' e2 v n
  //   | Tm_Let t e1 e2 ->
  //     elab_open_commute' t v n;    
  //     elab_open_commute' e1 v n;
  //     elab_open_commute' e2 v (n + 1)
  //   | Tm_Pure p ->
  //     elab_open_commute' p v n
  //   | Tm_Star e1 e2 ->
  //     elab_open_commute' e1 v n;
  //     elab_open_commute' e2 v n
  //   | Tm_ExistsSL u t body
  //   | Tm_ForallSL u t body ->
  //     elab_open_commute' t v n;
  //     elab_open_commute' body v (n + 1);
  //     admit()
  //   | Tm_Arrow b _ body ->
  //     elab_open_commute' b.binder_ty v n;
  //     elab_comp_open_commute' body v (n + 1)

and elab_comp_open_commute' (c:pure_comp) (v:pure_term) (n:index)
  : Lemma (ensures
              RT.open_or_close_term' (elab_pure_comp c) (RT.OpenWith (elab_pure v)) n ==
              elab_pure_comp (open_comp' c v n))
          (decreases c)
  = match c with
    | C_Tot t -> elab_open_commute' t v n
    | C_ST s -> 
      calc (==) {
      elab_pure_comp (open_comp' c v n);
      (==) {}
      mk_st s.u (elab_pure (open_term' s.res v n))
                (elab_pure (open_term' s.pre v n))
                (elab_pure (open_term' s.post v (n + 1)));
      (==) {       elab_open_commute' s.res v n;
                   elab_open_commute' s.pre v n;
                   elab_open_commute' s.post v (n + 1)
           }
      mk_st s.u (RT.open_or_close_term' (elab_pure s.res) (RT.OpenWith (elab_pure v)) n)
                (RT.open_or_close_term' (elab_pure s.pre) (RT.OpenWith (elab_pure v)) n)
                (RT.open_or_close_term' (elab_pure s.post) (RT.OpenWith (elab_pure v)) (n + 1));
      (==) { }
      (let u = elab_universe s.u in
       let head = R.pack_ln (R.Tv_UInst stt_fv [u]) in
       let res = RT.open_or_close_term' (elab_pure s.res) (RT.OpenWith (elab_pure v)) n in       
       pack_ln (Tv_App 
       
      mk_stt_app (elab_universe s.u)
                 [res;
                  (RT.open_or_close_term' (elab_pure s.pre) (RT.OpenWith (elab_pure v)) n);
                  mk_abs res R.Q_Explicit (RT.open_or_close_term' (elab_pure s.post) (RT.OpenWith (elab_pure v)) (n + 1))]);
                 
           
      };
      admit();
      elab_open_commute' s.res v n;
      elab_open_commute' s.pre v n;
      elab_open_commute' s.post v (n + 1)
    | _ -> admit()
    
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
    | Tm_ExistsSL _ t body
    | Tm_ForallSL _ t body ->
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
