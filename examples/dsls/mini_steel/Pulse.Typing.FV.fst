module Pulse.Typing.FV
module RT = Refl.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Typing
open Pulse.Elaborate.Pure
open Pulse.Soundness.Common

let vars_of_rt_env (g:R.env) = Set.intension (fun x -> Some? (RT.lookup_bvar g x))

#push-options "--query_stats --z3rlimit_factor 4"
let rec freevars_close_term' (e:term) (x:var) (i:index)
  : Lemma 
    (ensures freevars (close_term' e x i) `Set.equal`
             (freevars e `set_minus` x))
  = match e with
    | Tm_BVar _
    | Tm_Var _
    | Tm_FVar _
    | Tm_UInst _ _
    | Tm_Constant _  
    | Tm_Emp
    | Tm_Type _
    | Tm_VProp
    | Tm_Inames
    | Tm_EmpInames
    | Tm_UVar _ -> ()

    | Tm_Pure p ->
      freevars_close_term' p x i

    | Tm_Refine b t ->
      freevars_close_term' b.binder_ty x i;
      freevars_close_term' t x (i + 1)

    | Tm_Abs b _q pre body post ->
      freevars_close_term' b.binder_ty x i;
      freevars_close_term'_opt pre x (i + 1);
      freevars_close_term' body x (i + 1);
      freevars_close_term'_opt post x (i + 2)

    | Tm_PureApp l _ r
    | Tm_STApp l _ r
    | Tm_Star l r ->
      freevars_close_term' l x i;
      freevars_close_term' r x i

    | Tm_Bind e1 e2 ->
      freevars_close_term' e1 x i;
      freevars_close_term' e2 x (i + 1)

    | Tm_Let t e1 e2 ->
      freevars_close_term' t x i;    
      freevars_close_term' e1 x i;
      freevars_close_term' e2 x (i + 1)

    | Tm_ExistsSL _ t b
    | Tm_ForallSL _ t b ->
      freevars_close_term' t x i;    
      freevars_close_term' b x (i + 1)
      
    | Tm_If t0 t1 t2 post ->
      freevars_close_term' t0 x i;    
      freevars_close_term' t1 x i;    
      freevars_close_term' t2 x i;          
      freevars_close_term'_opt post x (i + 1)      

    | Tm_Arrow b _ body ->
      freevars_close_term' b.binder_ty x i;
      freevars_close_comp body x (i + 1)

    | Tm_ElimExists t -> freevars_close_term' t x i
    | Tm_IntroExists t e ->
      freevars_close_term' t x i;
      freevars_close_term' e x i

    | Tm_While inv cond body ->
      freevars_close_term' inv x (i + 1);
      freevars_close_term' cond x i;
      freevars_close_term' body x i

and freevars_close_comp (c:comp)
                        (x:var)
                        (i:index)
  : Lemma 
    (ensures freevars_comp (close_comp' c x i) `Set.equal`
             (freevars_comp c `set_minus` x))
    (decreases c)
    [SMTPat (freevars_comp (close_comp' c x i))]
  = match c with
    | C_Tot t ->
      freevars_close_term' t x i

    | C_ST s ->
      freevars_close_term' s.res x i;
      freevars_close_term' s.pre x i;      
      freevars_close_term' s.post x (i + 1)

    | C_STAtomic n s
    | C_STGhost n s ->    
      freevars_close_term' n x i;    
      freevars_close_term' s.res x i;
      freevars_close_term' s.pre x i;      
      freevars_close_term' s.post x (i + 1)

and freevars_close_term'_opt (t:option term) (x:var) (i:index)
  : Lemma
    (ensures (freevars_opt (close_term_opt' t x i) `Set.equal`
             (freevars_opt t `set_minus` x)))
    (decreases t)
  = match t with
    | None -> ()
    | Some t -> freevars_close_term' t x i

let freevars_close_term (e:term) (x:var) (i:index)
  : Lemma 
    (ensures freevars (close_term' e x i) `Set.equal`
             (freevars e `set_minus` x))
  = freevars_close_term' e x i

let contains_r (g:R.env) (x:var) = Some? (RT.lookup_bvar g x)
let vars_of_env_r (g:R.env) = Set.intension (contains_r g)

assume
val refl_typing_freevars (#g:R.env) (#e:R.term) (#t:R.term) 
                         (_:RT.typing g e t)
  : Lemma 
    (ensures RT.freevars e `Set.subset` (vars_of_env_r g) /\
             RT.freevars t `Set.subset` (vars_of_env_r g))

let freevars_open_term_inv (e:term) 
                           (x:var {~ (x `Set.mem` freevars e) })
  : Lemma 
    (ensures freevars e `Set.equal` (freevars (open_term e x) `set_minus` x))
    [SMTPat (freevars (open_term e x))]
  = close_open_inverse e x

assume
val freevars_open_term (e:term) (x:term) (i:index)
  : Lemma (freevars (open_term' e x i) `Set.subset` 
           (freevars e `Set.union` freevars x))
    [SMTPat (freevars (open_term' e x i))]

assume
val freevars_open_comp (c:comp) (x:term) (i:index)
  : Lemma 
    (ensures
      freevars_comp (open_comp' c x i) `Set.subset` 
      (freevars_comp c `Set.union` freevars x))
    [SMTPat (freevars_comp (open_comp' c x i))]
           
#push-options "--ifuel 10 --fuel 10 --z3rlimit_factor 10"

let bind_comp_freevars (#f:_) (#g:_) (#x:_) (#c1 #c2 #c:_)
                       (d:bind_comp f g x c1 c2 c)
                       (fv_lem: (#f:_ -> #g:_ -> #t:_ -> #c:_ -> d':src_typing f g t c { d' << d } -> Lemma (ensures (freevars t `Set.subset` vars_of_env g /\ freevars_comp c `Set.subset` vars_of_env g))))
  : Lemma 
    (requires freevars_comp c1 `Set.subset` vars_of_env g /\
              // freevars (comp_res c2) `Set.subset` vars_of_env g /\
              freevars_comp c2 `Set.subset` (Set.union (vars_of_env g) (Set.singleton x)))
    (ensures freevars_comp c `Set.subset` vars_of_env g)
  = match d with
    | Bind_comp _ _ _ _ (E dt) _ _ 
    | Bind_comp_ghost_l _ _ _ _ _ (E dt) _ _ 
    | Bind_comp_ghost_r _ _ _ _ _ (E dt) _ _  -> fv_lem dt

let rec vprop_equiv_freevars (#f:_) (#g:_) (#t0 #t1:_) (v:vprop_equiv f g t0 t1)
  : Lemma (ensures (freevars t0 `Set.subset` vars_of_env g) <==>
                   (freevars t1 `Set.subset` vars_of_env g))
          (decreases v)
  = match v with
    | VE_Refl _ _ -> ()
    | VE_Sym _ _ _ v' -> 
      vprop_equiv_freevars v'
    | VE_Trans g t0 t2 t1 v02 v21 ->
      vprop_equiv_freevars v02;
      vprop_equiv_freevars v21
    | VE_Ctxt g s0 s1 s0' s1' v0 v1 ->
      vprop_equiv_freevars v0;
      vprop_equiv_freevars v1
    | VE_Unit g t -> ()
    | VE_Comm g t0 t1 -> ()
    | VE_Assoc g t0 t1 t2 -> ()
    | VE_Ext g t0 t1 token ->
      let t : RT.typing (extend_env_l f g) token (elab_pure (mk_vprop_eq t0 t1)) = RT.T_Token _ _ _ () in
      refl_typing_freevars t;
      elab_freevars_inverse (mk_vprop_eq t0 t1)

#push-options "--fuel 2 --ifuel 2 --query_stats"
let st_equiv_freevars #f #g (#c1 #c2:_)
                      (d:st_equiv f g c1 c2)
  : Lemma
    (requires freevars_comp c1 `Set.subset` vars_of_env g)
    (ensures freevars_comp c2 `Set.subset` vars_of_env g)    
  = let ST_VPropEquiv _ _ _ x _ _ _ eq_pre eq_post = d in
    vprop_equiv_freevars eq_pre;
    vprop_equiv_freevars eq_post
#pop-options

let rec src_typing_freevars (#f:_) (#g:_) (#t:_) (#c:_)
                            (d:src_typing f g t c)
  : Lemma 
    (ensures freevars t `Set.subset` vars_of_env g /\
             freevars_comp c `Set.subset` vars_of_env g)
    (decreases d)
 = match d with
   | T_Tot _g e t dt ->
      elab_freevars_inverse e;
      elab_freevars_inverse t;      
      refl_typing_freevars dt;
      assert (vars_of_env_r (extend_env_l f g) `Set.equal` (vars_of_env g))
      
   | T_Abs _g _pp x _q ty _u body cres (E dt) db ->
      src_typing_freevars dt;
      src_typing_freevars db;
      freevars_close_comp cres x 0

   | T_STApp _ _ _ _ _ res arg st (E at) ->
     src_typing_freevars st;
     src_typing_freevars at

   | T_Return _ _ _ _ (E tt) _
   | T_ReturnNoEq _ _ _ _ tt _ ->
     src_typing_freevars tt

   | T_Lift _ _ _ _ d1 l ->
     src_typing_freevars d1

   | T_Bind _ _ e2 _ _ x _ d1 (E dc1) d2 bc ->
     src_typing_freevars d1;
     src_typing_freevars dc1;
     src_typing_freevars d2;
     bind_comp_freevars bc src_typing_freevars

   | T_If _ _b e1 e2 _c _u hyp (E tb) d1 d2 _ct ->
     admit();
     src_typing_freevars tb;
     src_typing_freevars d1;
     src_typing_freevars d2;
     assume (~(hyp `Set.mem` freevars e1));
     assume (~(hyp `Set.mem` freevars e2))
      
   | T_Frame _ _ _ _ (E df) dc ->
     src_typing_freevars df;
     src_typing_freevars dc

   | T_ElimExists _ _ _ _ (E dt) (E dv) ->
     src_typing_freevars dt;
     src_typing_freevars dv

   | T_IntroExists _ u tt p w (E dt) (E dv) (E dw) ->
     src_typing_freevars dt;
     src_typing_freevars dv;
     src_typing_freevars dw;
     assert (freevars t `Set.subset` vars_of_env g);
     calc (Set.subset) {
        freevars_comp c;
      (Set.equal) {}
        freevars_comp (comp_intro_exists u tt p w);
      (Set.equal) {}
        freevars Tm_EmpInames `Set.union`
        (freevars tm_unit `Set.union`
        (freevars (open_term' p w 0) `Set.union`
         freevars (Tm_ExistsSL u tt p)));
      (Set.equal) {} 
        (freevars (open_term' p w 0) `Set.union`
         freevars (Tm_ExistsSL u tt p));
      (Set.subset) { freevars_open_term p w 0 }
        (freevars p `Set.union` 
         freevars w `Set.union`
         freevars t `Set.union`
         freevars p);
     }

   | T_Equiv _ _ _ _ d2 deq ->
     src_typing_freevars d2;
     st_equiv_freevars deq

   | T_While _ inv _ _ (E inv_typing) cond_typing body_typing ->
     src_typing_freevars inv_typing;
     src_typing_freevars cond_typing;
     src_typing_freevars body_typing;
     assert (freevars tm_false `Set.equal` Set.empty);
     freevars_open_term inv tm_false 0;
     assert (freevars (open_term' inv tm_false 0) `Set.subset` freevars inv)
