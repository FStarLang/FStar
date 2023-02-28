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

#push-options "--query_stats --z3rlimit_factor 2"
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
    | Tm_UVar _
    | Tm_Unknown -> ()

    | Tm_Pure p ->
      freevars_close_term' p x i

    | Tm_Refine b t ->
      freevars_close_term' b.binder_ty x i;
      freevars_close_term' t x (i + 1)

    | Tm_PureApp l _ r
    | Tm_Star l r ->
      freevars_close_term' l x i;
      freevars_close_term' r x i

    | Tm_Let t e1 e2 ->
      freevars_close_term' t x i;    
      freevars_close_term' e1 x i;
      freevars_close_term' e2 x (i + 1)

    | Tm_ExistsSL _ t b _
    | Tm_ForallSL _ t b ->
      freevars_close_term' t x i;    
      freevars_close_term' b x (i + 1)

    | Tm_Arrow b _ body ->
      freevars_close_term' b.binder_ty x i;
      freevars_close_comp body x (i + 1)

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

let freevars_close_term_opt' (t:option term) (x:var) (i:index)
  : Lemma
    (ensures (freevars_opt (close_term_opt' t x i) `Set.equal`
             (freevars_opt t `set_minus` x)))
    (decreases t)
  = match t with
    | None -> ()
    | Some t -> freevars_close_term' t x i

let rec freevars_close_st_term' (t:st_term) (x:var) (i:index)
  : Lemma
    (ensures (freevars_st (close_st_term' t x i) `Set.equal`
             (freevars_st t `set_minus` x)))
    (decreases t)
  = match t with
    | Tm_Return _ _ t ->
      freevars_close_term' t x i

    | Tm_STApp l _ r ->
      freevars_close_term' l x i;
      freevars_close_term' r x i
    
    | Tm_Abs b _q pre body post ->
      freevars_close_term' b.binder_ty x i;
      freevars_close_term_opt' pre x (i + 1);
      freevars_close_st_term' body x (i + 1);
      freevars_close_term_opt' post x (i + 2)

    | Tm_Bind e1 e2 ->
      freevars_close_st_term' e1 x i;
      freevars_close_st_term' e2 x (i + 1)
      
    | Tm_If t0 t1 t2 post ->
      freevars_close_term' t0 x i;    
      freevars_close_st_term' t1 x i;    
      freevars_close_st_term' t2 x i;          
      freevars_close_term_opt' post x (i + 1)      

    | Tm_ElimExists t ->
      freevars_close_term' t x i
      
    | Tm_IntroExists _ t e ->
      freevars_close_term' t x i;
      freevars_close_term' e x i

    | Tm_While inv cond body ->
      freevars_close_term' inv x (i + 1);
      freevars_close_st_term' cond x i;
      freevars_close_st_term' body x i

    | Tm_Admit _ _ t post ->
      freevars_close_term' t x i;
      freevars_close_term_opt' post x (i + 1)

    | Tm_Protect t ->
      freevars_close_st_term' t x i
      
let freevars_close_term (e:term) (x:var) (i:index)
  : Lemma 
    (ensures freevars (close_term' e x i) `Set.equal`
             (freevars e `set_minus` x))
  = freevars_close_term' e x i

let freevars_close_st_term e x i = freevars_close_st_term' e x i

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
  = calc (==) {
     freevars e;
     (==) {  close_open_inverse e x }
     freevars (close_term (open_term e x) x);
     (==) {  freevars_close_term (open_term e x) x 0 }
     freevars (open_term e x) `set_minus` x;
    }

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

#push-options "--fuel 2 --ifuel 2"
let tot_typing_freevars (#f:_) (#g:_) (#t:_) (#ty:_)
                        (d:tot_typing f g t ty)
  : Lemma 
    (ensures freevars t `Set.subset` vars_of_env g /\
             freevars ty `Set.subset` vars_of_env g)
  = elab_freevars_inverse t;
    elab_freevars_inverse ty;      
    let E d = d in
    refl_typing_freevars d;
    assert (vars_of_env_r (extend_env_l f g) `Set.equal` (vars_of_env g))

let bind_comp_freevars (#f:_) (#g:_) (#x:_) (#c1 #c2 #c:_)
                       (d:bind_comp f g x c1 c2 c)
  : Lemma 
    (requires freevars_comp c1 `Set.subset` vars_of_env g /\
              freevars_comp c2 `Set.subset` (Set.union (vars_of_env g) (Set.singleton x)))
    (ensures freevars_comp c `Set.subset` vars_of_env g)
  = match d with
    | Bind_comp _ _ _ _ dt _ _ 
    | Bind_comp_ghost_l _ _ _ _ _ dt _ _ 
    | Bind_comp_ghost_r _ _ _ _ _ dt _ _  -> tot_typing_freevars dt

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
      let t : RT.typing (extend_env_l f g) token (elab_term (mk_vprop_eq t0 t1)) = RT.T_Token _ _ _ () in
      refl_typing_freevars t;
      elab_freevars_inverse (mk_vprop_eq t0 t1)

let st_equiv_freevars #f #g (#c1 #c2:_)
                      (d:st_equiv f g c1 c2)
  : Lemma
    (requires freevars_comp c1 `Set.subset` vars_of_env g)
    (ensures freevars_comp c2 `Set.subset` vars_of_env g)    
  = let ST_VPropEquiv _ _ _ x _ _ _ eq_pre eq_post = d in
    vprop_equiv_freevars eq_pre;
    vprop_equiv_freevars eq_post;
    freevars_open_term_inv (comp_post c1) x;     
    freevars_open_term_inv (comp_post c2) x


let src_typing_freevars_t (d':'a) = 
    (#f:_) -> (#g:_) -> (#t:_) -> (#c:_) -> (d:st_typing f g t c { d << d' }) ->
    Lemma 
    (ensures freevars_st t `Set.subset` vars_of_env g /\
             freevars_comp c `Set.subset` vars_of_env g)

let st_comp_typing_freevars #f #g #st (d:st_comp_typing f g st)
  : Lemma
    (ensures freevars_st_comp st `Set.subset` vars_of_env g)
    (decreases d)
  = let STC _ _ x dt pre post = d in
    tot_typing_freevars dt;
    tot_typing_freevars pre;
    tot_typing_freevars post

let comp_typing_freevars  (#f:_) (#g:_) (#c:_) (#u:_)
                          (d:comp_typing f g c u)
  : Lemma 
    (ensures freevars_comp c `Set.subset` vars_of_env g)
    (decreases d)
  = match d with
    | CT_Tot _ _ _ dt ->
      tot_typing_freevars dt

    | CT_ST _ _ dst -> 
      st_comp_typing_freevars dst

    | CT_STAtomic _ _ _ it dst -> 
      tot_typing_freevars it;
      st_comp_typing_freevars dst

    | CT_STGhost _ _ _ it dst -> 
      tot_typing_freevars it;
      st_comp_typing_freevars dst

let freevars_open_st_term_inv (e:st_term) 
                              (x:var {~ (x `Set.mem` freevars_st e) })
  : Lemma 
    (ensures freevars_st e `Set.equal` (freevars_st (open_st_term e x) `set_minus` x))
    [SMTPat (freevars_st (open_st_term e x))]
  = calc (==) {
     freevars_st e;
     (==) {  close_open_inverse_st e x }
     freevars_st (close_st_term (open_st_term e x) x);
     (==) {  freevars_close_st_term' (open_st_term e x) x 0 }
     freevars_st (open_st_term e x) `set_minus` x;
    }
#pop-options
#pop-options

#push-options "--fuel 10 --ifuel 10 --z3rlimit_factor 20 --z3cliopt 'smt.qi.eager_threshold=100' --query_stats"
let rec st_typing_freevars (#f:_) (#g:_) (#t:_) (#c:_)
                            (d:st_typing f g t c)
  : Lemma 
    (ensures freevars_st t `Set.subset` vars_of_env g /\
             freevars_comp c `Set.subset` vars_of_env g)
    (decreases d)

 = match d with
   // | T_Tot _g e t dt ->
   //    tot_typing_freevars dt
      
   | T_Abs _g  x _q ty _u body cres dt db ->
      tot_typing_freevars dt;
      st_typing_freevars db;
      freevars_close_comp cres x 0;
      freevars_open_st_term_inv body x

   | T_STApp _ _ _ _ res arg st at ->
     tot_typing_freevars st;
     tot_typing_freevars at;
     freevars_open_comp res arg 0

   | T_Return _ c use_eq u t e post x t_typing e_typing post_typing ->
     tot_typing_freevars t_typing;
     tot_typing_freevars e_typing;
     tot_typing_freevars post_typing;
     freevars_open_term post (term_of_var x) 0;
     let post =
       if use_eq then Tm_Star post (Tm_Pure (mk_eq2 u t (null_bvar 0) e))
       else post in
     freevars_open_term post e 0

   | T_Lift _ _ _ _ d1 l ->
     st_typing_freevars d1


   | T_Bind _ e1 e2 _ _ x c d1 dc1 d2 bc ->
     st_typing_freevars d1;
     tot_typing_freevars dc1;
     st_typing_freevars d2;
     bind_comp_freevars bc;
     freevars_open_st_term_inv e2 x

   | T_If _ _b e1 e2 _c _u hyp tb d1 d2 (E ct) ->
     tot_typing_freevars tb;
     comp_typing_freevars ct;
     st_typing_freevars d1;
     st_typing_freevars d2

   | T_Frame _ _ _ _ df dc ->
     tot_typing_freevars df;
     st_typing_freevars dc

   | T_ElimExists _ u t p x dt dv ->
     let x_tm = Tm_Var {nm_index=x;nm_ppname=RT.pp_name_default} in
     tot_typing_freevars dt;
     tot_typing_freevars dv;
     assert (Set.equal (freevars (Pulse.Typing.mk_reveal u t x_tm))
                       (Set.union (freevars t) (Set.singleton x)));
     freevars_open_term p (Pulse.Typing.mk_reveal u t x_tm) 0;
     assert (Set.subset (freevars (open_term' p (Pulse.Typing.mk_reveal u t x_tm) 0))
                       (Set.union (freevars p)
                                  (Set.union (freevars t)
                                             (Set.singleton x))));
     assert (~ (Set.mem x (freevars t)));
     assert (~ (Set.mem x (freevars p)));
     assert (Set.subset (set_minus (freevars (open_term' p (Pulse.Typing.mk_reveal u t x_tm) 0)) x)
                       (Set.union (freevars p)
                                  (freevars t)));
     assert (Set.subset
               (set_minus (freevars (open_term' p (Pulse.Typing.mk_reveal u t x_tm) 0)) x)
               (vars_of_env g))

   | T_IntroExists _ u tt p w dt dv dw ->
     tot_typing_freevars dt;
     tot_typing_freevars dv;
     tot_typing_freevars dw;
     assert (freevars_st t `Set.subset` vars_of_env g);
     calc (Set.subset) {
        freevars_comp c;
      (Set.equal) {}
        freevars_comp (comp_intro_exists u tt p w);
      (Set.equal) {}
        freevars Tm_EmpInames `Set.union`
        (freevars tm_unit `Set.union`
        (freevars (open_term' p w 0) `Set.union`
         freevars (Tm_ExistsSL u tt p should_elim_true)));
      (Set.equal) {} 
        (freevars (open_term' p w 0) `Set.union`
         freevars (Tm_ExistsSL u tt p should_elim_true));
      (Set.subset) { freevars_open_term p w 0 }
        (freevars p `Set.union` 
         freevars w `Set.union`
         freevars_st t `Set.union`
         freevars p);
     }

   | T_IntroExistsErased _ u tt p w dt dv dw ->
     tot_typing_freevars dt;
     tot_typing_freevars dv;
     tot_typing_freevars dw;
     assert (freevars_st t `Set.subset` vars_of_env g);
     calc (Set.subset) {
        freevars_comp c;
      (Set.equal) {}
        freevars_comp (comp_intro_exists_erased u tt p w);
      (Set.equal) {}
        freevars Tm_EmpInames `Set.union`
        (freevars tm_unit `Set.union`
        (freevars (open_term' p (Pulse.Typing.mk_reveal u tt w) 0) `Set.union`
         freevars (Tm_ExistsSL u tt p should_elim_true)));
      (Set.equal) {} 
        (freevars (open_term' p (Pulse.Typing.mk_reveal u tt w) 0) `Set.union`
         freevars (Tm_ExistsSL u tt p should_elim_true));
      (Set.subset) { freevars_open_term p (Pulse.Typing.mk_reveal u tt w) 0 }
        (freevars p `Set.union` 
         freevars w `Set.union`
         freevars_st t `Set.union`
         freevars p);
     }

   | T_Equiv _ _ _ _ d2 deq ->
     st_typing_freevars d2;
     st_equiv_freevars deq

   | T_While _ inv _ _ inv_typing cond_typing body_typing ->
     tot_typing_freevars inv_typing;
     st_typing_freevars cond_typing;
     st_typing_freevars body_typing;
     assert (freevars tm_false `Set.equal` Set.empty);
     freevars_open_term inv tm_false 0;
     assert (freevars (open_term' inv tm_false 0) `Set.subset` freevars inv)

   | T_Admit _ s _ (STC _ _ x t_typing pre_typing post_typing) ->
     tot_typing_freevars t_typing;
     tot_typing_freevars pre_typing;
     tot_typing_freevars post_typing;
     freevars_open_term s.post (term_of_var x) 0
#pop-options //takes about 23s
