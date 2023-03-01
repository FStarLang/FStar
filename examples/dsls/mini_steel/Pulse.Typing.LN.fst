module Pulse.Typing.LN
module RT = Refl.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Typing
open Pulse.Elaborate.Pure

assume
val well_typed_terms_are_ln (g:R.env) (e:R.term) (t:R.term) (_:RT.typing g e t)
  : Lemma (ensures RT.ln e /\ RT.ln t)

assume
val elab_ln_inverse (e:term)
  : Lemma 
    (requires RT.ln (elab_term e))
    (ensures ln e)


let rec open_term_ln' (e:term)
                      (x:term)
                      (i:index)
  : Lemma 
    (requires ln' (open_term' e x i) (i - 1))
    (ensures ln' e i)
    (decreases e)
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
      open_term_ln' p x i

    | Tm_Refine b t ->
      open_term_ln' b.binder_ty x i;
      open_term_ln' t x (i + 1)


    | Tm_PureApp l _ r
    | Tm_Star l r ->
      open_term_ln' l x i;
      open_term_ln' r x i

    | Tm_Let t e1 e2 ->
      open_term_ln' t x i;    
      open_term_ln' e1 x i;
      open_term_ln' e2 x (i + 1)

    | Tm_ExistsSL _ t b _
    | Tm_ForallSL _ t b ->
      open_term_ln' t x i;    
      open_term_ln' b x (i + 1)

    | Tm_Arrow b _ body ->
      open_term_ln' b.binder_ty x i;
      open_comp_ln' body x (i + 1)

and open_comp_ln' (c:comp)
                       (x:term)
                       (i:index)
  : Lemma 
    (requires ln_c' (open_comp' c x i) (i - 1))
    (ensures ln_c' c i)
    (decreases c)
  = match c with
    | C_Tot t ->
      open_term_ln' t x i

    | C_ST s ->
      open_term_ln' s.res x i;
      open_term_ln' s.pre x i;      
      open_term_ln' s.post x (i + 1)

    | C_STAtomic n s
    | C_STGhost n s ->    
      open_term_ln' n x i;    
      open_term_ln' s.res x i;
      open_term_ln' s.pre x i;      
      open_term_ln' s.post x (i + 1)

let open_term_ln_opt' (t:option term) (x:term) (i:index)
  : Lemma
    (requires ln_opt' (open_term_opt' t x i) (i - 1))
    (ensures ln_opt' t i)
    (decreases t)
  = match t with
    | None -> ()
    | Some t -> open_term_ln' t x i

let rec open_st_term_ln' (e:st_term)
                         (x:term)
                         (i:index)
  : Lemma 
    (requires ln_st' (open_st_term' e x i) (i - 1))
    (ensures ln_st' e i)
    (decreases e)
  = match e with
    | Tm_Return _ _ e ->
      open_term_ln' e x i
      
    | Tm_STApp l _ r ->
      open_term_ln' l x i;
      open_term_ln' r x i

    | Tm_Abs b _q pre body post ->
      open_term_ln' b.binder_ty x i;
      open_term_ln_opt' pre x (i + 1);
      open_st_term_ln' body x (i + 1);
      open_term_ln_opt' post x (i + 2)
      
    | Tm_Bind e1 e2 ->
      open_st_term_ln' e1 x i;
      open_st_term_ln' e2 x (i + 1)

      
    | Tm_If t0 t1 t2 post ->
      open_term_ln' t0 x i;    
      open_st_term_ln' t1 x i;    
      open_st_term_ln' t2 x i;          
      open_term_ln_opt' post x (i + 1)      

    | Tm_ElimExists t -> open_term_ln' t x i
    | Tm_IntroExists t e ->
      open_term_ln' t x i;
      open_term_ln' e x i

    | Tm_While inv cond body ->
      open_term_ln' inv x (i + 1);
      open_st_term_ln' cond x i;
      open_st_term_ln' body x i

    | Tm_Par preL eL postL preR eR postR ->
      open_term_ln' preL x i;
      open_st_term_ln' eL x i;
      open_term_ln' postL x (i + 1);
      open_term_ln' preR x i;
      open_st_term_ln' eR x i;
      open_term_ln' postR x (i + 1)

    | Tm_Admit _ _ t post ->
      open_term_ln' t x i;
      open_term_ln_opt' post x (i + 1)

    | Tm_Protect t ->
      open_st_term_ln' t x i
      
let open_term_ln (e:term) (v:var)
  : Lemma 
    (requires ln (open_term e v))
    (ensures ln' e 0)
  = open_term_ln' e (term_of_var v) 0


let open_st_term_ln (e:st_term) (v:var)
  : Lemma 
    (requires ln_st (open_st_term e v))
    (ensures ln_st' e 0)
  = open_st_term_ln' e (term_of_var v) 0

let rec ln_weakening (e:term) (i j:int)
  : Lemma 
    (requires ln' e i /\ i <= j)
    (ensures ln' e j)      
    (decreases e)
    [SMTPat (ln' e j);
     SMTPat (ln' e i)]
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
      ln_weakening p i j
      
    | Tm_Refine b t ->
      ln_weakening b.binder_ty i j;
      ln_weakening t (i + 1) (j + 1)

    | Tm_PureApp l _ r
    | Tm_Star l r ->
      ln_weakening l i j;
      ln_weakening r i j

    | Tm_Let t e1 e2 ->
      ln_weakening t i j;    
      ln_weakening e1 i j;
      ln_weakening e2 (i + 1) (j + 1)

    | Tm_ExistsSL _ t b _
    | Tm_ForallSL _ t b ->
      ln_weakening t i j;    
      ln_weakening b (i + 1) (j + 1)

    | Tm_Arrow b _ body ->
      ln_weakening b.binder_ty i j;
      ln_weakening_comp body (i + 1) (j + 1)

and ln_weakening_comp (c:comp) (i j:int)
  : Lemma 
    (requires ln_c' c i /\ i <= j)
    (ensures ln_c' c j)      
    (decreases c)
  = match c with
    | C_Tot t ->
      ln_weakening t i j

    | C_ST s ->
      ln_weakening s.res i j;
      ln_weakening s.pre i j;      
      ln_weakening s.post (i + 1) (j + 1)

    | C_STAtomic n s
    | C_STGhost n s ->    
      ln_weakening n i j;    
      ln_weakening s.res i j;
      ln_weakening s.pre i j;      
      ln_weakening s.post (i + 1) (j + 1)

let ln_weakening_opt (t:option term) (i j:int)
  : Lemma
    (requires ln_opt' t i /\ i <= j)
    (ensures ln_opt' t j)
    (decreases t)
  = match t with
    | None -> ()
    | Some t -> ln_weakening t i j

let rec ln_weakening_st (t:st_term) (i j:int)
  : Lemma
    (requires ln_st' t i /\ i <= j)
    (ensures ln_st' t j)
    (decreases t)
  = match t with
    | Tm_Return _ _ t ->
      ln_weakening t i j

    | Tm_ElimExists t ->
      ln_weakening t i j
      
    | Tm_IntroExists t e ->
      ln_weakening t i j;
      ln_weakening e i j

    | Tm_While inv cond body ->
      ln_weakening inv (i + 1) (j + 1);
      ln_weakening_st cond i j;
      ln_weakening_st body i j

    
    | Tm_If t0 t1 t2 post ->
      ln_weakening t0 i j;    
      ln_weakening_st t1 i j;    
      ln_weakening_st t2 i j;          
      ln_weakening_opt post (i + 1) (j + 1)

    | Tm_STApp l _ r ->
      ln_weakening l i j;
      ln_weakening r i j      

    | Tm_Bind e1 e2 ->
      ln_weakening_st e1 i j;
      ln_weakening_st e2 (i + 1) (j + 1)

    | Tm_Abs b _q pre body post ->
      ln_weakening b.binder_ty i j;
      ln_weakening_opt pre (i + 1) (j + 1);
      ln_weakening_st body (i + 1) (j + 1);
      ln_weakening_opt post (i + 2) (j + 2)

    | Tm_Par preL eL postL preR eR postR ->
      ln_weakening preL i j;
      ln_weakening_st eL i j;
      ln_weakening postL (i + 1) (j + 1);
      ln_weakening preR i j;
      ln_weakening_st eR i j;
      ln_weakening postR (i + 1) (j + 1)

    | Tm_Admit _ _ t post ->
      ln_weakening t i j;
      ln_weakening_opt post (i + 1) (j + 1)
      
    | Tm_Protect t ->
      ln_weakening_st t i j
      
let rec open_term_ln_inv' (e:term)
                          (x:term { ln x })
                          (i:index)
  : Lemma 
    (requires ln' e i)
    (ensures ln' (open_term' e x i) (i - 1))
    (decreases e)
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
    | Tm_Unknown ->
      ln_weakening x (-1) (i - 1)

    | Tm_Pure p ->
      open_term_ln_inv' p x i

    | Tm_Refine b t ->
      open_term_ln_inv' b.binder_ty x i;
      open_term_ln_inv' t x (i + 1)

    | Tm_PureApp l _ r
    | Tm_Star l r ->
      open_term_ln_inv' l x i;
      open_term_ln_inv' r x i

    | Tm_Let t e1 e2 ->
      open_term_ln_inv' t x i;    
      open_term_ln_inv' e1 x i;
      open_term_ln_inv' e2 x (i + 1)

    | Tm_ExistsSL _ t b _
    | Tm_ForallSL _ t b ->
      open_term_ln_inv' t x i;    
      open_term_ln_inv' b x (i + 1)

    | Tm_Arrow b _ body ->
      open_term_ln_inv' b.binder_ty x i;
      open_comp_ln_inv' body x (i + 1)

and open_comp_ln_inv' (c:comp)
                      (x:term { ln x })
                      (i:index)
  : Lemma 
    (requires ln_c' c i)
    (ensures ln_c' (open_comp' c x i) (i - 1))
    (decreases c)
  = match c with
    | C_Tot t ->
      open_term_ln_inv' t x i

    | C_ST s ->
      open_term_ln_inv' s.res x i;
      open_term_ln_inv' s.pre x i;      
      open_term_ln_inv' s.post x (i + 1)

    | C_STAtomic n s
    | C_STGhost n s ->    
      open_term_ln_inv' n x i;    
      open_term_ln_inv' s.res x i;
      open_term_ln_inv' s.pre x i;      
      open_term_ln_inv' s.post x (i + 1)

let open_term_ln_inv_opt' (t:option term)
                          (x:term { ln x })
                          (i:index)
  : Lemma
    (requires ln_opt' t i)
    (ensures ln_opt' (open_term_opt' t x i) (i - 1))
    (decreases t)
  = match t with
    | None -> ()
    | Some t -> open_term_ln_inv' t x i

let rec open_term_ln_inv_st' (t:st_term)
                             (x:term { ln x })
                             (i:index)
  : Lemma
    (requires ln_st' t i)
    (ensures ln_st' (open_st_term' t x i) (i - 1))
    (decreases t)
  = match t with
    | Tm_Return _ _ t ->
      open_term_ln_inv' t x i

    | Tm_ElimExists t ->
      open_term_ln_inv' t x i
      
    | Tm_IntroExists t e ->
      open_term_ln_inv' t x i;
      open_term_ln_inv' e x i

    | Tm_While inv cond body ->
      open_term_ln_inv' inv x (i + 1);
      open_term_ln_inv_st' cond x i;
      open_term_ln_inv_st' body x i

    | Tm_If t0 t1 t2 post ->
      open_term_ln_inv' t0 x i;    
      open_term_ln_inv_st' t1 x i;    
      open_term_ln_inv_st' t2 x i;          
      open_term_ln_inv_opt' post x (i + 1)      

    | Tm_Bind e1 e2 ->
      open_term_ln_inv_st' e1 x i;
      open_term_ln_inv_st' e2 x (i + 1)

    | Tm_STApp l _ r ->
      open_term_ln_inv' l x i;
      open_term_ln_inv' r x i

    | Tm_Abs b _q pre body post ->
      open_term_ln_inv' b.binder_ty x i;
      open_term_ln_inv_opt' pre x (i + 1);
      open_term_ln_inv_st' body x (i + 1);
      open_term_ln_inv_opt' post x (i + 2)

    | Tm_Par preL eL postL preR eR postR ->
      open_term_ln_inv' preL x i;
      open_term_ln_inv_st' eL x i;
      open_term_ln_inv' postL x (i + 1);
      open_term_ln_inv' preR x i;
      open_term_ln_inv_st' eR x i;
      open_term_ln_inv' postR x (i + 1)

    | Tm_Admit _ _ t post ->
      open_term_ln_inv' t x i;
      open_term_ln_inv_opt' post x (i + 1)

    | Tm_Protect t ->
      open_term_ln_inv_st' t x i
      
let rec close_term_ln' (e:term)
                       (x:var)
                       (i:index)
  : Lemma 
    (requires ln' e (i - 1))
    (ensures ln' (close_term' e x i) i)
    (decreases e)
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
      close_term_ln' p x i

    | Tm_Refine b t ->
      close_term_ln' b.binder_ty x i;
      close_term_ln' t x (i + 1)

    | Tm_PureApp l _ r
    | Tm_Star l r ->
      close_term_ln' l x i;
      close_term_ln' r x i

    | Tm_Let t e1 e2 ->
      close_term_ln' t x i;    
      close_term_ln' e1 x i;
      close_term_ln' e2 x (i + 1)

    | Tm_ExistsSL _ t b _
    | Tm_ForallSL _ t b ->
      close_term_ln' t x i;    
      close_term_ln' b x (i + 1)

    | Tm_Arrow b _ body ->
      close_term_ln' b.binder_ty x i;
      close_comp_ln' body x (i + 1)

and close_comp_ln' (c:comp)
                   (x:var)
                   (i:index)
  : Lemma 
    (requires ln_c' c (i - 1))
    (ensures ln_c' (close_comp' c x i) i)
    (decreases c)
  = match c with
    | C_Tot t ->
      close_term_ln' t x i

    | C_ST s ->
      close_term_ln' s.res x i;
      close_term_ln' s.pre x i;      
      close_term_ln' s.post x (i + 1)

    | C_STAtomic n s
    | C_STGhost n s ->    
      close_term_ln' n x i;    
      close_term_ln' s.res x i;
      close_term_ln' s.pre x i;      
      close_term_ln' s.post x (i + 1)

let close_term_ln_opt' (t:option term) (x:var) (i:index)
  : Lemma
    (requires ln_opt' t (i - 1))
    (ensures ln_opt' (close_term_opt' t x i) i)
    (decreases t)
  = match t with
    | None -> ()
    | Some t -> close_term_ln' t x i

let rec close_st_term_ln' (t:st_term) (x:var) (i:index)
  : Lemma
    (requires ln_st' t (i - 1))
    (ensures ln_st' (close_st_term' t x i) i)
    (decreases t)
  = match t with
    | Tm_Return _ _ t ->
      close_term_ln' t x i

    | Tm_ElimExists t ->
      close_term_ln' t x i
      
    | Tm_IntroExists t e ->
      close_term_ln' t x i;
      close_term_ln' e x i

    | Tm_While inv cond body ->
      close_term_ln' inv x (i + 1);
      close_st_term_ln' cond x i;
      close_st_term_ln' body x i

    | Tm_If t0 t1 t2 post ->
      close_term_ln' t0 x i;    
      close_st_term_ln' t1 x i;    
      close_st_term_ln' t2 x i;          
      close_term_ln_opt' post x (i + 1)      

    | Tm_Bind e1 e2 ->
      close_st_term_ln' e1 x i;
      close_st_term_ln' e2 x (i + 1)

    | Tm_STApp l _ r ->
      close_term_ln' l x i;
      close_term_ln' r x i

    | Tm_Abs b _q pre body post ->
      close_term_ln' b.binder_ty x i;
      close_term_ln_opt' pre x (i + 1);
      close_st_term_ln' body x (i + 1);
      close_term_ln_opt' post x (i + 2)

    | Tm_Par preL eL postL preR eR postR ->
      close_term_ln' preL x i;
      close_st_term_ln' eL x i;
      close_term_ln' postL x (i + 1);
      close_term_ln' preR x i;
      close_st_term_ln' eR x i;
      close_term_ln' postR x (i + 1)

    | Tm_Admit _ _ t post ->
      close_term_ln' t x i;
      close_term_ln_opt' post x (i + 1)

    | Tm_Protect t ->
      close_st_term_ln' t x i
      
let close_comp_ln (c:comp) (v:var)
  : Lemma 
    (requires ln_c c)
    (ensures ln_c' (close_comp c v) 0)
  = close_comp_ln' c v 0

#push-options "--ifuel 2 --z3rlimit_factor 4 --z3cliopt 'smt.qi.eager_threshold=100'"

let test x = assert (x + 1 > x)

let lift_comp_ln #f #g #c1 #c2 (d:lift_comp f g c1 c2)
  : Lemma
    (requires ln_c c1)
    (ensures ln_c c2)    
  = ()


let rec vprop_equiv_ln (#f:_) (#g:_) (#t0 #t1:_) (v:vprop_equiv f g t0 t1)
  : Lemma (ensures ln t0 <==> ln t1)
          (decreases v)
  = match v with
    | VE_Refl _ _ -> ()
    | VE_Sym _ _ _ v' -> 
      vprop_equiv_ln v'
    | VE_Trans g t0 t2 t1 v02 v21 ->
      vprop_equiv_ln v02;
      vprop_equiv_ln v21
    | VE_Ctxt g s0 s1 s0' s1' v0 v1 ->
      vprop_equiv_ln v0;
      vprop_equiv_ln v1
    | VE_Unit g t -> ()
    | VE_Comm g t0 t1 -> ()
    | VE_Assoc g t0 t1 t2 -> ()
    | VE_Ext g t0 t1 token ->
      let t : RT.typing (extend_env_l f g) token (elab_term (mk_vprop_eq t0 t1)) =
        RT.T_Token _ _ _ ()
      in
      well_typed_terms_are_ln _ _ _ t;
      elab_ln_inverse (mk_vprop_eq t0 t1)

let st_equiv_ln #f #g #c1 #c2 (d:st_equiv f g c1 c2)
  : Lemma 
    (requires ln_c c1)
    (ensures ln_c c2)
  = let ST_VPropEquiv _ _ _ x (E dpre) _dres _dpost eq_pre eq_post = d in
    vprop_equiv_ln eq_pre;
    open_term_ln_inv' (comp_post c1) (term_of_var x) 0;
    vprop_equiv_ln eq_post;
    open_term_ln' (comp_post c2) (term_of_var x) 0

let bind_comp_ln #f #g #x #c1 #c2 #c (d:bind_comp f g x c1 c2 c)
  : Lemma 
    (requires ln_c c1 /\ ln_c c2)
    (ensures ln_c c)
  = ()

let tot_typing_ln (#f:_) (#g:_) (#e:_) (#t:_)
                  (d:tot_typing f g e t)
  : Lemma 
    (ensures ln e /\ ln t)
  = let E dt = d in
    well_typed_terms_are_ln _ _ _ dt;
    elab_ln_inverse e;
    elab_ln_inverse t
  
#push-options "--query_stats --fuel 8 --ifuel 8 --z3rlimit_factor 20"
let rec st_typing_ln (#f:_) (#g:_) (#t:_) (#c:_)
                     (d:st_typing f g t c)
  : Lemma 
    (ensures ln_st t /\ ln_c c)
    (decreases d)
  = match d with
    // | T_Tot _g e t dt ->
    //   tot_typing_ln dt

    | T_Abs _g x _q ty _u body c dt db ->
      tot_typing_ln dt;
      st_typing_ln db;
      open_st_term_ln body x;
      close_comp_ln c x

    | T_STApp _ _ _ _ res arg st at ->
      tot_typing_ln st;
      tot_typing_ln at;
      open_comp_ln_inv' res arg 0


    | T_Return _ c use_eq u t e post x t_typing e_typing post_typing ->
      tot_typing_ln t_typing;
      tot_typing_ln e_typing;
      tot_typing_ln post_typing;
      open_term_ln' post (term_of_var x) 0;
      let post =
        if use_eq then Tm_Star post (Tm_Pure (mk_eq2 u t (null_bvar 0) e))
        else post in
      open_term_ln_inv' post e 0
      
    | T_Lift _ _ _ _ d1 l ->
      st_typing_ln d1;
      lift_comp_ln l

    | T_Bind _ _ e2 _ _ x _ d1 dc1 d2 bc ->
      st_typing_ln d1;
      tot_typing_ln dc1;
      st_typing_ln d2;
      open_st_term_ln e2 x;
      bind_comp_ln bc

    | T_If _ _ _ _ _ _ _ tb d1 d2 _ ->
      tot_typing_ln tb;
      st_typing_ln d1;
      st_typing_ln d2

    | T_Frame _ _ _ _ df dc ->
      tot_typing_ln df;
      st_typing_ln dc

    | T_ElimExists _ u t p x dt dv ->
      tot_typing_ln dt;
      tot_typing_ln dv;
      let x_tm = Tm_Var {nm_index=x;nm_ppname=RT.pp_name_default} in
      open_term_ln_inv' p (Pulse.Typing.mk_reveal u t x_tm) 0;
      close_term_ln' (open_term' p (Pulse.Typing.mk_reveal u t x_tm) 0) x 0

    | T_IntroExists _ u t p e dt dv dw ->
      tot_typing_ln dt;
      tot_typing_ln dv;
      tot_typing_ln dw;
      open_term_ln_inv' p e 0
      
    | T_Equiv _ _ _ _ d2 deq ->
      st_typing_ln d2;
      st_equiv_ln deq

    | T_While _ inv _ _ inv_typing cond_typing body_typing ->
      tot_typing_ln inv_typing;
      st_typing_ln cond_typing;
      st_typing_ln body_typing;
      open_term_ln_inv' inv tm_false 0

    | T_Par _ _ _ _ _ eL_typing eR_typing ->
      st_typing_ln eL_typing;
      st_typing_ln eR_typing

    | T_Admit _ s _ (STC _ _ x t_typing pre_typing post_typing) ->
      tot_typing_ln t_typing;
      tot_typing_ln pre_typing;
      tot_typing_ln post_typing;
      open_term_ln' s.post (term_of_var x) 0
#pop-options
