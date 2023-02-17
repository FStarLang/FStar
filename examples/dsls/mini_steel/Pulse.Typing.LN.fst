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
val elab_ln_inverse (e:pure_term)
  : Lemma 
    (requires RT.ln (elab_pure e))
    (ensures ln e)
    [SMTPat (RT.ln (elab_pure e))]

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
    | Tm_UVar _ -> ()

    | Tm_Pure p ->
      open_term_ln' p x i

    | Tm_Refine b t ->
      open_term_ln' b.binder_ty x i;
      open_term_ln' t x (i + 1)

    | Tm_Abs b _q pre body post ->
      open_term_ln' b.binder_ty x i;
      open_term_ln' pre x (i + 1);
      open_term_ln' body x (i + 1);
      open_term_ln'_opt post x (i + 2)

    | Tm_PureApp l _ r
    | Tm_STApp l _ r
    | Tm_Star l r ->
      open_term_ln' l x i;
      open_term_ln' r x i

    | Tm_Bind e1 e2 ->
      open_term_ln' e1 x i;
      open_term_ln' e2 x (i + 1)

    | Tm_Let t e1 e2 ->
      open_term_ln' t x i;    
      open_term_ln' e1 x i;
      open_term_ln' e2 x (i + 1)

    | Tm_ExistsSL _ t b
    | Tm_ForallSL _ t b ->
      open_term_ln' t x i;    
      open_term_ln' b x (i + 1)
      
    | Tm_If t0 t1 t2 post ->
      open_term_ln' t0 x i;    
      open_term_ln' t1 x i;    
      open_term_ln' t2 x i;          
      open_term_ln'_opt post x (i + 1)      

    | Tm_Arrow b _ body ->
      open_term_ln' b.binder_ty x i;
      open_comp_ln' body x (i + 1)

    | Tm_ElimExists t -> open_term_ln' t x i
    | Tm_IntroExists t e ->
      open_term_ln' t x i;
      open_term_ln' e x i

and open_comp_ln' (c:comp)
                       (x:term)
                       (i:index)
  : Lemma 
    (requires ln'_comp (open_comp' c x i) (i - 1))
    (ensures ln'_comp c i)
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

and open_term_ln'_opt (t:option term) (x:term) (i:index)
  : Lemma
    (requires ln'_opt (open_term_opt' t x i) (i - 1))
    (ensures ln'_opt t i)
    (decreases t)
  = match t with
    | None -> ()
    | Some t -> open_term_ln' t x i
    
let open_term_ln (e:term) (v:var)
  : Lemma 
    (requires ln (open_term e v))
    (ensures ln' e 0)
  = open_term_ln' e (term_of_var v) 0

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
    | Tm_UVar _ -> ()

    | Tm_Pure p ->
      close_term_ln' p x i

    | Tm_Refine b t ->
      close_term_ln' b.binder_ty x i;
      close_term_ln' t x (i + 1)

    | Tm_Abs b _q pre body post ->
      close_term_ln' b.binder_ty x i;
      close_term_ln' pre x (i + 1);
      close_term_ln' body x (i + 1);
      close_term_ln'_opt post x (i + 2)

    | Tm_PureApp l _ r
    | Tm_STApp l _ r
    | Tm_Star l r ->
      close_term_ln' l x i;
      close_term_ln' r x i

    | Tm_Bind e1 e2 ->
      close_term_ln' e1 x i;
      close_term_ln' e2 x (i + 1)

    | Tm_Let t e1 e2 ->
      close_term_ln' t x i;    
      close_term_ln' e1 x i;
      close_term_ln' e2 x (i + 1)

    | Tm_ExistsSL _ t b
    | Tm_ForallSL _ t b ->
      close_term_ln' t x i;    
      close_term_ln' b x (i + 1)
      
    | Tm_If t0 t1 t2 post ->
      close_term_ln' t0 x i;    
      close_term_ln' t1 x i;    
      close_term_ln' t2 x i;          
      close_term_ln'_opt post x (i + 1)      

    | Tm_Arrow b _ body ->
      close_term_ln' b.binder_ty x i;
      close_comp_ln' body x (i + 1)

    | Tm_ElimExists t -> close_term_ln' t x i
    | Tm_IntroExists t e ->
      close_term_ln' t x i;
      close_term_ln' e x i

and close_comp_ln' (c:comp)
                   (x:var)
                   (i:index)
  : Lemma 
    (requires ln'_comp c (i - 1))
    (ensures ln'_comp (close_comp' c x i) i)
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

and close_term_ln'_opt (t:option term) (x:var) (i:index)
  : Lemma
    (requires ln'_opt t (i - 1))
    (ensures ln'_opt (close_term_opt' t x i) i)
    (decreases t)
  = match t with
    | None -> ()
    | Some t -> close_term_ln' t x i

let close_comp_ln (c:comp) (v:var)
  : Lemma 
    (requires ln_c c)
    (ensures ln'_comp (close_comp c v) 0)
  = close_comp_ln' c v 0

let rec src_typing_ln (#f:_) (#g:_) (#t:_) (#c:_)
                      (d:src_typing f g t c)
  : Lemma 
    (ensures ln t /\ ln_c c)
    (decreases d)
  = match d with
    | T_Tot _g _e _t dt ->
      well_typed_terms_are_ln _ _ _ dt

    | T_Abs _g _pp x _q ty _u body c _pre_hint _post_hint (E dt) db ->
      src_typing_ln dt;
      src_typing_ln db;
      assert (ln ty);
      assert (ln_c c);
      assert (ln (open_term body x));
      open_term_ln body x;
      close_comp_ln c x;
      assume (_pre_hint == Tm_Emp /\ None? _post_hint);
      assert (ln t)

      
    | _ -> admit()

