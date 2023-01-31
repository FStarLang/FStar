module Pulse.Elaborate.Pure
module RT = Refl.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
open FStar.List.Tot
open Pulse.Syntax

#push-options "--z3rlimit_factor 2"
let rec opening_pure_term_with_pure_term (x:pure_term) (v:pure_term) (i:index)
  : Lemma (ensures is_pure_term (open_term' x v i))
          [SMTPat (is_pure_term (open_term' x v i))]
  = let aux (y:pure_term {y << x}) (j:index)
      : Lemma (ensures (is_pure_term (open_term' y v j)))
      = opening_pure_term_with_pure_term y v j
    in
    match x with
    | Tm_BVar _
    | Tm_Var _
    | Tm_FVar _
    | Tm_UInst _ _
    | Tm_Constant _
    | Tm_Type _
    | Tm_VProp
    | Tm_Inames
    | Tm_EmpInames
    | Tm_Emp -> ()

    // | Tm_Abs t pre_hint body ->
    //   aux t i;
    //   aux body (i + 1)

    | Tm_Refine b phi ->
      aux b.binder_ty i;
      aux phi (i + 1)        

    | Tm_PureApp l _ r
    // | Tm_STApp l r
    | Tm_Star l r ->    
      aux l i; aux r i
                 
    | Tm_Let t e1 e2  ->
    // | Tm_Bind t e1 e2 ->    
      aux t i; aux e1 i; aux e2 (i + 1)
      
    | Tm_Pure p ->
      aux p i
              
    | Tm_ExistsSL t body
    | Tm_ForallSL t body ->
      aux t i; aux body (i + 1)
    
    | Tm_Arrow b _ c ->
      aux b.binder_ty i;
      opening_pure_comp_with_pure_term c v (i + 1)

    | Tm_If b then_ else_ ->
      aux b i; aux then_ i; aux else_ i

and opening_pure_comp_with_pure_term (x:pure_comp) (v:pure_term) (i:index)
  : Lemma (ensures is_pure_comp (open_comp' x v i))
          [SMTPat (is_pure_comp (open_comp' x v i))]
  = match x with
    | C_Tot t ->
      opening_pure_term_with_pure_term t v i
      
    | C_ST { res; pre; post } ->
      opening_pure_term_with_pure_term res v i;
      opening_pure_term_with_pure_term pre v i;
      opening_pure_term_with_pure_term post v (i + 1)

    | C_STAtomic inames { res; pre; post }
    | C_STGhost inames { res; pre; post } ->
      opening_pure_term_with_pure_term inames v i;
      opening_pure_term_with_pure_term res v i;
      opening_pure_term_with_pure_term pre v i;
      opening_pure_term_with_pure_term post v (i + 1)

let rec closing_pure_term (x:pure_term) (v:var) (i:index)
  : Lemma (ensures is_pure_term (close_term' x v i))
          [SMTPat (is_pure_term (close_term' x v i))]
  = let aux (y:pure_term {y << x}) (j:index)
      : Lemma (ensures (is_pure_term (close_term' y v j)))
      = closing_pure_term y v j
    in
    match x with
    | Tm_BVar _
    | Tm_Var _
    | Tm_FVar _
    | Tm_UInst _ _
    | Tm_Constant _
    | Tm_Type _
    | Tm_VProp
    | Tm_Inames
    | Tm_EmpInames
    | Tm_Emp -> ()

    // | Tm_Abs t pre_hint body ->
    //   aux t i;
    //   aux body (i + 1)

    | Tm_Refine b phi ->
      aux b.binder_ty i;
      aux phi (i + 1)

    | Tm_PureApp l _ r
    // | Tm_STApp l r
    | Tm_Star l r ->    
      aux l i; aux r i
                 
    | Tm_Let t e1 e2  ->
    // | Tm_Bind t e1 e2 ->    
      aux t i; aux e1 i; aux e2 (i + 1)
      
    | Tm_Pure p ->
      aux p i
              
    | Tm_ExistsSL t body
    | Tm_ForallSL t body ->
      aux t i; aux body (i + 1)
    
    | Tm_Arrow b _ c ->
      aux b.binder_ty i;
      closing_pure_comp c v (i + 1)

    | Tm_If b then_ else_ ->
      aux b i; aux then_ i; aux else_ i

and closing_pure_comp (x:pure_comp) (v:var) (i:index)
  : Lemma (ensures is_pure_comp (close_comp' x v i))
          [SMTPat (is_pure_comp (close_comp' x v i))]
  = match x with
    | C_Tot t ->
      closing_pure_term t v i
      
    | C_ST { res; pre; post } -> 
      closing_pure_term res v i;
      closing_pure_term pre v i;
      closing_pure_term post v (i + 1)

    | C_STAtomic inames { res; pre; post }
    | C_STGhost inames { res; pre; post } ->
      closing_pure_term inames v i;
      closing_pure_term res v i;
      closing_pure_term pre v i;
      closing_pure_term post v (i + 1)
#pop-options
