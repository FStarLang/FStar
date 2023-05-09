module Pulse.Syntax
module RTB = FStar.Reflection.Typing.Builtins
module RT = FStar.Reflection.Typing
module R = FStar.Reflection
module T = FStar.Tactics

let host_term_equality (t1 t2:host_term)
  : Lemma
    (ensures R.term_eq t1 t2 <==> t1==t2)
  = admit()

let rec eq_tm (t1 t2:term) 
  : Tot (b:bool { b <==> (t1 == t2) }) (decreases t1)
  = match t1, t2 with
    | Tm_VProp, Tm_VProp
    | Tm_Emp, Tm_Emp
    | Tm_Inames, Tm_Inames
    | Tm_EmpInames, Tm_EmpInames
    | Tm_Unknown, Tm_Unknown -> true
    | Tm_BVar x1, Tm_BVar x2 -> x1.bv_index = x2.bv_index
    | Tm_Var x1,  Tm_Var x2 -> x1.nm_index = x2.nm_index
    | Tm_FVar x1, Tm_FVar x2 -> x1.fv_name = x2.fv_name
    | Tm_UInst x1 us1, Tm_UInst x2 us2 -> x1.fv_name=x2.fv_name && us1=us2
    | Tm_Constant c1, Tm_Constant c2 -> c1=c2
    | Tm_Refine b1 t1, Tm_Refine b2 t2 -> 
      eq_tm b1.binder_ty b2.binder_ty &&
      eq_tm t1 t2
    | Tm_PureApp h1 o1 t1, Tm_PureApp h2 o2 t2 ->
      eq_tm h1 h2 &&
      o1=o2 &&
      eq_tm t1 t2
    | Tm_Star l1 r1, Tm_Star l2 r2 ->
      eq_tm l1 l2 &&
      eq_tm r1 r2
    | Tm_Pure p1, Tm_Pure p2 ->
      eq_tm p1 p2
    | Tm_Type u1, Tm_Type u2 ->
      u1=u2
    | Tm_Let t1 e1 e1', Tm_Let t2 e2 e2' ->
      eq_tm t1 t2 &&
      eq_tm e1 e2 &&
      eq_tm e1' e2'
    | Tm_ExistsSL u1 t1 b1 _, Tm_ExistsSL u2 t2 b2 _
    | Tm_ForallSL u1 t1 b1, Tm_ForallSL u2 t2 b2 ->
      u1=u2 &&
      eq_tm t1 t2 &&
      eq_tm b1 b2
    | Tm_Arrow b1 q1 c1, Tm_Arrow b2 q2 c2 ->
      eq_tm b1.binder_ty b2.binder_ty &&
      q1=q2 &&
      eq_comp c1 c2
    | Tm_UVar z1, Tm_UVar z2 ->
      z1=z2
    | Tm_FStar t1, Tm_FStar t2 ->
      host_term_equality t1 t2;
      R.term_eq t1 t2
    | _ -> false
    
and eq_comp (c1 c2:comp) 
  : Tot (b:bool { b <==> (c1 == c2) }) (decreases c1)
  = match c1, c2 with
    | C_Tot t1, C_Tot t2 ->
      eq_tm t1 t2
    | C_ST s1, C_ST s2 ->
      eq_st_comp s1 s2
    | C_STAtomic i1 s1, C_STAtomic i2 s2
    | C_STGhost i1 s1, C_STGhost i2 s2 ->
      eq_tm i1 i2 &&
      eq_st_comp s1 s2
    | _ -> false

and eq_st_comp (s1 s2:st_comp)  
  : b:bool { b <==> (s1 == s2) }
  = s1.u=s2.u && 
    eq_tm s1.res s2.res &&
    eq_tm s1.pre s2.pre &&
    eq_tm s1.post s2.post

let eq_tm_opt (t1 t2:option term)
  : b:bool { b <==> (t1 == t2) }
  = match t1, t2 with
    | None, None -> true
    | Some t1, Some t2 -> eq_tm t1 t2
    | _ -> false

let rec eq_tm_list (t1 t2:list term)
  : b:bool { b <==> (t1 == t2) }
  = match t1, t2 with
    | [], [] -> true
    | h1::t1, h2::t2 ->
      eq_tm h1 h2 &&
      eq_tm_list t1 t2
    | _ -> false

let rec eq_st_term (t1 t2:st_term) 
  : b:bool { b <==> (t1 == t2) }
  = match t1, t2 with
    | Tm_Return c1 use_eq1 t1, Tm_Return c2 use_eq2 t2 ->
      c1 = c2 &&
      use_eq1 = use_eq2 &&
      eq_tm t1 t2
      
    | Tm_Abs b1 o1 p1 t1 q1, Tm_Abs b2 o2 p2 t2 q2 ->
      eq_tm b1.binder_ty b2.binder_ty &&
      o1=o2 &&
      eq_tm_opt p1 p2 &&
      eq_st_term t1 t2 &&
      eq_tm_opt q1 q2
  
    | Tm_STApp h1 o1 t1, Tm_STApp h2 o2 t2 ->
      eq_tm h1 h2 &&
      o1=o2 &&
      eq_tm t1 t2

    | Tm_Bind b1 t1 k1, Tm_Bind b2 t2 k2 ->
      eq_tm b1.binder_ty b2.binder_ty &&
      eq_st_term t1 t2 &&
      eq_st_term k1 k2

    | Tm_TotBind t1 k1, Tm_TotBind t2 k2 ->
      eq_tm t1 t2 &&
      eq_st_term k1 k2
      
    | Tm_IntroExists b1 p1 l1, Tm_IntroExists b2 p2 l2 ->
      b1 = b2 &&
      eq_tm p1 p2 &&
      eq_tm_list l1 l2

    | Tm_ElimExists p1, Tm_ElimExists p2 ->
      eq_tm p1 p2

    | Tm_If g1 ethen1 eelse1 p1, Tm_If g2 ethen2 eelse2 p2 ->
      eq_tm g1 g2 &&
      eq_st_term ethen1 ethen2 &&
      eq_st_term eelse1 eelse2 &&
      eq_tm_opt p1 p2
    
    | Tm_While inv1 cond1 body1, Tm_While inv2 cond2 body2 ->
      eq_tm inv1 inv2 &&
      eq_st_term cond1 cond2 &&
      eq_st_term body1 body2

    | Tm_Par preL1 eL1 postL1 preR1 eR1 postR1,
      Tm_Par preL2 eL2 postL2 preR2 eR2 postR2 ->      
      eq_tm preL1 preL2 &&
      eq_st_term eL1 eL2 &&
      eq_tm postL1 postL2 &&
      eq_tm preR1 preR2 &&
      eq_st_term eR1 eR2 &&
      eq_tm postR1 postR2

    | Tm_WithLocal e1 e2, Tm_WithLocal e3 e4 ->
      eq_tm e1 e3 &&
      eq_st_term e2 e4

    | Tm_Rewrite	e1 e2, Tm_Rewrite e3 e4 ->
						eq_tm e1 e3 &&
						eq_tm e2 e4

    | Tm_Admit c1 u1 t1 post1, Tm_Admit c2 u2 t2 post2 ->
      c1 = c2 &&
      u1 = u2 &&
      eq_tm t1 t2 &&
      eq_tm_opt post1 post2

    | Tm_Protect t1, Tm_Protect t2 ->
      eq_st_term t1 t2
      
    | _ -> false
