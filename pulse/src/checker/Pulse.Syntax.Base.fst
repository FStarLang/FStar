(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Pulse.Syntax.Base
module RU = Pulse.RuntimeUtils
module R = FStar.Reflection.V2

let range_of_st_comp (st:st_comp) =
  RU.union_ranges (RU.range_of_term st.pre) (RU.range_of_term st.post)

let range_of_comp (c:comp) =
  match c with
  | C_Tot t -> RU.range_of_term t
  | C_ST st -> range_of_st_comp st
  | C_STAtomic _ _ st -> range_of_st_comp st
  | C_STGhost _ st -> range_of_st_comp st

let eq_univ (u1 u2:universe) : b:bool{b <==> u1 == u2} =
  let open FStar.Reflection.TermEq in
  assume (faithful_univ u1);
  assume (faithful_univ u2);
  univ_eq_dec u1 u2

let eq_tm (t1 t2:term) : Tot (b:bool { b <==> (t1 == t2) }) =  
  let open FStar.Reflection.TermEq in
  assume (faithful t1);
  assume (faithful t2);
  term_eq_dec t1 t2

let eq_st_comp (s1 s2:st_comp)  
  : b:bool { b <==> (s1 == s2) }
  = eq_univ s1.u s2.u &&
    eq_tm s1.res s2.res &&
    eq_tm s1.pre s2.pre &&
    eq_tm s1.post s2.post

let eq_comp (c1 c2:comp)
  : b:bool { b <==> (c1 == c2) }
  = match c1, c2 with
    | C_Tot t1, C_Tot t2 ->
      eq_tm t1 t2
    | C_ST s1, C_ST s2 ->
      eq_st_comp s1 s2
    | C_STAtomic i1 o1 s1, C_STAtomic i2 o2 s2 ->
      eq_tm i1 i2 &&
      o1 = o2 &&
      eq_st_comp s1 s2
    | C_STGhost i1 s1, C_STGhost i2 s2 ->
      eq_tm i1 i2 &&
      eq_st_comp s1 s2
    | _ -> false

let rec eq_list (f: (x:'a -> y:'a -> b:bool { b <==> (x == y)})) (l m:list 'a)
  : b:bool { b <==> (l == m) }
  = match l, m with
    | [], [] -> true
    | h1::t1, h2::t2 ->
      f h1 h2 &&
      eq_list f t1 t2
    | _ -> false

let eq_opt_dec (l m:option 'a) (f: (x:'a -> y:'a{x << l /\ y << m} -> b:bool { b <==> (x == y)}))
  : b:bool { b <==> (l == m) }
  = match l, m with
    | None, None -> true
    | Some l, Some m -> f l m
    | _ -> false

let eq_opt (f: (x:'a -> y:'a -> b:bool { b <==> (x == y)})) (l m:option 'a)
  : b:bool { b <==> (l == m) }
  = eq_opt_dec l m f

let eq_tm_opt (t1 t2:option term)
  : b:bool { b <==> (t1 == t2) }
  = eq_opt eq_tm t1 t2

let eq_comp_opt (c1 c2:option comp)
  : b:bool { b <==> (c1 == c2) }
  = eq_opt eq_comp c1 c2

let rec eq_list_dec top1 top2
   (f: (x:'a -> y:'a{x << top1 /\ y << top2} -> b:bool { b <==> (x == y)}))
   (l : list 'a{l << top1})
   (m : list 'a{m << top2})
  : b:bool { b <==> (l == m) }
  = match l, m with
    | [], [] -> true
    | h1::t1, h2::t2 ->
      f h1 h2 &&
      eq_list_dec top1 top2 f t1 t2
    | _ -> false

let eq_binder (b0 b1:binder) : b:bool { b <==> (b0 == b1) } =
  eq_tm b0.binder_ty b1.binder_ty

let eq_tm_list (t1 t2:list term) = eq_list eq_tm t1 t2

// wire to Reflection.TermEq
assume val fstar_const_eq : c1:R.vconst -> c2:R.vconst -> b:bool{b <==> (c1==c2)}

let rec sealed_list_eq #a (l1 l2 : list (Sealed.sealed a))
  : Lemma ((length l1 = length l2) ==> (l1 == l2))
  = match l1, l2 with
    | [], [] -> ()
    | h1::t1, h2::t2 ->
      Sealed.sealed_singl h1 h2;
      sealed_list_eq t1 t2
    | _ -> ()

let rec eq_pattern (p1 p2 : pattern) : b:bool{ b <==> (p1 == p2) } =
  match p1, p2 with
  | Pat_Cons f1 vs1,
    Pat_Cons f2 vs2 ->
    f1.fv_name = f2.fv_name &&
    eq_list_dec p1 p2 eq_sub_pat vs1 vs2

  | Pat_Constant c1, Pat_Constant c2 ->
    fstar_const_eq c1 c2

  | Pat_Var _ _, Pat_Var _ _ -> true
  
  | Pat_Dot_Term to1, Pat_Dot_Term to2 -> eq_opt eq_tm to1 to2

  | _ -> false

and eq_sub_pat (pb1 pb2 : pattern & bool) : b:bool{b <==> pb1 == pb2} =
  let (p1, b1) = pb1 in
  let (p2, b2) = pb2 in
  eq_pattern p1 p2 && b1 = b2

let eq_hint_type (ht1 ht2:proof_hint_type)
  : b:bool { b <==> (ht1 == ht2) }
  = match ht1, ht2 with
    | ASSERT { p=p1; elaborated=e1 }, ASSERT { p=p2; elaborated=e2 } ->
      eq_tm p1 p2 && e1 = e2
    | FOLD { names=ns1; p=p1}, FOLD { names=ns2; p=p2 }
    | UNFOLD { names=ns1; p=p1}, UNFOLD { names=ns2; p=p2 } ->
      eq_opt (eq_list (fun n1 n2 -> n1 = n2)) ns1 ns2 &&
      eq_tm p1 p2
    | RENAME { pairs=ps1; goal=p1; tac_opt=t1; elaborated=e1 }, RENAME { pairs=ps2; goal=p2; tac_opt=t2; elaborated=e2 } ->
      eq_list (fun (x1, y1) (x2, y2) -> eq_tm x1 x2 && eq_tm y1 y2) ps1 ps2 &&
      eq_opt eq_tm p1 p2 &&
      eq_tm_opt t1 t2 &&
      e1 = e2
    | REWRITE { t1; t2; tac_opt; elaborated=e1 }, REWRITE { t1=s1; t2=s2; tac_opt=tac_opt2; elaborated=e2 } ->
      eq_tm t1 s1 &&
      eq_tm t2 s2 &&
      eq_tm_opt tac_opt tac_opt2 &&
      e1 = e2
    | WILD, WILD
    | SHOW_PROOF_STATE _, SHOW_PROOF_STATE _ -> true
    | _ -> false

let eq_ascription (a1 a2:comp_ascription) 
 : b:bool { b <==> (a1 == a2) }
 = eq_comp_opt a1.elaborated a2.elaborated &&
   eq_comp_opt a1.annotated a2.annotated


let rec eq_st_term (t1 t2:st_term) 
  : b:bool { b <==> (t1 == t2) }
  = match t1.term, t2.term with
    | Tm_Return {expected_type=ty1; insert_eq=b1; term=t1}, 
      Tm_Return {expected_type=ty2; insert_eq=b2; term=t2} ->
      eq_tm ty1 ty2 &&
      b1 = b2 &&
      eq_tm t1 t2

    | Tm_Abs { b=b1; q=q1; ascription=c1; body=t1 },
      Tm_Abs { b=b2; q=q2; ascription=c2; body=t2 } ->
      eq_tm b1.binder_ty b2.binder_ty &&
      eq_opt_dec q1 q2 eq_aqual &&
      eq_ascription c1 c2 &&
      eq_st_term t1 t2
  
    | Tm_ST { t=tm1; args=a1 }, Tm_ST { t=tm2; args=a2 } ->
      eq_tm tm1 tm2 && eq_list_dec t1 t2 eq_st_term a1 a2
      
    | Tm_Bind { binder=b1; head=t1; body=k1 },
      Tm_Bind { binder=b2; head=t2; body=k2 } ->
      eq_tm b1.binder_ty b2.binder_ty &&
      eq_st_term t1 t2 &&
      eq_st_term k1 k2

    | Tm_TotBind { binder=b1; head=t1; body=k1 },
      Tm_TotBind { binder=b2; head=t2; body=k2 } ->
      eq_tm b1.binder_ty b2.binder_ty &&
      eq_tm t1 t2 &&
      eq_st_term k1 k2
      
    | Tm_IntroPure { p=p1 }, Tm_IntroPure { p=p2 } ->
      eq_tm p1 p2

    | Tm_IntroExists { p=p1; witnesses=l1 },
      Tm_IntroExists { p=p2; witnesses=l2 } ->
      eq_tm p1 p2 &&
      eq_tm_list l1 l2

    | Tm_ElimExists {p=p1},
      Tm_ElimExists {p=p2} ->
      eq_tm p1 p2

    | Tm_If { b=g1; then_=ethen1; else_=eelse1; post=p1},
      Tm_If { b=g2; then_=ethen2; else_=eelse2; post=p2} ->
      eq_tm g1 g2 &&
      eq_st_term ethen1 ethen2 &&
      eq_st_term eelse1 eelse2 &&
      eq_tm_opt p1 p2
    
    | Tm_Match {sc=sc1; returns_=r1; brs=br1},
      Tm_Match {sc=sc2; returns_=r2; brs=br2} ->
      eq_tm sc1 sc2 &&
      eq_tm_opt r1 r2 &&
      eq_list_dec t1 t2 eq_branch br1 br2

    | Tm_While { invariant=inv1; condition=cond1; body=body1 },
      Tm_While { invariant=inv2; condition=cond2; body=body2 } ->
      eq_tm inv1 inv2 &&
      eq_st_term cond1 cond2 &&
      eq_st_term body1 body2

    | Tm_NuWhile { invariant=inv1; condition=cond1; body=body1 },
      Tm_NuWhile { invariant=inv2; condition=cond2; body=body2 } ->
      eq_tm inv1 inv2 &&
      eq_st_term cond1 cond2 &&
      eq_st_term body1 body2

    | Tm_Par {pre1=preL1; body1=eL1; post1=postL1; pre2=preR1; body2=eR1; post2=postR1 },
      Tm_Par {pre1=preL2; body1=eL2; post1=postL2; pre2=preR2; body2=eR2; post2=postR2 } ->
      eq_tm preL1 preL2 &&
      eq_st_term eL1 eL2 &&
      eq_tm postL1 postL2 &&
      eq_tm preR1 preR2 &&
      eq_st_term eR1 eR2 &&
      eq_tm postR1 postR2

    | Tm_WithLocal { binder=x1; initializer=e1; body=b1 },
      Tm_WithLocal { binder=x2; initializer=e2; body=b2 } ->
      eq_tm x1.binder_ty x2.binder_ty &&
      eq_tm e1 e2 &&
      eq_st_term b1 b2

    | Tm_WithLocalArray { binder=x1; initializer=e1; length=n1; body=b1 },
      Tm_WithLocalArray { binder=x2; initializer=e2; length=n2; body=b2 } ->
      eq_tm x1.binder_ty x2.binder_ty &&
      eq_tm e1 e2 &&
      eq_tm n1 n2 &&
      eq_st_term b1 b2

    | Tm_Rewrite { t1=l1; t2=r1; tac_opt=tac1; elaborated=e1 },
      Tm_Rewrite { t1=l2; t2=r2; tac_opt=tac2; elaborated=e2 } ->
      eq_tm l1 l2 &&
      eq_tm r1 r2 &&
      eq_tm_opt tac1 tac2 &&
      e1 = e2

    | Tm_Admit { ctag=c1; u=u1; typ=t1; post=post1 }, 
      Tm_Admit { ctag=c2; u=u2; typ=t2; post=post2 } ->
      c1 = c2 &&
      eq_univ u1 u2 &&
      eq_tm t1 t2 &&
      eq_tm_opt post1 post2
      
    | Tm_Unreachable {c=c1},
      Tm_Unreachable {c=c2} ->
      eq_comp c1 c2
    
    | Tm_ProofHintWithBinders { hint_type=ht1; binders=bs1; t=t1 },
      Tm_ProofHintWithBinders { hint_type=ht2; binders=bs2; t=t2 } ->
      eq_hint_type ht1 ht2 &&
      eq_list eq_binder bs1 bs2 &&
      eq_st_term t1 t2

    | Tm_WithInv {name=name1; returns_inv=r1; body=body1},
      Tm_WithInv {name=name2; returns_inv=r2; body=body2} ->
      eq_tm name1 name2 &&
      eq_opt (fun (b1, r1, is1) (b2, r2, is2) ->
              eq_tm b1.binder_ty b2.binder_ty &&
              eq_tm r1 r2 &&
              eq_tm is1 is2) r1 r2
             &&
      eq_st_term body1 body2

    | Tm_PragmaWithOptions { options=o1; body=b1 }, 
      Tm_PragmaWithOptions { options=o2; body=b2 } ->
      o1 = o2 && eq_st_term b1 b2
      
    | _ -> false

and eq_branch (b1 b2 : branch)
  : b:bool{b <==> (b1 == b2)}
  = eq_pattern b1.pat b2.pat &&
    eq_st_term b1.e   b2.e

and eq_aqual (q1 q2 : qualifier) : b:bool{b <==> (q1 == q2)} =
  match q1, q2 with
  | Implicit, Implicit
  | TcArg, TcArg -> true
  | Meta t1, Meta t2 -> eq_tm t1 t2
  | _ -> false
