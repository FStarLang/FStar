module Pulse.Syntax
module RTB = FStar.Reflection.Typing.Builtins
module RT = FStar.Reflection.Typing
module R = FStar.Reflection
open FStar.List.Tot
module T = FStar.Tactics

type constant =
  | Unit
  | Bool of bool
  | Int of int

let var = nat
let index = nat

type universe = 
  | U_zero
  | U_succ of universe
  | U_var of string
  | U_max : universe -> universe -> universe
  | U_unknown

(* locally nameless.
   term is currently an eqtype. That makes some experiments a bit easier.
   but it doesn't have to be. 
   
   if we include Embed it won't be.
   So, we should remove reliance on this thing being an eqtype soon.
   But, adding a Tm_Embed poses some other difficulties too, 
   
     e.g., opening/closing a term with embedded terms in it becomes
           problematic since that makes opening/closing mutually
           recursive with elaboration
*)

let ppname = RT.pp_name_t

let range_singleton_trigger (r:FStar.Range.range) = True
let range = r:FStar.Range.range { range_singleton_trigger r }
let range_singleton (r:FStar.Range.range)
  : Lemma 
    (ensures r == FStar.Range.range_0)
    [SMTPat (range_singleton_trigger r)]
  = FStar.Sealed.sealed_singl r FStar.Range.range_0


noeq
type bv = {
  bv_index  : index;
  bv_ppname : ppname;
  bv_range  : range;
}

noeq
type nm = {
  nm_index  : var;
  nm_ppname : ppname;
  nm_range  : range;
}

type qualifier =
  | Implicit

let should_elim_t = FStar.Sealed.Inhabited.sealed false
let should_elim_true : should_elim_t = FStar.Sealed.Inhabited.seal true
let should_elim_false : should_elim_t = FStar.Sealed.Inhabited.seal false

noeq
type fv = {
  fv_name : R.name;
  fv_range : range;
}
let as_fv l = { fv_name = l; fv_range = FStar.Range.range_0 }

let not_tv_unknown (t:R.term) = R.inspect_ln t =!= R.Tv_Unknown
let host_term = t:R.term { not_tv_unknown t }
let host_term_equality (t1 t2:host_term)
  : Lemma
    (ensures R.term_eq t1 t2 <==> t1==t2)
  = admit()

[@@ no_auto_projectors]
noeq
type term =
  | Tm_BVar       : bv -> term
  | Tm_Var        : nm -> term
  | Tm_FVar       : l:fv -> term
  | Tm_UInst      : l:fv -> us:list universe -> term
  | Tm_Constant   : c:constant -> term
  | Tm_Refine     : b:binder -> term -> term
  | Tm_PureApp    : head:term -> arg_qual:option qualifier -> arg:term -> term
  | Tm_Let        : t:term -> e1:term -> e2:term -> term  
  | Tm_Emp        : term
  | Tm_Pure       : p:term -> term
  | Tm_Star       : l:vprop -> r:vprop -> term
  | Tm_ExistsSL   : u:universe -> t:term -> body:vprop -> should_elim:should_elim_t -> term
  | Tm_ForallSL   : u:universe -> t:term -> body:vprop -> term
  | Tm_Arrow      : b:binder -> q:option qualifier -> body:comp -> term 
  | Tm_Type       : universe -> term
  | Tm_VProp      : term
  | Tm_Inames     : term  // type inames
  | Tm_EmpInames  : term
  | Tm_UVar       : int -> term
  | Tm_FStar      : host_term -> term
  | Tm_Unknown    : term


and binder = {
  binder_ty     : term;
  binder_ppname : ppname;
}

and comp =
  | C_Tot      : term -> comp
  | C_ST       : st_comp -> comp
  | C_STAtomic : term -> st_comp -> comp  // inames
  | C_STGhost  : term -> st_comp -> comp  // inames

and st_comp = { (* ST pre (x:res) post ... x is free in post *)
  u:universe;
  res:term;
  pre:vprop;
  post:vprop
}

and vprop = term

let comp_st = c:comp {not (C_Tot? c) }

type ctag =
  | STT
  | STT_Atomic
  | STT_Ghost

(* terms with STT types *)
[@@ no_auto_projectors]
noeq
type st_term =
  | Tm_Return     : ctag -> bool -> term -> st_term  // bool is whether insert equality in the post
  | Tm_Abs        : b:binder -> q:option qualifier -> pre:option vprop -> body:st_term -> post:option vprop -> st_term
  | Tm_STApp      : head:term -> arg_qual:option qualifier -> arg:term -> st_term  
  | Tm_Bind       : e1:st_term -> e2:st_term -> st_term
  | Tm_If         : b:term -> then_:st_term -> else_:st_term -> post:option vprop -> st_term
  | Tm_ElimExists : vprop -> st_term
  | Tm_IntroExists: erased:bool -> vprop -> witnesses:list term -> st_term
  | Tm_While      : term -> st_term -> st_term -> st_term  // inv, cond, body
  | Tm_Par        : term -> st_term -> term -> term -> st_term -> term -> st_term  // (pre, e, post) for left and right computations
  | Tm_WithLocal  : term -> st_term -> st_term  // initial value of the local, continuation

  | Tm_Rewrite    : term -> term -> st_term
  | Tm_Admit      : ctag -> universe -> term -> option term -> st_term  // u, a:type_u, optional post
  | Tm_Protect    : st_term -> st_term //Wrap a term to indicate that no proof-automation heuristics should be applied 

let null_binder (t:term) : binder =
  {binder_ty=t;binder_ppname=RT.pp_name_default}

let mk_binder (s:string) (t:term) : binder =
  {binder_ty=t;binder_ppname=RT.seal_pp_name s}

let mk_bvar (s:string) (r:Range.range) (i:index) : term =
  Tm_BVar {bv_index=i;bv_ppname=RT.seal_pp_name s;bv_range=r}

let null_var (v:var) : term = Tm_Var {nm_index=v;nm_ppname=RT.pp_name_default;nm_range=Range.range_0}

let null_bvar (i:index) : term = Tm_BVar {bv_index=i;bv_ppname=RT.pp_name_default;bv_range=Range.range_0}

let gen_uvar (t:term) : T.Tac term =
  Tm_UVar (T.fresh ())

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

    | Tm_Bind t1 k1, Tm_Bind t2 k2 ->
      eq_st_term t1 t2 &&
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

let rec leftmost_head_and_args (t:term) : term & list (option qualifier & term) =
  match t with
  | Tm_PureApp hd q arg ->
    let hd, args = leftmost_head_and_args hd in
    hd, args@[q, arg]
  | _ -> t, []


let comp_res (c:comp) : term =
  match c with
  | C_Tot ty -> ty
  | C_ST s
  | C_STAtomic _ s
  | C_STGhost _ s -> s.res

let stateful_comp (c:comp) =
  C_ST? c || C_STAtomic? c || C_STGhost? c

let st_comp_of_comp (c:comp{stateful_comp c}) : st_comp =
  match c with
  | C_ST s
  | C_STAtomic _ s
  | C_STGhost _ s -> s

let with_st_comp (c:comp{stateful_comp c}) (s:st_comp) : comp =
  match c with
  | C_ST _ -> C_ST s
  | C_STAtomic inames _ -> C_STAtomic inames s
  | C_STGhost inames _ -> C_STGhost inames s

let comp_u (c:comp { stateful_comp c }) =
  match c with
  | C_ST s
  | C_STAtomic _ s
  | C_STGhost _ s -> s.u

let comp_pre (c:comp { stateful_comp c }) =
  match c with
  | C_ST s
  | C_STAtomic _ s
  | C_STGhost _ s -> s.pre

let comp_post (c:comp { stateful_comp c }) =
  match c with
  | C_ST s
  | C_STAtomic _ s
  | C_STGhost _ s -> s.post

let comp_inames (c:comp { C_STAtomic? c \/ C_STGhost? c }) : term =
  match c with
  | C_STAtomic inames _
  | C_STGhost inames _ -> inames

let term_of_var (x:var) = Tm_Var { nm_ppname=RT.pp_name_default; nm_index=x; nm_range=FStar.Range.range_0}