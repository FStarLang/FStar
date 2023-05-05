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

(* locally nameless. *)
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


val eq_tm (t1 t2:term) 
  : b:bool { b <==> (t1 == t2) }

val eq_comp (c1 c2:comp) 
  : b:bool { b <==> (c1 == c2) }

val eq_st_comp (s1 s2:st_comp)  
  : b:bool { b <==> (s1 == s2) }

val eq_tm_opt (t1 t2:option term)
  : b:bool { b <==> (t1 == t2) }

val eq_tm_list (t1 t2:list term)
  : b:bool { b <==> (t1 == t2) }

val eq_st_term (t1 t2:st_term) 
  : b:bool { b <==> (t1 == t2) }

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

let nvar = ppname & var 
let v_as_nv x = RT.pp_name_default, x
let term_of_nvar (x:nvar) = Tm_Var { nm_ppname=fst x; nm_index=snd x; nm_range=FStar.Range.range_0}
let term_of_no_name_var (x:var) = term_of_nvar (v_as_nv x)

//// TEMPORARY : THEY SHOULD COME FROM FStar.Reflection.Typing.fsti WHEN THE BRANCHES STORM IS GONE ////
let equiv_abs (#g:R.env) (#e1 #e2:R.term) (ty:R.typ) (q:R.aqualv)
  (x:var{None? (RT.lookup_bvar g x)})
  (eq:RT.equiv (RT.extend_env g x ty)
               (RT.open_or_close_term' e1 (RT.open_with_var x) 0)
               (RT.open_or_close_term' e2 (RT.open_with_var x) 0))
  : RT.equiv g (RT.mk_abs ty q e1)
               (RT.mk_abs ty q e2) = admit ()

let equiv_arrow (#g:R.env) (#e1 #e2:R.term) (ty:R.typ) (q:R.aqualv)
  (x:var{None? (RT.lookup_bvar g x)})
  (eq:RT.equiv (RT.extend_env g x ty)
               (RT.open_or_close_term' e1 (RT.open_with_var x) 0)
               (RT.open_or_close_term' e2 (RT.open_with_var x) 0))
  : RT.equiv g (RT.mk_arrow ty q e1)
               (RT.mk_arrow ty q e2) = admit ()

let equiv_abs_close (#g:R.env) (#e1 #e2:R.term) (ty:R.typ) (q:R.aqualv)
  (x:var{None? (RT.lookup_bvar g x)})
  (eq:RT.equiv (RT.extend_env g x ty) e1 e2)
  : RT.equiv g (RT.mk_abs ty q (RT.open_or_close_term' e1 (RT.CloseVar x) 0))
               (RT.mk_abs ty q (RT.open_or_close_term' e2 (RT.CloseVar x) 0)) = admit ()
