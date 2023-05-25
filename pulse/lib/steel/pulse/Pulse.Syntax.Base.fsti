module Pulse.Syntax.Base
module RTB = FStar.Reflection.Typing.Builtins
module RT = FStar.Reflection.Typing
module R = FStar.Reflection
open FStar.List.Tot

module T = FStar.Tactics

type constant = R.vconst

let var = nat
let index = nat

type universe = R.universe

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
  | Tm_Emp        : term
  | Tm_Pure       : p:term -> term
  | Tm_Star       : l:vprop -> r:vprop -> term
  | Tm_ExistsSL   : u:universe -> t:term -> body:vprop -> should_elim:should_elim_t -> term
  | Tm_ForallSL   : u:universe -> t:term -> body:vprop -> term
  | Tm_VProp      : term
  | Tm_Inames     : term  // type inames
  | Tm_EmpInames  : term
  | Tm_FStar      : host_term -> range -> term
  | Tm_Unknown    : term

and vprop = term

noeq
type binder = {
  binder_ty     : term;
  binder_ppname : ppname;
}

noeq
type st_comp = { (* ST pre (x:res) post ... x is free in post *)
  u:universe;
  res:term;
  pre:vprop;
  post:vprop
}

noeq
type comp =
  | C_Tot      : term -> comp
  | C_ST       : st_comp -> comp
  | C_STAtomic : term -> st_comp -> comp  // inames
  | C_STGhost  : term -> st_comp -> comp  // inames


let comp_st = c:comp {not (C_Tot? c) }

type ctag =
  | STT
  | STT_Atomic
  | STT_Ghost

(* terms with STT types *)
[@@ no_auto_projectors]
noeq
type st_term' =
  | Tm_Return { 
      ctag:ctag;
      insert_eq:bool;
      term: term;
    }
  | Tm_Abs {
      b:binder;
      q:option qualifier;
      pre:option vprop;
      body:st_term;
      ret_ty:option term;
      post:option vprop;
    }
  | Tm_STApp {
      head:term;
      arg_qual:option qualifier;
      arg:term;
    }
  | Tm_Bind { 
      binder:binder;
      head:st_term;
      body:st_term;
    }
  | Tm_TotBind {
      head:term;
      body:st_term;
    } 
  | Tm_If {
      b:term;
      then_:st_term;
      else_:st_term;
      post:option vprop;
    }
  | Tm_ElimExists {
      p:vprop;
    }
  | Tm_IntroExists {
      erased:bool;
      p:vprop;
      witnesses:list term;
    }
  | Tm_While {
      invariant:term;
      condition:st_term;
      body:st_term;
    }
  | Tm_Par {
      pre1:term;
      body1:st_term;
      post1:term;
      pre2:term;
      body2:st_term;
      post2:term;
    }  
  | Tm_WithLocal {
      initializer:term;
      body:st_term;
    }
  | Tm_Rewrite {
      t1:term;
      t2:term;
    } 
  | Tm_Admit {
      ctag:ctag;
      u:universe;
      typ:term;
      post:option term;
    }
  | Tm_Protect {
      //Wrap a term to indicate that no proof-automation heuristics should be applied
      t:st_term;
    }

and st_term = {
    term : st_term';
    range : range
} 

let null_binder (t:term) : binder =
  {binder_ty=t;binder_ppname=RT.pp_name_default}

let mk_binder (s:string) (t:term) : binder =
  {binder_ty=t;binder_ppname=RT.seal_pp_name s}

val eq_univ (u1 u2:universe)
  : b:bool { b <==> (u1 == u2) }

val eq_tm (t1 t2:term) 
  : b:bool { b <==> (t1 == t2) }

val eq_st_comp (s1 s2:st_comp)  
  : b:bool { b <==> (s1 == s2) }

val eq_comp (c1 c2:comp) 
  : b:bool { b <==> (c1 == c2) }

val eq_tm_opt (t1 t2:option term)
  : b:bool { b <==> (t1 == t2) }

val eq_tm_list (t1 t2:list term)
  : b:bool { b <==> (t1 == t2) }

val eq_st_term (t1 t2:st_term) 
  : b:bool { b <==> (t1 == t2) }

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
