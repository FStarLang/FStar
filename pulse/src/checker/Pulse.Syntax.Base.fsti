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
module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module T = FStar.Tactics.V2
open FStar.List.Tot

let allow_invert (#a:Type) (x:a) : Lemma (inversion a) = allow_inversion a

type constant = R.vconst

let var = nat
let index = nat

type universe = R.universe

(* locally nameless. *)
let range_singleton_trigger (r:FStar.Range.range) = True
let range = r:FStar.Range.range { range_singleton_trigger r }
let range_singleton (r:FStar.Range.range)
  : Lemma 
    (ensures r == FStar.Range.range_0)
    [SMTPat (range_singleton_trigger r)]
  = FStar.Sealed.sealed_singl r FStar.Range.range_0

noeq
type ppname0 = {
  name : RT.pp_name_t;
  range : range
}

let ppname_default =  {
    // This used to be "_", but that is a *null binder* and behaves very magically
    name = FStar.Sealed.seal "__";
    range = FStar.Range.range_0
}

let ppname_singleton_trigger (r:ppname0) = True
let ppname_singleton (x:ppname0)
  : Lemma 
    (ensures x == ppname_default)
    [SMTPat (ppname_singleton_trigger x)]
  = FStar.Sealed.sealed_singl x.name ppname_default.name
let ppname = p:ppname0 { ppname_singleton_trigger p }
let mk_ppname (name:RT.pp_name_t) (range:FStar.Range.range) : ppname = {
    name = name;
    range = range
}

let mk_ppname_no_range (s:string) : ppname = {
  name = FStar.Sealed.seal s;
  range = FStar.Range.range_0;
}

noeq
type bv = {
  bv_index  : index;
  bv_ppname : ppname;
}

noeq
type nm = {
  nm_index  : var;
  nm_ppname : ppname;
}

noeq
type qualifier =
  | Implicit
  | TcArg
  | Meta of R.term

noeq
type fv = {
  fv_name : R.name;
  fv_range : range;
}
let as_fv l = { fv_name = l; fv_range = FStar.Range.range_0 }

type term = R.term
type slprop = term
type typ = term

noeq
type binder = {
  binder_ty     : term;
  binder_ppname : ppname;
  binder_attrs  : FStar.Sealed.Inhabited.sealed #(list term) []
}

noeq
type st_comp = { (* ST pre (x:res) post ... x is free in post *)
  u:universe;
  res:term;
  pre:slprop;
  post:slprop
}

type observability =
  | Neutral
  | Observable

noeq
type comp =
  | C_Tot      : term -> comp
  | C_ST       : st_comp -> comp
  | C_STAtomic : inames:term -> obs:observability -> st_comp -> comp
  | C_STGhost  : inames:term -> st_comp -> comp

val range_of_st_comp (st:st_comp) : R.range
val range_of_comp (c:comp) : R.range


let stateful_comp (c:comp) = not (C_Tot? c)
let comp_st = c:comp { stateful_comp c }

noeq
type pattern =
  | Pat_Cons     : fv -> list (pattern & bool) -> pattern
  | Pat_Constant : constant -> pattern
  | Pat_Var      : RT.pp_name_t -> ty:RT.sort_t -> pattern
  | Pat_Dot_Term : option term -> pattern

type ctag =
  | STT
  | STT_Atomic
  | STT_Ghost

let effect_hint = FStar.Sealed.Inhabited.sealed #(option ctag) None
let default_effect_hint : effect_hint = FStar.Sealed.seal None
let as_effect_hint (c:ctag) : effect_hint = FStar.Sealed.seal (Some c)

let ctag_of_comp_st (c:comp_st) : ctag =
  match c with
  | C_ST _ -> STT
  | C_STAtomic _ _ _ -> STT_Atomic
  | C_STGhost _ _ -> STT_Ghost

noeq
type effect_annot =
  | EffectAnnotSTT
  | EffectAnnotGhost { opens:term }
  | EffectAnnotAtomic { opens:term }
  | EffectAnnotAtomicOrGhost { opens:term }

let effect_annot_of_comp (c:comp_st)
: effect_annot
= match c with
  | C_ST _ -> EffectAnnotSTT
  | C_STGhost opens _ -> EffectAnnotGhost { opens }
  | C_STAtomic opens _ _ -> EffectAnnotAtomic { opens }

let ctag_of_effect_annot (x:effect_annot) : option ctag =
  match x with
  | EffectAnnotSTT -> Some STT
  | EffectAnnotGhost _ -> Some STT_Ghost
  | EffectAnnotAtomic _ -> Some STT_Atomic
  | EffectAnnotAtomicOrGhost _ -> None

noeq
type proof_hint_type =
  | ASSERT {
      p:slprop;
      elaborated: bool; (* internally created by the checker, don't purify *)
    }
  | FOLD { 
      names:option (list string);
      p:slprop;
    }
  | UNFOLD {
      names:option (list string);
      p:slprop
    }
  | RENAME { //rename e as e' [in p]
      pairs:list (term & term);
      goal: option term;
      tac_opt : option term; (* optional tactic *)
      elaborated: bool; (* internally created by the checker, don't purify *)
    }
  | REWRITE {
      t1:slprop;
      t2:slprop;
      tac_opt : option term; (* optional tactic *)
      elaborated: bool; (* internally created by the checker, don't purify *)
    }
    (* NB: A REWRITE proof hint will elaborate to a Tm_Rewrite
    after solving all of the binders (if any). Tm_Rewrite is what
    really changes the context. *)
  | WILD //with p q r. _
  | SHOW_PROOF_STATE of range //print the proof state and exit

noeq
type comp_ascription = {
  annotated:option comp;
  elaborated:option comp
}
let empty_ascription = { annotated=None; elaborated=None }  

(* terms with STT types *)
[@@ no_auto_projectors]
noeq
type st_term' =
  | Tm_Return { 
      expected_type:term;
      insert_eq:bool;
      term: term;
    }
  | Tm_Abs {
      b:binder;
      q:option qualifier;
      ascription: comp_ascription;
      body:st_term;
    }    
  | Tm_ST { //promote a pure term with an stt/stt_ghost/stt_atomic type to an st_term
      t:term;
      args:list st_term;
    }
  | Tm_Bind { 
      binder:binder;
      head:st_term;
      body:st_term;
    }
  | Tm_TotBind {  // tot here means non-stateful, head could also be ghost, we should rename it
      binder:binder;
      head:term;
      body:st_term;
    }
  | Tm_If {
      b:term;
      then_:st_term;
      else_:st_term;
      post:option slprop;
    }
  | Tm_Match {
      sc:term;
      returns_:option slprop;
      brs: list branch;
    }
  | Tm_IntroPure {
      p:term;
    }
  | Tm_ElimExists {
      p:slprop;
    }
  | Tm_IntroExists {
      p:slprop;
      witnesses:list term;
    }
  | Tm_While {
      invariant:term;
      condition:st_term;
      condition_var:ppname;
      body:st_term;
    }
   | Tm_NuWhile {
      invariant:term;
      condition:st_term;
      body:st_term;
    }
  | Tm_WithLocal {
      binder:binder;
      initializer:option term;
      body:st_term;
    }
  | Tm_WithLocalArray {
      binder:binder;
      initializer:option term;
      length:term;
      body:st_term;
    }
  | Tm_Rewrite {
      t1:term;
      t2:term;
      tac_opt : option term;
      elaborated: bool; (* internally created by the checker, don't purify *)
    } 
  | Tm_Admit {
      ctag:ctag;
      u:universe;
      typ:term;
      post:option term;
    }
  | Tm_Unreachable {
      c: comp;
    }
  | Tm_ProofHintWithBinders {
      hint_type:proof_hint_type;
      binders:list binder;
      t:st_term
  }
  | Tm_PragmaWithOptions {
      options: string;
      body: st_term
    }
  | Tm_ForwardJumpLabel {
      lbl: ppname;
      body: st_term;
      post: comp_st; // pre & post condition for the whole block, not the goto
    }
  | Tm_Goto {
      lbl: term; // either var or named
      arg: term;
    }
and st_term = {
    term : st_term';
    range : range;
    effect_tag: effect_hint;
    source : Sealed.Inhabited.sealed #bool false; (* was this term in the user-written source code? false for anything generated by the checker. *)
    seq_lhs : Sealed.Inhabited.sealed #bool false; (* was this s1; ..? if so check that it types to unit *)
} 

and branch = {
  pat : pattern;
  e : st_term;
  norw: Sealed.Inhabited.sealed false; (* do not automatically rewrite strutinee to the pattern. *)
}

(* Create a term with default fields *)
let mk_term (s : st_term') (r : range) : st_term =
  { term = s;
    range = r;
    effect_tag = default_effect_hint;
    source = FStar.Sealed.seal false;
    seq_lhs = FStar.Sealed.seal false;
  }

noeq
type fn_defn = {
  (* A function definition. This will be mostly checked as a nested
  Tm_Abs with bs and body, especially if non-recursive. *)
  id : R.ident;
  isrec : bool;
  us : list R.univ_name;
  bs : list (option qualifier & binder & bv);
  comp : comp; (* bs in scope *)
  meas : (meas:option term{Some? meas ==> isrec}); (* bs in scope *)
  body : st_term; (* bs in scope *)
}

noeq
type fn_decl = {
  (* A function declaration, without a body. *)
  id : R.ident;
  us : list R.univ_name;
  bs : list (option qualifier & binder & bv);
  comp : comp_st; (* bs in scope *)
}

noeq
type decl' =
  | FnDefn of fn_defn
  | FnDecl of fn_decl

and decl = {
  d : decl';
  range : range;
}

let mk_binder_with_attrs (binder_ty:term) (binder_ppname:ppname) binder_attrs : binder =
  {binder_ty;binder_ppname;binder_attrs}

let binder_attrs_default = FStar.Sealed.seal []

let null_binder (t:term) : binder =
  mk_binder_with_attrs t ppname_default binder_attrs_default

let mk_binder (s:string) (r:range) (t:term) : binder =
  mk_binder_with_attrs t (mk_ppname (RT.seal_pp_name s) r) binder_attrs_default

let mk_binder_ppname (binder_ty:term) (binder_ppname:ppname) : binder =
  mk_binder_with_attrs binder_ty binder_ppname binder_attrs_default

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
  | C_STAtomic _ _ s
  | C_STGhost _ s -> s.res

let st_comp_of_comp (c:comp_st) : st_comp =
  match c with
  | C_ST s
  | C_STAtomic _ _ s
  | C_STGhost _ s -> s

let with_st_comp (c:comp_st) (s:st_comp) : comp =
  match c with
  | C_ST _ -> C_ST s
  | C_STAtomic inames obs _ -> C_STAtomic inames obs s
  | C_STGhost inames _ -> C_STGhost inames s

let comp_u (c:comp_st) = (st_comp_of_comp c).u

let universe_of_comp (c:comp_st) =
  match c with
  | C_ST _ -> RT.u_zero
  | _ -> Pulse.Reflection.Util.u_atomic_ghost (comp_u c)

let comp_pre (c:comp { stateful_comp c }) = (st_comp_of_comp c).pre

let comp_post (c:comp { stateful_comp c }) = (st_comp_of_comp c).post

let comp_inames (c:comp { C_STAtomic? c || C_STGhost? c }) : term =
  match c with
  | C_STGhost inames _
  | C_STAtomic inames _ _ -> inames

let nvar = ppname & var 
let v_as_nv x : nvar = ppname_default, x
let as_binder (t:term) = null_binder t

let ppname_for_uvar (p : ppname) : T.Tac ppname =
  {
    p with name = T.seal ("?" ^ T.unseal p.name);
  }

