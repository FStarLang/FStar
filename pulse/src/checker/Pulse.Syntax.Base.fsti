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
module RTB = FStar.Reflection.Typing.Builtins
module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module RU = Pulse.RuntimeUtils
module T = FStar.Tactics.V2
open FStar.List.Tot

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
type ppname = {
  name : RT.pp_name_t;
  range : range
}

let ppname_default =  {
    name = FStar.Sealed.seal "_";
    range = FStar.Range.range_0
}

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

type qualifier =
  | Implicit


noeq
type fv = {
  fv_name : R.name;
  fv_range : range;
}
let as_fv l = { fv_name = l; fv_range = FStar.Range.range_0 }

type term = R.term
type vprop = term
type typ = term

noeq
type binder = {
  binder_ty     : term;
  binder_ppname : ppname;
  binder_attrs  : FStar.Sealed.Inhabited.sealed #(list term) []
}

[@@ no_auto_projectors]
noeq
type term_view =
  | Tm_Emp        : term_view
  | Tm_Pure       : p:term -> term_view
  | Tm_Star       : l:vprop -> r:vprop -> term_view
  | Tm_ExistsSL   : u:universe -> b:binder -> body:vprop -> term_view
  | Tm_ForallSL   : u:universe -> b:binder -> body:vprop -> term_view
  | Tm_VProp      : term_view
  | Tm_Inv        : vprop -> term_view
  | Tm_Inames     : term_view  // type inames
  | Tm_EmpInames  : term_view
  | Tm_AddInv     : i:term -> is:term -> term_view
  | Tm_Unknown    : term_view

open Pulse.Reflection.Util

let pack_term_view (top:term_view) (r:range)
  : term
  = let open R in
    let w t' = RU.set_range t' r in
    match top with
    | Tm_VProp ->
      w (pack_ln (Tv_FVar (pack_fv vprop_lid)))

    | Tm_Emp ->
      w (pack_ln (Tv_FVar (pack_fv emp_lid)))
      
    | Tm_Inv p ->
      let head = pack_ln (Tv_FVar (pack_fv inv_lid)) in
      w (pack_ln (Tv_App head (p, Q_Explicit)))

    | Tm_Pure p ->
      let head = pack_ln (Tv_FVar (pack_fv pure_lid)) in
      w (pack_ln (Tv_App head (p, Q_Explicit)))

    | Tm_Star l r ->
      w (mk_star l r)
      
    | Tm_ExistsSL u b body
    | Tm_ForallSL u b body ->
      let t = set_range_of b.binder_ty b.binder_ppname.range in
      if Tm_ExistsSL? top
      then w (mk_exists u t (mk_abs_with_name_and_range b.binder_ppname.name b.binder_ppname.range t R.Q_Explicit body))
      else w (mk_forall u t (mk_abs_with_name_and_range b.binder_ppname.name b.binder_ppname.range t R.Q_Explicit body))

    | Tm_Inames ->
      w (pack_ln (Tv_FVar (pack_fv inames_lid)))

    | Tm_EmpInames ->
      w (emp_inames_tm)

    | Tm_AddInv i is ->
      w (add_inv_tm (`_) is i) // Careful on the order flip

    | Tm_Unknown ->
      w (pack_ln R.Tv_Unknown)

let binder_attrs_default = FStar.Sealed.seal []

let term_range (t:term) = RU.range_of_term t
let tm_fstar (t:term) (r:range) : term = RU.set_range t r
let with_range (t:term_view) (r:range) = pack_term_view t r
let tm_vprop = with_range Tm_VProp FStar.Range.range_0
let tm_inv p = with_range (Tm_Inv p) FStar.Range.range_0
let tm_inames = with_range Tm_Inames FStar.Range.range_0
let tm_emp = with_range Tm_Emp FStar.Range.range_0
let tm_emp_inames = with_range Tm_EmpInames FStar.Range.range_0
let tm_unknown = with_range Tm_Unknown FStar.Range.range_0
let tm_pure (p:term) : term = pack_term_view (Tm_Pure p) (RU.range_of_term p)
let tm_star (l:vprop) (r:vprop) : term =
  pack_term_view (Tm_Star l r)
                 (RU.union_ranges (RU.range_of_term l) (RU.range_of_term r))
let tm_exists_sl (u:universe) (b:binder) (body:vprop) : term =
  pack_term_view (Tm_ExistsSL u b body)
                 (RU.union_ranges (RU.range_of_term b.binder_ty) (RU.range_of_term body))
let tm_forall_sl (u:universe) (b:binder) (body:vprop) : term =
  pack_term_view (Tm_ForallSL u b body)
                 (RU.union_ranges (RU.range_of_term b.binder_ty) (RU.range_of_term body))

noeq
type st_comp = { (* ST pre (x:res) post ... x is free in post *)
  u:universe;
  res:term;
  pre:vprop;
  post:vprop
}

type observability =
  | Neutral
  | Observable
  | Unobservable

noeq
type comp =
  | C_Tot      : term -> comp
  | C_ST       : st_comp -> comp
  | C_STAtomic : inames:term -> obs:observability -> st_comp -> comp
  | C_STGhost  : st_comp -> comp


let comp_st = c:comp {not (C_Tot? c) }

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
  | C_STGhost _ -> STT_Ghost

noeq
type effect_annot =
  | EffectAnnotSTT
  | EffectAnnotGhost
  | EffectAnnotAtomic { opens:term }

let effect_annot_of_comp (c:comp_st)
: effect_annot
= match c with
  | C_ST _ -> EffectAnnotSTT
  | C_STGhost _ -> EffectAnnotGhost
  | C_STAtomic opens _ _ -> EffectAnnotAtomic { opens }

let ctag_of_effect_annot =
  function
  | EffectAnnotSTT -> STT
  | EffectAnnotGhost -> STT_Ghost
  | _ -> STT_Atomic

noeq
type proof_hint_type =
  | ASSERT {
      p:vprop
    }
  | FOLD { 
      names:option (list string);
      p:vprop;
    }
  | UNFOLD {
      names:option (list string);
      p:vprop
    }
  | RENAME { //rename e as e' [in p]
      pairs:list (term & term);
      goal: option term
    }
  | REWRITE {
      t1:vprop;
      t2:vprop;
    }
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
  | Tm_TotBind {  // tot here means non-stateful, head could also be ghost, we should rename it
      binder:binder;
      head:term;
      body:st_term;
    }
  | Tm_If {
      b:term;
      then_:st_term;
      else_:st_term;
      post:option vprop;
    }
  | Tm_Match {
      sc:term;
      returns_:option vprop;
      brs: list branch;
    }
  | Tm_IntroPure {
      p:term;
    }
  | Tm_ElimExists {
      p:vprop;
    }
  | Tm_IntroExists {
      p:vprop;
      witnesses:list term;
    }
  | Tm_While {
      invariant:term;
      condition:st_term;
      condition_var: ppname;
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
      binder:binder;
      initializer:term;
      body:st_term;
    }
  | Tm_WithLocalArray {
      binder:binder;
      initializer:term;
      length:term;
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
  | Tm_Unreachable
  | Tm_ProofHintWithBinders {
      hint_type:proof_hint_type;
      binders:list binder;
      t:st_term
  }
  | Tm_WithInv {
      name : term; // invariant name is an F* term that is an Tm_fvar or Tm_name
      body : st_term;
      returns_inv : option (binder & vprop);
    }

and st_term = {
    term : st_term';
    range : range;
    effect_tag: effect_hint
} 

and branch = pattern & st_term

noeq
type decl' =
  | FnDecl {
      (* A function declaration, currently the only Pulse
      top-level decl. This will be mostly checked as a nested
      Tm_Abs with bs and body, especially if non-recursive. *)
      id : R.ident;
      isrec : bool;
      bs : list (option qualifier & binder & bv);
      comp : comp; (* bs in scope *)
      meas : (meas:option term{Some? meas ==> isrec}); (* bs in scope *)
      body : st_term; (* bs in scope *)
  }
and decl = {
  d : decl';
  range : range;
}

let mk_binder_with_attrs (binder_ty:term) (binder_ppname:ppname) binder_attrs : binder =
  {binder_ty;binder_ppname;binder_attrs}

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
  | C_STGhost s -> s.res

let stateful_comp (c:comp) =
  C_ST? c || C_STAtomic? c || C_STGhost? c

let st_comp_of_comp (c:comp{stateful_comp c}) : st_comp =
  match c with
  | C_ST s
  | C_STAtomic _ _ s
  | C_STGhost s -> s

let with_st_comp (c:comp{stateful_comp c}) (s:st_comp) : comp =
  match c with
  | C_ST _ -> C_ST s
  | C_STAtomic inames obs _ -> C_STAtomic inames obs s
  | C_STGhost _ -> C_STGhost s

let comp_u (c:comp { stateful_comp c }) = (st_comp_of_comp c).u

let universe_of_comp (c:comp_st) =
  match c with
  | C_ST _ -> RT.u_zero
  | _ -> Pulse.Reflection.Util.u_atomic_ghost (comp_u c)

let comp_pre (c:comp { stateful_comp c }) = (st_comp_of_comp c).pre

let comp_post (c:comp { stateful_comp c }) = (st_comp_of_comp c).post

let comp_inames (c:comp { C_STAtomic? c }) : term =
  match c with
  | C_STAtomic inames _ _ -> inames

let nvar = ppname & var 
let v_as_nv x : nvar = ppname_default, x
let as_binder (t:term) = null_binder t

