(*
   Copyright 2008-2018 Microsoft Research

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
module FStar.Reflection.TermSpec.Lemmas

(* Structural [freevars]/[ln] predicates on the erasable model type
   [term_spec], together with the substitution-inverse lemmas
   ([open_close]/[close_open], etc.) restated on [term_spec].

   These are the spec-level counterparts of the concrete lemmas in
   [FStar.Reflection.Typing] (on [term] via [inspect_ln]/[pack_ln]).
   Because [term_spec] is a plain inductive with no range/name data, the
   proofs are direct structural inductions with no [pack_ln] round-trip,
   and (unlike their concrete counterparts) they remain true even once
   [==] on [term] becomes range-sensitive.

   This module is built *additively* on the green tree: it introduces no
   changes to existing modules. The concrete lemmas in Reflection.Typing
   will later be rephrased to delegate to these via [denote_term]. *)

open FStar.Stubs.Reflection.Types
open FStar.Stubs.Reflection.V2.Data
open FStar.Reflection.TermSpec
module L = FStar.List.Tot
module Set = FStar.Set

(* ------------------------------------------------------------------ *)
(* Free variables of a [term_spec]. Mirrors [Reflection.Typing.freevars]
   but matches structurally on [term_spec]. Aqualv/binder qualifiers are
   ignored, exactly as in the concrete version. *)

let rec freevars_spec (e:term_spec)
  : GTot (Set.set var) (decreases e)
  = match e with
    | Ts_Uvar _ -> Set.complement Set.empty

    | Ts_UInst _ _
    | Ts_FVar _
    | Ts_Type _
    | Ts_Const _
    | Ts_Unknown
    | Ts_Unsupp
    | Ts_BVar _ -> Set.empty

    | Ts_Var x -> Set.singleton x

    | Ts_App e1 e2 _ ->
      Set.union (freevars_spec e1) (freevars_spec e2)

    | Ts_Abs b body ->
      Set.union (freevars_binder_spec b) (freevars_spec body)

    | Ts_Arrow b c ->
      Set.union (freevars_binder_spec b) (freevars_comp_spec c)

    | Ts_Refine sort f ->
      freevars_spec sort `Set.union`
      freevars_spec f

    | Ts_Let _ attrs sort def body ->
      freevars_terms_spec attrs `Set.union`
      freevars_spec sort `Set.union`
      freevars_spec def `Set.union`
      freevars_spec body

    | Ts_Match scr ret brs ->
      freevars_spec scr `Set.union`
      freevars_ret_spec ret `Set.union`
      freevars_branches_spec brs

    | Ts_AscribedT e t tac _ ->
      freevars_spec e `Set.union`
      freevars_spec t `Set.union`
      freevars_opt_spec tac

    | Ts_AscribedC e c tac _ ->
      freevars_spec e `Set.union`
      freevars_comp_spec c `Set.union`
      freevars_opt_spec tac

and freevars_opt_spec (o:option term_spec)
  : GTot (Set.set var) (decreases o)
  = match o with
    | None -> Set.empty
    | Some t -> freevars_spec t

and freevars_comp_spec (c:comp_spec)
  : GTot (Set.set var) (decreases c)
  = match c with
    | Cs_Total t
    | Cs_GTotal t -> freevars_spec t

    | Cs_Lemma pre post pats ->
      freevars_spec pre `Set.union`
      freevars_spec post `Set.union`
      freevars_spec pats

    | Cs_Eff _ _ res pre post decrs ->
      freevars_spec res `Set.union`
      freevars_spec pre `Set.union`
      freevars_spec post `Set.union`
      freevars_terms_spec decrs

and freevars_args_spec (ts:list (term_spec & aqualv_spec))
  : GTot (Set.set var) (decreases ts)
  = match ts with
    | [] -> Set.empty
    | (t,_)::ts ->
      freevars_spec t `Set.union`
      freevars_args_spec ts

and freevars_terms_spec (ts:list term_spec)
  : GTot (Set.set var) (decreases ts)
  = match ts with
    | [] -> Set.empty
    | t::ts ->
      freevars_spec t `Set.union`
      freevars_terms_spec ts

and freevars_binder_spec (b:binder_spec)
  : GTot (Set.set var) (decreases b)
  = let Bs sort _ = b in
    freevars_spec sort

and freevars_ret_spec (o:option (binder_spec & (either term_spec comp_spec & option term_spec & bool)))
  : GTot (Set.set var) (decreases o)
  = match o with
    | None -> Set.empty
    | Some (b, (Inl t, as_, _)) ->
      freevars_binder_spec b `Set.union`
      freevars_spec t `Set.union`
      freevars_opt_spec as_
    | Some (b, (Inr c, as_, _)) ->
      freevars_binder_spec b `Set.union`
      freevars_comp_spec c `Set.union`
      freevars_opt_spec as_

and freevars_pattern_spec (p:pattern_spec)
  : GTot (Set.set var) (decreases p)
  = match p with
    | Ps_Constant _ -> Set.empty
    | Ps_Cons _ _ subpats -> freevars_patterns_spec subpats
    | Ps_Var -> Set.empty
    | Ps_Dot_Term topt -> freevars_opt_spec topt

and freevars_patterns_spec (ps:list (pattern_spec & bool))
  : GTot (Set.set var) (decreases ps)
  = match ps with
    | [] -> Set.empty
    | (p, _)::ps ->
      freevars_pattern_spec p `Set.union`
      freevars_patterns_spec ps

and freevars_branch_spec (br:(pattern_spec & term_spec))
  : GTot (Set.set var) (decreases br)
  = let p, t = br in
    freevars_pattern_spec p `Set.union`
    freevars_spec t

and freevars_branches_spec (brs:list (pattern_spec & term_spec))
  : GTot (Set.set var) (decreases brs)
  = match brs with
    | [] -> Set.empty
    | hd::tl -> freevars_branch_spec hd `Set.union` freevars_branches_spec tl

(* ------------------------------------------------------------------ *)
(* Local-closedness of a [term_spec]. Mirrors [Reflection.Typing.ln']. *)

let rec ln_spec' (e:term_spec) (n:int)
  : GTot bool (decreases e)
  = match e with
    | Ts_UInst _ _
    | Ts_FVar _
    | Ts_Type _
    | Ts_Const _
    | Ts_Unknown
    | Ts_Unsupp
    | Ts_Var _ -> true
    | Ts_BVar m -> m <= n
    | Ts_App e1 e2 _ -> ln_spec' e1 n && ln_spec' e2 n
    | Ts_Abs b body ->
      ln_spec'_binder b n &&
      ln_spec' body (n + 1)

    | Ts_Arrow b c ->
      ln_spec'_binder b n &&
      ln_spec'_comp c (n + 1)

    | Ts_Refine sort f ->
      ln_spec' sort n &&
      ln_spec' f (n + 1)

    | Ts_Uvar _ -> false

    | Ts_Let recf attrs b def body ->
      ln_spec'_terms attrs n &&
      ln_spec' b n &&
      (if recf then ln_spec' def (n + 1) else ln_spec' def n) &&
      ln_spec' body (n + 1)

    | Ts_Match scr ret brs ->
      ln_spec' scr n &&
      ln_spec'_ret ret n &&
      ln_spec'_branches brs n

    | Ts_AscribedT e t tac _ ->
      ln_spec' e n &&
      ln_spec' t n &&
      ln_spec'_opt tac n

    | Ts_AscribedC e c tac _ ->
      ln_spec' e n &&
      ln_spec'_comp c n &&
      ln_spec'_opt tac n

and ln_spec'_opt (o:option term_spec) (n:int)
  : GTot bool (decreases o)
  = match o with
    | None -> true
    | Some t -> ln_spec' t n

and ln_spec'_comp (c:comp_spec) (i:int)
  : GTot bool (decreases c)
  = match c with
    | Cs_Total t
    | Cs_GTotal t -> ln_spec' t i

    | Cs_Lemma pre post pats ->
      ln_spec' pre i &&
      ln_spec' post i &&
      ln_spec' pats i

    | Cs_Eff _ _ res pre post decrs ->
      ln_spec' res i &&
      ln_spec' pre i &&
      ln_spec' post i &&
      ln_spec'_terms decrs i

and ln_spec'_args (ts:list (term_spec & aqualv_spec)) (i:int)
  : GTot bool (decreases ts)
  = match ts with
    | [] -> true
    | (t,_)::ts ->
      ln_spec' t i &&
      ln_spec'_args ts i

and ln_spec'_binder (b:binder_spec) (n:int)
  : GTot bool (decreases b)
  = let Bs sort _ = b in
    ln_spec' sort n

and ln_spec'_terms (ts:list term_spec) (n:int)
  : GTot bool (decreases ts)
  = match ts with
    | [] -> true
    | t::ts -> ln_spec' t n && ln_spec'_terms ts n

and ln_spec'_ret (o:option (binder_spec & (either term_spec comp_spec & option term_spec & bool))) (n:int)
  : GTot bool (decreases o)
  = match o with
    | None -> true
    | Some (b, (Inl t, as_, _)) ->
      ln_spec'_binder b n &&
      ln_spec' t (n + 1) &&
      ln_spec'_opt as_ (n + 1)
    | Some (b, (Inr c, as_, _)) ->
      ln_spec'_binder b n &&
      ln_spec'_comp c (n + 1) &&
      ln_spec'_opt as_ (n + 1)

and ln_spec'_patterns (ps:list (pattern_spec & bool)) (i:int)
  : GTot bool (decreases ps)
  = match ps with
    | [] -> true
    | (p, _)::ps ->
      let b0 = ln_spec'_pattern p i in
      let n = binder_offset_pattern_spec p in
      let b1 = ln_spec'_patterns ps (i + n) in
      b0 && b1

and ln_spec'_pattern (p:pattern_spec) (i:int)
  : GTot bool (decreases p)
  = match p with
    | Ps_Constant _ -> true
    | Ps_Cons _ _ subpats -> ln_spec'_patterns subpats i
    | Ps_Var -> true
    | Ps_Dot_Term topt ->
      (match topt with
       | None -> true
       | Some t -> ln_spec' t i)

and ln_spec'_branch (br:(pattern_spec & term_spec)) (i:int)
  : GTot bool (decreases br)
  = let p, t = br in
    let b = ln_spec'_pattern p i in
    let j = binder_offset_pattern_spec p in
    let b' = ln_spec' t (i + j) in
    b && b'

and ln_spec'_branches (brs:list (pattern_spec & term_spec)) (i:int)
  : GTot bool (decreases brs)
  = match brs with
    | [] -> true
    | br::brs -> ln_spec'_branch br i && ln_spec'_branches brs i

let ln_spec (t:term_spec) : GTot bool = ln_spec' t (-1)
let ln_spec_comp (c:comp_spec) : GTot bool = ln_spec'_comp c (-1)

(* ------------------------------------------------------------------ *)
(* Opening a bound variable [i] to the free variable [x]. Mirror of
   [Reflection.Typing.open_with_var]. *)

let open_with_var_elt_spec (x:var) (i:nat) : subst_spec_elt = DTs i (Ts_Var x)
let open_with_var_spec (x:var) (i:nat) : subst_spec = [open_with_var_elt_spec x i]

(* ------------------------------------------------------------------ *)
(* Substitution lemmas.

   Only the signatures live here: the proofs are large structural
   inductions, and this module is imported widely (notably by
   [FStar.Reflection.Typing]), so keeping the bodies in the
   implementation keeps them out of every consumer's checked file. *)

val binder_offset_pattern_spec_invariant (p:pattern_spec) (ss:subst_spec)
  : Lemma (ensures binder_offset_pattern_spec p ==
                   binder_offset_pattern_spec (subst_pattern_spec p ss))

val open_close_inverse'_spec (i:nat) (t:term_spec { ln_spec' t (i - 1) }) (x:var)
  : Lemma
      (ensures subst_term_spec
                 (subst_term_spec t [ NDs x i ])
                 (open_with_var_spec x i)
               == t)

val close_open_inverse'_spec (i:nat)
                             (t:term_spec)
                             (x:var { ~(x `Set.mem` freevars_spec t) })
  : Lemma
      (ensures subst_term_spec
                 (subst_term_spec t (open_with_var_spec x i))
                 [ NDs x i ]
               == t)

val close_with_not_free_var_spec (t:term_spec) (x:var) (i:nat)
  : Lemma
      (requires ~ (Set.mem x (freevars_spec t)))
      (ensures subst_term_spec t [ NDs x i ] == t)

val open_with_gt_ln_spec (e:term_spec) (i:nat) (t:term_spec) (j:nat)
  : Lemma (requires ln_spec' e i /\ i < j)
          (ensures subst_term_spec e [ DTs j t ] == e)
