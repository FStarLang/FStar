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
(* [binder_offset_pattern_spec] is invariant under substitution. *)

let rec binder_offset_pattern_spec_invariant (p:pattern_spec) (ss:subst_spec)
  : Lemma (ensures binder_offset_pattern_spec p ==
                   binder_offset_pattern_spec (subst_pattern_spec p ss))
          (decreases p)
  = match p with
    | Ps_Cons _ _ pats ->
      binder_offset_patterns_spec_invariant pats ss
    | _ -> ()

and binder_offset_patterns_spec_invariant (ps:list (pattern_spec & bool)) (ss:subst_spec)
  : Lemma (ensures binder_offset_patterns_spec ps ==
                   binder_offset_patterns_spec (subst_patterns_spec ps ss))
          (decreases ps)
  = match ps with
    | [] -> ()
    | (hd, _)::tl ->
      binder_offset_pattern_spec_invariant hd ss;
      let n = binder_offset_pattern_spec hd in
      binder_offset_patterns_spec_invariant tl (shift_subst_spec_n n ss)

(* ------------------------------------------------------------------ *)
(* open . close = id on locally-nameless [term_spec]. *)

let rec open_close_inverse'_spec (i:nat) (t:term_spec { ln_spec' t (i - 1) }) (x:var)
  : Lemma
      (ensures subst_term_spec
                 (subst_term_spec t [ NDs x i ])
                 (open_with_var_spec x i)
               == t)
      (decreases t)
  = match t with
    | Ts_UInst _ _
    | Ts_FVar _
    | Ts_Type _
    | Ts_Const _
    | Ts_Unsupp
    | Ts_Unknown
    | Ts_Uvar _
    | Ts_BVar _
    | Ts_Var _ -> ()

    | Ts_App t1 t2 _ ->
      open_close_inverse'_spec i t1 x;
      open_close_inverse'_spec i t2 x

    | Ts_Abs b body ->
      open_close_inverse'_spec_binder i b x;
      open_close_inverse'_spec (i + 1) body x

    | Ts_Arrow b c ->
      open_close_inverse'_spec_binder i b x;
      open_close_inverse'_spec_comp (i + 1) c x

    | Ts_Refine sort f ->
      open_close_inverse'_spec i sort x;
      open_close_inverse'_spec (i + 1) f x

    | Ts_Let recf attrs sort def body ->
      open_close_inverse'_spec_terms i attrs x;
      open_close_inverse'_spec i sort x;
      (if recf
       then open_close_inverse'_spec (i + 1) def x
       else open_close_inverse'_spec i def x);
      open_close_inverse'_spec (i + 1) body x

    | Ts_Match scr ret brs ->
      open_close_inverse'_spec i scr x;
      open_close_inverse'_spec_ret i ret x;
      open_close_inverse'_spec_branches i brs x

    | Ts_AscribedT e ta tac _ ->
      open_close_inverse'_spec i e x;
      open_close_inverse'_spec i ta x;
      (match tac with
       | None -> ()
       | Some tac -> open_close_inverse'_spec i tac x)

    | Ts_AscribedC e c tac _ ->
      open_close_inverse'_spec i e x;
      open_close_inverse'_spec_comp i c x;
      (match tac with
       | None -> ()
       | Some tac -> open_close_inverse'_spec i tac x)

and open_close_inverse'_spec_binder (i:nat) (b:binder_spec { ln_spec'_binder b (i - 1) }) (x:var)
  : Lemma
      (ensures subst_binder_spec
                 (subst_binder_spec b [ NDs x i ])
                 (open_with_var_spec x i)
               == b)
      (decreases b)
  = let Bs sort _ = b in
    open_close_inverse'_spec i sort x

and open_close_inverse'_spec_terms (i:nat) (ts:list term_spec { ln_spec'_terms ts (i - 1) }) (x:var)
  : Lemma
      (ensures subst_terms_spec
                 (subst_terms_spec ts [ NDs x i ])
                 (open_with_var_spec x i)
               == ts)
      (decreases ts)
  = match ts with
    | [] -> ()
    | t::ts ->
      open_close_inverse'_spec i t x;
      open_close_inverse'_spec_terms i ts x

and open_close_inverse'_spec_comp (i:nat) (c:comp_spec { ln_spec'_comp c (i - 1) }) (x:var)
  : Lemma
      (ensures subst_comp_spec
                 (subst_comp_spec c [ NDs x i ])
                 (open_with_var_spec x i)
               == c)
      (decreases c)
  = match c with
    | Cs_Total t
    | Cs_GTotal t -> open_close_inverse'_spec i t x

    | Cs_Lemma pre post pats ->
      open_close_inverse'_spec i pre x;
      open_close_inverse'_spec i post x;
      open_close_inverse'_spec i pats x

    | Cs_Eff _ _ res args decrs ->
      open_close_inverse'_spec i res x;
      open_close_inverse'_spec_args i args x;
      open_close_inverse'_spec_terms i decrs x

and open_close_inverse'_spec_args (i:nat)
                                  (ts:list (term_spec & aqualv_spec) { ln_spec'_args ts (i - 1) })
                                  (x:var)
  : Lemma
      (ensures subst_args_spec
                 (subst_args_spec ts [ NDs x i ])
                 (open_with_var_spec x i)
               == ts)
      (decreases ts)
  = match ts with
    | [] -> ()
    | (t,_)::ts ->
      open_close_inverse'_spec i t x;
      open_close_inverse'_spec_args i ts x

and open_close_inverse'_spec_ret (i:nat)
      (o:option (binder_spec & (either term_spec comp_spec & option term_spec & bool)) { ln_spec'_ret o (i - 1) })
      (x:var)
  : Lemma
      (ensures subst_ret_spec
                 (subst_ret_spec o [ NDs x i ])
                 (open_with_var_spec x i)
               == o)
      (decreases o)
  = match o with
    | None -> ()
    | Some (b, (Inl t, as_, _)) ->
      open_close_inverse'_spec_binder i b x;
      open_close_inverse'_spec (i + 1) t x;
      (match as_ with
       | None -> ()
       | Some t -> open_close_inverse'_spec (i + 1) t x)
    | Some (b, (Inr c, as_, _)) ->
      open_close_inverse'_spec_binder i b x;
      open_close_inverse'_spec_comp (i + 1) c x;
      (match as_ with
       | None -> ()
       | Some t -> open_close_inverse'_spec (i + 1) t x)

and open_close_inverse'_spec_patterns (i:nat)
      (ps:list (pattern_spec & bool) { ln_spec'_patterns ps (i - 1) })
      (x:var)
  : Lemma
      (ensures subst_patterns_spec
                 (subst_patterns_spec ps [ NDs x i ])
                 (open_with_var_spec x i)
               == ps)
      (decreases ps)
  = match ps with
    | [] -> ()
    | (p, _)::ps' ->
      open_close_inverse'_spec_pattern i p x;
      let n = binder_offset_pattern_spec p in
      binder_offset_pattern_spec_invariant p [ NDs x i ];
      open_close_inverse'_spec_patterns (i + n) ps' x

and open_close_inverse'_spec_pattern (i:nat) (p:pattern_spec { ln_spec'_pattern p (i - 1) }) (x:var)
  : Lemma
      (ensures subst_pattern_spec
                 (subst_pattern_spec p [ NDs x i ])
                 (open_with_var_spec x i)
               == p)
      (decreases p)
  = match p with
    | Ps_Constant _ -> ()
    | Ps_Cons _ _ pats -> open_close_inverse'_spec_patterns i pats x
    | Ps_Var -> ()
    | Ps_Dot_Term topt ->
      (match topt with
       | None -> ()
       | Some t -> open_close_inverse'_spec i t x)

and open_close_inverse'_spec_branch (i:nat) (br:(pattern_spec & term_spec) { ln_spec'_branch br (i - 1) }) (x:var)
  : Lemma
      (ensures subst_branch_spec
                 (subst_branch_spec br [ NDs x i ])
                 (open_with_var_spec x i)
               == br)
      (decreases br)
  = let p, t = br in
    let j = binder_offset_pattern_spec p in
    binder_offset_pattern_spec_invariant p [ NDs x i ];
    open_close_inverse'_spec_pattern i p x;
    open_close_inverse'_spec (i + j) t x

and open_close_inverse'_spec_branches (i:nat)
      (brs:list (pattern_spec & term_spec) { ln_spec'_branches brs (i - 1) })
      (x:var)
  : Lemma
      (ensures subst_branches_spec
                 (subst_branches_spec brs [ NDs x i ])
                 (open_with_var_spec x i)
               == brs)
      (decreases brs)
  = match brs with
    | [] -> ()
    | br::brs ->
      open_close_inverse'_spec_branch i br x;
      open_close_inverse'_spec_branches i brs x

(* ------------------------------------------------------------------ *)
(* close . open = id on locally-nameless [term_spec], when [x] is fresh. *)

let rec close_open_inverse'_spec (i:nat)
                                 (t:term_spec)
                                 (x:var { ~(x `Set.mem` freevars_spec t) })
  : Lemma
      (ensures subst_term_spec
                 (subst_term_spec t (open_with_var_spec x i))
                 [ NDs x i ]
               == t)
      (decreases t)
  = match t with
    | Ts_Uvar _ -> assert false
    | Ts_UInst _ _
    | Ts_FVar _
    | Ts_Type _
    | Ts_Const _
    | Ts_Unsupp
    | Ts_Unknown
    | Ts_BVar _
    | Ts_Var _ -> ()

    | Ts_App t1 t2 _ ->
      close_open_inverse'_spec i t1 x;
      close_open_inverse'_spec i t2 x

    | Ts_Abs b body ->
      close_open_inverse'_spec_binder i b x;
      close_open_inverse'_spec (i + 1) body x

    | Ts_Arrow b c ->
      close_open_inverse'_spec_binder i b x;
      close_open_inverse'_spec_comp (i + 1) c x

    | Ts_Refine sort f ->
      close_open_inverse'_spec i sort x;
      close_open_inverse'_spec (i + 1) f x

    | Ts_Let recf attrs sort def body ->
      close_open_inverse'_spec_terms i attrs x;
      close_open_inverse'_spec i sort x;
      close_open_inverse'_spec (if recf then (i + 1) else i) def x;
      close_open_inverse'_spec (i + 1) body x

    | Ts_Match scr ret brs ->
      close_open_inverse'_spec i scr x;
      close_open_inverse'_spec_ret i ret x;
      close_open_inverse'_spec_branches i brs x

    | Ts_AscribedT e ta tac _ ->
      close_open_inverse'_spec i e x;
      close_open_inverse'_spec i ta x;
      (match tac with
       | None -> ()
       | Some t -> close_open_inverse'_spec i t x)

    | Ts_AscribedC e c tac _ ->
      close_open_inverse'_spec i e x;
      close_open_inverse'_spec_comp i c x;
      (match tac with
       | None -> ()
       | Some t -> close_open_inverse'_spec i t x)

and close_open_inverse'_spec_comp (i:nat)
                                  (c:comp_spec)
                                  (x:var { ~(x `Set.mem` freevars_comp_spec c) })
  : Lemma
      (ensures subst_comp_spec
                 (subst_comp_spec c (open_with_var_spec x i))
                 [ NDs x i ]
               == c)
      (decreases c)
  = match c with
    | Cs_Total t
    | Cs_GTotal t -> close_open_inverse'_spec i t x

    | Cs_Lemma pre post pats ->
      close_open_inverse'_spec i pre x;
      close_open_inverse'_spec i post x;
      close_open_inverse'_spec i pats x

    | Cs_Eff _ _ res args decrs ->
      close_open_inverse'_spec i res x;
      close_open_inverse'_spec_args i args x;
      close_open_inverse'_spec_terms i decrs x

and close_open_inverse'_spec_args (i:nat)
                                  (args:list (term_spec & aqualv_spec))
                                  (x:var { ~(x `Set.mem` freevars_args_spec args) })
  : Lemma
      (ensures subst_args_spec
                 (subst_args_spec args (open_with_var_spec x i))
                 [ NDs x i ]
               == args)
      (decreases args)
  = match args with
    | [] -> ()
    | (a, _)::args ->
      close_open_inverse'_spec i a x;
      close_open_inverse'_spec_args i args x

and close_open_inverse'_spec_binder (i:nat)
                                    (b:binder_spec)
                                    (x:var { ~(x `Set.mem` freevars_binder_spec b) })
  : Lemma
      (ensures subst_binder_spec
                 (subst_binder_spec b (open_with_var_spec x i))
                 [ NDs x i ]
               == b)
      (decreases b)
  = let Bs sort _ = b in
    close_open_inverse'_spec i sort x

and close_open_inverse'_spec_terms (i:nat)
                                   (ts:list term_spec)
                                   (x:var { ~(x `Set.mem` freevars_terms_spec ts) })
  : Lemma
      (ensures subst_terms_spec
                 (subst_terms_spec ts (open_with_var_spec x i))
                 [ NDs x i ]
               == ts)
      (decreases ts)
  = match ts with
    | [] -> ()
    | hd::tl ->
      close_open_inverse'_spec i hd x;
      close_open_inverse'_spec_terms i tl x

and close_open_inverse'_spec_ret (i:nat)
      (o:option (binder_spec & (either term_spec comp_spec & option term_spec & bool)))
      (x:var { ~(x `Set.mem` freevars_ret_spec o) })
  : Lemma
      (ensures subst_ret_spec
                 (subst_ret_spec o (open_with_var_spec x i))
                 [ NDs x i ]
               == o)
      (decreases o)
  = match o with
    | None -> ()
    | Some (b, (Inl t, as_, _)) ->
      close_open_inverse'_spec_binder i b x;
      close_open_inverse'_spec (i + 1) t x;
      (match as_ with
       | None -> ()
       | Some t -> close_open_inverse'_spec (i + 1) t x)
    | Some (b, (Inr c, as_, _)) ->
      close_open_inverse'_spec_binder i b x;
      close_open_inverse'_spec_comp (i + 1) c x;
      (match as_ with
       | None -> ()
       | Some t -> close_open_inverse'_spec (i + 1) t x)

and close_open_inverse'_spec_branches (i:nat)
                                      (brs:list (pattern_spec & term_spec))
                                      (x:var { ~(x `Set.mem` freevars_branches_spec brs) })
  : Lemma
      (ensures subst_branches_spec
                 (subst_branches_spec brs (open_with_var_spec x i))
                 [ NDs x i ]
               == brs)
      (decreases brs)
  = match brs with
    | [] -> ()
    | b::brs ->
      close_open_inverse'_spec_branch i b x;
      close_open_inverse'_spec_branches i brs x

and close_open_inverse'_spec_branch (i:nat)
                                    (br:(pattern_spec & term_spec))
                                    (x:var { ~(x `Set.mem` freevars_branch_spec br) })
  : Lemma
      (ensures subst_branch_spec
                 (subst_branch_spec br (open_with_var_spec x i))
                 [ NDs x i ]
               == br)
      (decreases br)
  = let p, t = br in
    close_open_inverse'_spec_pattern i p x;
    binder_offset_pattern_spec_invariant p (open_with_var_spec x i);
    close_open_inverse'_spec (i + binder_offset_pattern_spec p) t x

and close_open_inverse'_spec_pattern (i:nat)
                                     (p:pattern_spec)
                                     (x:var { ~(x `Set.mem` freevars_pattern_spec p) })
  : Lemma
      (ensures subst_pattern_spec
                 (subst_pattern_spec p (open_with_var_spec x i))
                 [ NDs x i ]
               == p)
      (decreases p)
  = match p with
    | Ps_Constant _ -> ()
    | Ps_Cons _ _ pats -> close_open_inverse'_spec_patterns i pats x
    | Ps_Var -> ()
    | Ps_Dot_Term topt ->
      (match topt with
       | None -> ()
       | Some t -> close_open_inverse'_spec i t x)

and close_open_inverse'_spec_patterns (i:nat)
                                      (ps:list (pattern_spec & bool))
                                      (x:var { ~(x `Set.mem` freevars_patterns_spec ps) })
  : Lemma
      (ensures subst_patterns_spec
                 (subst_patterns_spec ps (open_with_var_spec x i))
                 [ NDs x i ]
               == ps)
      (decreases ps)
  = match ps with
    | [] -> ()
    | (p, _)::ps' ->
      close_open_inverse'_spec_pattern i p x;
      let n = binder_offset_pattern_spec p in
      binder_offset_pattern_spec_invariant p (open_with_var_spec x i);
      close_open_inverse'_spec_patterns (i + n) ps' x

(* ------------------------------------------------------------------ *)
(* Closing over a variable that does not occur free is a no-op. Mirror of
   [Reflection.Typing.close_with_not_free_var]. *)

let rec close_with_not_free_var_spec (t:term_spec) (x:var) (i:nat)
  : Lemma
      (requires ~ (Set.mem x (freevars_spec t)))
      (ensures subst_term_spec t [ NDs x i ] == t)
      (decreases t)
  = match t with
    | Ts_Var _
    | Ts_BVar _
    | Ts_FVar _
    | Ts_UInst _ _ -> ()
    | Ts_App hd arg _ ->
      close_with_not_free_var_spec hd x i;
      close_with_not_free_var_spec arg x i
    | Ts_Abs b body ->
      close_binder_with_not_free_var_spec b x i;
      close_with_not_free_var_spec body x (i + 1)
    | Ts_Arrow b c ->
      close_binder_with_not_free_var_spec b x i;
      close_comp_with_not_free_var_spec c x (i + 1)
    | Ts_Type _ -> ()
    | Ts_Refine sort f ->
      close_with_not_free_var_spec sort x i;
      close_with_not_free_var_spec f x (i + 1)
    | Ts_Const _ -> ()
    | Ts_Uvar _ -> assert False
    | Ts_Let recf attrs sort e1 e2 ->
      close_terms_with_not_free_var_spec attrs x i;
      close_with_not_free_var_spec sort x i;
      (if recf then close_with_not_free_var_spec e1 x (i + 1)
       else close_with_not_free_var_spec e1 x i);
      close_with_not_free_var_spec e2 x (i + 1)
    | Ts_Match scrutinee ret_opt brs ->
      close_with_not_free_var_spec scrutinee x i;
      close_ret_with_not_free_var_spec ret_opt x i;
      close_branches_with_not_free_var_spec brs x i
    | Ts_AscribedT e ta tacopt _ ->
      close_with_not_free_var_spec e x i;
      close_with_not_free_var_spec ta x i;
      (match tacopt with
       | None -> ()
       | Some tac -> close_with_not_free_var_spec tac x i)
    | Ts_AscribedC e c tacopt _ ->
      close_with_not_free_var_spec e x i;
      close_comp_with_not_free_var_spec c x i;
      (match tacopt with
       | None -> ()
       | Some tac -> close_with_not_free_var_spec tac x i)
    | Ts_Unknown -> ()
    | Ts_Unsupp -> ()

and close_ret_with_not_free_var_spec
      (o:option (binder_spec & (either term_spec comp_spec & option term_spec & bool)))
      (x:var) (i:nat)
  : Lemma
      (requires ~ (Set.mem x (freevars_ret_spec o)))
      (ensures subst_ret_spec o [ NDs x i ] == o)
      (decreases o)
  = match o with
    | None -> ()
    | Some (b, (Inl t, as_opt, _)) ->
      close_binder_with_not_free_var_spec b x i;
      close_with_not_free_var_spec t x (i + 1);
      (match as_opt with
       | None -> ()
       | Some t -> close_with_not_free_var_spec t x (i + 1))
    | Some (b, (Inr c, as_opt, _)) ->
      close_binder_with_not_free_var_spec b x i;
      close_comp_with_not_free_var_spec c x (i + 1);
      (match as_opt with
       | None -> ()
       | Some t -> close_with_not_free_var_spec t x (i + 1))

and close_branches_with_not_free_var_spec
      (brs:list (pattern_spec & term_spec)) (x:var) (i:nat)
  : Lemma
      (requires ~ (Set.mem x (freevars_branches_spec brs)))
      (ensures subst_branches_spec brs [ NDs x i ] == brs)
      (decreases brs)
  = match brs with
    | [] -> ()
    | hd::tl ->
      close_branch_with_not_free_var_spec hd x i;
      close_branches_with_not_free_var_spec tl x i

and close_branch_with_not_free_var_spec
      (br:(pattern_spec & term_spec)) (x:var) (i:nat)
  : Lemma
      (requires ~ (Set.mem x (freevars_branch_spec br)))
      (ensures subst_branch_spec br [ NDs x i ] == br)
      (decreases br)
  = let p, t = br in
    close_pattern_with_not_free_var_spec p x i;
    close_with_not_free_var_spec t x (binder_offset_pattern_spec p + i)

and close_pattern_with_not_free_var_spec (p:pattern_spec) (x:var) (i:nat)
  : Lemma
      (requires ~ (Set.mem x (freevars_pattern_spec p)))
      (ensures subst_pattern_spec p [ NDs x i ] == p)
      (decreases p)
  = match p with
    | Ps_Constant _ -> ()
    | Ps_Cons _ _ pats ->
      close_patterns_with_not_free_var_spec pats x i
    | Ps_Var -> ()
    | Ps_Dot_Term topt ->
      (match topt with
       | None -> ()
       | Some t -> close_with_not_free_var_spec t x i)

and close_patterns_with_not_free_var_spec (l:list (pattern_spec & bool)) (x:var) (i:nat)
  : Lemma
      (requires ~ (Set.mem x (freevars_patterns_spec l)))
      (ensures subst_patterns_spec l [ NDs x i ] == l)
      (decreases l)
  = match l with
    | [] -> ()
    | (p, _)::tl ->
      close_pattern_with_not_free_var_spec p x i;
      close_patterns_with_not_free_var_spec tl x (binder_offset_pattern_spec p + i)

and close_terms_with_not_free_var_spec (l:list term_spec) (x:var) (i:nat)
  : Lemma
      (requires ~ (Set.mem x (freevars_terms_spec l)))
      (ensures subst_terms_spec l [ NDs x i ] == l)
      (decreases l)
  = match l with
    | [] -> ()
    | hd::tl ->
      close_with_not_free_var_spec hd x i;
      close_terms_with_not_free_var_spec tl x i

and close_binder_with_not_free_var_spec (b:binder_spec) (x:var) (i:nat)
  : Lemma
      (requires ~ (Set.mem x (freevars_binder_spec b)))
      (ensures subst_binder_spec b [ NDs x i ] == b)
      (decreases b)
  = let Bs sort _ = b in
    close_with_not_free_var_spec sort x i

and close_comp_with_not_free_var_spec (c:comp_spec) (x:var) (i:nat)
  : Lemma
      (requires ~ (Set.mem x (freevars_comp_spec c)))
      (ensures subst_comp_spec c [ NDs x i ] == c)
      (decreases c)
  = match c with
    | Cs_Total t
    | Cs_GTotal t -> close_with_not_free_var_spec t x i
    | Cs_Lemma pre post pats ->
      close_with_not_free_var_spec pre x i;
      close_with_not_free_var_spec post x i;
      close_with_not_free_var_spec pats x i
    | Cs_Eff _ _ t args decrs ->
      close_with_not_free_var_spec t x i;
      close_args_with_not_free_var_spec args x i;
      close_terms_with_not_free_var_spec decrs x i

and close_args_with_not_free_var_spec (l:list (term_spec & aqualv_spec)) (x:var) (i:nat)
  : Lemma
      (requires ~ (Set.mem x (freevars_args_spec l)))
      (ensures subst_args_spec l [ NDs x i ] == l)
      (decreases l)
  = match l with
    | [] -> ()
    | (t, _)::tl ->
      close_with_not_free_var_spec t x i;
      close_args_with_not_free_var_spec tl x i

(* ------------------------------------------------------------------ *)
(* Substituting a bound index [j] that is beyond the local scope is a
   no-op. Mirror of [Reflection.Typing.open_with_gt_ln]. (The [Ts_Uvar]
   case is vacuous here: [ln_spec'] is [false] on uvars, contradicting the
   precondition, so no [admit] is needed.) *)

let rec open_with_gt_ln_spec (e:term_spec) (i:nat) (t:term_spec) (j:nat)
  : Lemma (requires ln_spec' e i /\ i < j)
          (ensures subst_term_spec e [ DTs j t ] == e)
          (decreases e)
  = match e with
    | Ts_UInst _ _
    | Ts_FVar _
    | Ts_Type _
    | Ts_Const _
    | Ts_Unsupp
    | Ts_Unknown
    | Ts_Uvar _
    | Ts_Var _
    | Ts_BVar _ -> ()
    | Ts_App hd arg _ ->
      open_with_gt_ln_spec hd i t j;
      open_with_gt_ln_spec arg i t j
    | Ts_Abs b body ->
      open_with_gt_ln_spec_binder b i t j;
      open_with_gt_ln_spec body (i + 1) t (j + 1)
    | Ts_Arrow b c ->
      open_with_gt_ln_spec_binder b i t j;
      open_with_gt_ln_spec_comp c (i + 1) t (j + 1)
    | Ts_Refine sort f ->
      open_with_gt_ln_spec sort i t j;
      open_with_gt_ln_spec f (i + 1) t (j + 1)
    | Ts_Let recf attrs sort def body ->
      open_with_gt_ln_spec_terms attrs i t j;
      open_with_gt_ln_spec sort i t j;
      (if recf
       then open_with_gt_ln_spec def (i + 1) t (j + 1)
       else open_with_gt_ln_spec def i t j);
      open_with_gt_ln_spec body (i + 1) t (j + 1)
    | Ts_Match scr ret brs ->
      open_with_gt_ln_spec scr i t j;
      open_with_gt_ln_spec_ret ret i t j;
      open_with_gt_ln_spec_branches brs i t j
    | Ts_AscribedT e t1 tac _ ->
      open_with_gt_ln_spec e i t j;
      open_with_gt_ln_spec t1 i t j;
      (match tac with
       | None -> ()
       | Some tac -> open_with_gt_ln_spec tac i t j)
    | Ts_AscribedC e c tac _ ->
      open_with_gt_ln_spec e i t j;
      open_with_gt_ln_spec_comp c i t j;
      (match tac with
       | None -> ()
       | Some tac -> open_with_gt_ln_spec tac i t j)

and open_with_gt_ln_spec_binder (b:binder_spec) (i:nat) (t:term_spec) (j:nat)
  : Lemma (requires ln_spec'_binder b i /\ i < j)
          (ensures subst_binder_spec b [ DTs j t ] == b)
          (decreases b)
  = let Bs sort _ = b in
    open_with_gt_ln_spec sort i t j

and open_with_gt_ln_spec_comp (c:comp_spec) (i:nat) (t:term_spec) (j:nat)
  : Lemma (requires ln_spec'_comp c i /\ i < j)
          (ensures subst_comp_spec c [ DTs j t ] == c)
          (decreases c)
  = match c with
    | Cs_Total t1
    | Cs_GTotal t1 -> open_with_gt_ln_spec t1 i t j
    | Cs_Lemma pre post pats ->
      open_with_gt_ln_spec pre i t j;
      open_with_gt_ln_spec post i t j;
      open_with_gt_ln_spec pats i t j
    | Cs_Eff _ _ res args decrs ->
      open_with_gt_ln_spec res i t j;
      open_with_gt_ln_spec_args args i t j;
      open_with_gt_ln_spec_terms decrs i t j

and open_with_gt_ln_spec_terms (l:list term_spec) (i:nat) (t:term_spec) (j:nat)
  : Lemma (requires ln_spec'_terms l i /\ i < j)
          (ensures subst_terms_spec l [ DTs j t ] == l)
          (decreases l)
  = match l with
    | [] -> ()
    | hd::tl ->
      open_with_gt_ln_spec hd i t j;
      open_with_gt_ln_spec_terms tl i t j

and open_with_gt_ln_spec_ret
      (o:option (binder_spec & (either term_spec comp_spec & option term_spec & bool)))
      (i:nat) (t:term_spec) (j:nat)
  : Lemma (requires ln_spec'_ret o i /\ i < j)
          (ensures subst_ret_spec o [ DTs j t ] == o)
          (decreases o)
  = match o with
    | None -> ()
    | Some (b, (Inl t1, as_, _)) ->
      open_with_gt_ln_spec_binder b i t j;
      open_with_gt_ln_spec t1 (i + 1) t (j + 1);
      (match as_ with
       | None -> ()
       | Some t1 -> open_with_gt_ln_spec t1 (i + 1) t (j + 1))
    | Some (b, (Inr c, as_, _)) ->
      open_with_gt_ln_spec_binder b i t j;
      open_with_gt_ln_spec_comp c (i + 1) t (j + 1);
      (match as_ with
       | None -> ()
       | Some t1 -> open_with_gt_ln_spec t1 (i + 1) t (j + 1))

and open_with_gt_ln_spec_branches (l:list (pattern_spec & term_spec)) (i:nat) (t:term_spec) (j:nat)
  : Lemma (requires ln_spec'_branches l i /\ i < j)
          (ensures subst_branches_spec l [ DTs j t ] == l)
          (decreases l)
  = match l with
    | [] -> ()
    | hd::tl ->
      open_with_gt_ln_spec_branch hd i t j;
      open_with_gt_ln_spec_branches tl i t j

and open_with_gt_ln_spec_args (l:list (term_spec & aqualv_spec)) (i:nat) (t:term_spec) (j:nat)
  : Lemma (requires ln_spec'_args l i /\ i < j)
          (ensures subst_args_spec l [ DTs j t ] == l)
          (decreases l)
  = match l with
    | [] -> ()
    | (t1, _)::tl ->
      open_with_gt_ln_spec t1 i t j;
      open_with_gt_ln_spec_args tl i t j

and open_with_gt_ln_spec_branch (b:(pattern_spec & term_spec)) (i:nat) (t:term_spec) (j:nat)
  : Lemma (requires ln_spec'_branch b i /\ i < j)
          (ensures subst_branch_spec b [ DTs j t ] == b)
          (decreases b)
  = let p, t1 = b in
    open_with_gt_ln_spec_pat p i t j;
    let k = binder_offset_pattern_spec p in
    open_with_gt_ln_spec t1 (i + k) t (j + k)

and open_with_gt_ln_spec_pat (p:pattern_spec) (i:nat) (t:term_spec) (j:nat)
  : Lemma (requires ln_spec'_pattern p i /\ i < j)
          (ensures subst_pattern_spec p [ DTs j t ] == p)
          (decreases p)
  = match p with
    | Ps_Constant _ -> ()
    | Ps_Cons _ _ pats ->
      open_with_gt_ln_spec_pats pats i t j
    | Ps_Var -> ()
    | Ps_Dot_Term topt ->
      (match topt with
       | None -> ()
       | Some t1 -> open_with_gt_ln_spec t1 i t j)

and open_with_gt_ln_spec_pats (l:list (pattern_spec & bool)) (i:nat) (t:term_spec) (j:nat)
  : Lemma (requires ln_spec'_patterns l i /\ i < j)
          (ensures subst_patterns_spec l [ DTs j t ] == l)
          (decreases l)
  = match l with
    | [] -> ()
    | hd::tl ->
      open_with_gt_ln_spec_pat (fst hd) i t j;
      let k = binder_offset_pattern_spec (fst hd) in
      open_with_gt_ln_spec_pats tl (i + k) t (j + k)
