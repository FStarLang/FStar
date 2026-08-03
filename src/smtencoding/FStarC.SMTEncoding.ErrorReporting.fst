(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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

module FStarC.SMTEncoding.ErrorReporting

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.BaseTypes
open FStarC.SMTEncoding.Term
open FStarC.SMTEncoding.Util
open FStarC.SMTEncoding
open FStarC.Range
open FStarC.Class.Show
module BU = FStarC.Util

(* Smart constructors: a context or a branch with no goals under it is
   itself trivial, and must not be emitted. *)
let gctx (ds:list decl) (t:goal_tree) : goal_tree =
  match t with
  | GTrivial -> GTrivial
  | _ -> GCtx ds t

let gbranch (ts:list goal_tree) : ML goal_tree =
  match ts |> List.filter (function GTrivial -> false | _ -> true) with
  | [] -> GTrivial
  | [t] -> t
  | ts -> GBranch ts

let rec goals_of (t:goal_tree) : ML (list goal) =
  match t with
  | GTrivial -> []
  | GLeaf g -> [g]
  | GCtx _ t -> goals_of t
  | GBranch ts -> List.collect goals_of ts

let goal_context (t:goal_tree) (g:goal) : ML (list decl) =
  let rec aux (t:goal_tree) : ML (option (list decl)) =
    match t with
    | GTrivial -> None
    | GLeaf g' -> if g'.goal_id = g.goal_id then Some [] else None
    | GCtx ds t -> aux t |> Option.map (fun ds' -> ds @ ds')
    | GBranch ts ->
      List.fold_left (fun acc t -> match acc with Some _ -> acc | None -> aux t) None ts
  in
  Option.dflt [] (aux t)

let split_goals use_env_msg  //when present, provides an alternate error message,
                             //usually "could not check implicit argument",
                             //        "could not prove post-condition"
                             //or something like that
               (r:Range.t)   //the source range in which this query was asked
               (q:term)      //the query
             : ML goal_tree
             =
    let ctr = mk_ref 0 in
    (* Names for the constants and hypotheses we introduce.  The counter is
       local to the query: all of these declarations live inside a push/pop
       frame, so they only have to be unique within it, and keeping them
       independent of the rest of the run makes error messages reproducible. *)
    let name_ctr = mk_ref 0 in
    let fresh_name (prefix:string) : ML string =
      name_ctr := !name_ctr + 1;
      prefix ^ show !name_ctr
    in
    let flag, msg_prefix = match use_env_msg with
        | None -> false, Pprint.empty
        | Some f -> true, Pprint.doc_of_string (f()) in
    let mk_leaf (msg:Errors.error_message) (ropt:option Range.t) (t:term) : ML goal_tree =
        let open FStarC.Pprint in
        let msg = if flag
                  then (Errors.Msg.text "Failed to verify implicit argument: " ^^ msg_prefix) :: msg
                  else msg in
        let rng = range_of_term t in
        let rng = match ropt with
                  | None -> rng
                  | Some r -> if Range.rng_included (Range.use_range rng) (Range.use_range r)
                              then rng
                              else Range.set_def_range r (Range.def_range rng)
        in
        ctr := !ctr + 1;
        GLeaf { goal_id = !ctr; goal_msg = msg; goal_range = rng; goal_term = t }
    in
    (* An assumption emitted by the walker.  It is given a fresh name, and no
       fact ids, so that --using_facts_from never filters it out. *)
    let hyp (t:term) : ML decl =
        mkAssume (t, None, fresh_name "@hypothesis_")
    in
    (* Is [t] a small quantifier-free formula?  Such a formula is cheap to
       assume: it adds no new quantifier instantiations, it only brings ground
       terms into the solver's congruence closure. *)
    let quantifier_free (t:term) : ML bool =
        let budget = mk_ref 200 in
        let rec aux (t:term) : ML bool =
            if !budget <= 0 then false
            else begin
              budget := !budget - 1;
              match t with
              | Quant _ _ _ _ _ _ -> false
              | App _ tms _ -> List.for_all aux tms
              | Let tms t -> List.for_all aux tms && aux t
              | Labeled t _ _ -> aux t
              | _ -> true
            end
        in
        aux t
    in
    (* [aux] returns the goal tree together with a flag saying whether the tree
       really establishes the term it was given.  The flag is false when the
       term contains an [Unreachable] marker, which we deliberately do not
       prove; such a term may not be assumed elsewhere (it is defined to be
       [false] in the prelude). *)
    let rec aux (default_msg : Errors.error_message) //the error message to report for a leaf
                (ropt:option Range.t)                //position of the enclosing Labeled node, if any
                (q:term)                             //the term being split
     : ML (goal_tree & bool)
     =  match q with
        | Labeled arg [d] r when Errors.Msg.renderdoc d = "Could not prove post-condition" ->
          (* [check_expected_effect] labels a definition's *whole* guard with
             this message, so it says nothing about the individual goal.  Keep
             it only as a position, and report whatever more specific message
             is in scope. *)
          aux default_msg (Some r) arg

        | Labeled arg reason r ->
          aux reason (Some r) arg

        | App TrueOp [] _ ->
          GTrivial, true

        | App (Var "Unreachable") _ _ ->
          //ITEs are encoded with an additional else case just to make them well-formed
          //These are not real goals
          GTrivial, false

        | App And conjuncts _ ->
          (* To prove [c1 /\ ... /\ cn] we prove each [ci] under the assumption
             of the preceding conjuncts.  This is sound, and it is what keeps
             the terms occurring in the earlier conjuncts available to the
             solver -- in a single monolithic query they were all in scope. *)
          let rec seq (cs:list term) : ML (goal_tree & bool) =
            match cs with
            | [] -> GTrivial, true
            | [c] -> aux default_msg ropt c
            | c::cs ->
              let t, ok = aux default_msg ropt c in
              let rest, ok' = seq cs in
              let rest = if ok && quantifier_free c then gctx [hyp c] rest else rest in
              gbranch [t; rest], ok && ok'
          in
          seq conjuncts

        | App Imp [lhs; rhs] _ ->
          let t, ok = aux default_msg ropt rhs in
          gctx [hyp lhs] t, ok

        | App ITE [hd; q1; q2] _ ->
          let t1, ok1 = aux default_msg ropt q1 in
          let t2, ok2 = aux default_msg ropt q2 in
          gbranch [ gctx [hyp hd]         t1;
                    gctx [hyp (mkNot hd)] t2 ],
          ok1 && ok2

        | Quant Forall _pats _iopt sorts body _ ->
          (* Skolemize: each bound variable becomes a fresh constant.  Note we
             keep them as FreeV, which prints exactly like a constant but keeps
             the hash-consed encodings of refinements parameterized over them. *)
          let fvs = sorts |> List.map (fun s -> mk_fv (fresh_name "@sk_", s)) in
          let decls = fvs |> List.map (fun fv -> DeclFun (fv_name fv) [] (fv_sort fv) None) in
          let t, ok = aux default_msg ropt (Term.inst (List.map mkFreeV fvs) body) in
          gctx decls t, ok

        | Let es body ->
          (* Turn each let binding into a fresh constant with a defining
             equation, rather than inlining it (which would destroy sharing).
             The only producer of [Let] is the encoding of a match scrutinee,
             which is always of [Term_sort]. *)
          let rec go (fvs:list fv) (decls:list decl) (es:list term) : ML (list fv & list decl) =
            match es with
            | [] -> fvs, decls
            | e::es ->
              let e = Term.inst (List.map mkFreeV fvs) e in
              let fv = mk_fv (fresh_name "@let_", Term_sort) in
              go (fvs @ [fv])
                 (decls @ [DeclFun (fv_name fv) [] Term_sort None; hyp (mkEq (mkFreeV fv, e))])
                 es
          in
          let fvs, decls = go [] [] es in
          let t, ok = aux default_msg ropt (Term.inst (List.map mkFreeV fvs) body) in
          gctx decls t, ok

        | App RealDiv _ _
        | App Add _ _
        | App Sub _ _
        | App Div _ _
        | App Mul _ _
        | App Minus _ _
        | App Mod _ _
        | App BvAnd _ _
        | App BvXor _ _
        | App BvOr _ _
        | App BvAdd _ _
        | App BvSub _ _
        | App BvShl _ _
        | App BvShr _ _
        | App (BvRol _) _ _
        | App (BvRor _) _ _
        | App BvExtRol _ _
        | App BvExtRor _ _
        | App BvUdiv _ _
        | App BvMod _ _
        | App BvMul _ _
        | App (BvUext _) _ _
        | App BvNot _ _
        | App BvToNat _ _
        | App (NatToBv _) _ _ ->
          failwith "Impossible: non-propositional term"

        | App ITE _ _
        | App Imp _ _ ->
          failwith "Impossible: arity mismatch"

        (* Everything else is an atomic goal: existentials, disjunctions,
           equalities, applications of uninterpreted predicates, ... *)
        | _ ->
          mk_leaf default_msg ropt q, true
    in
    fst (aux (Errors.mkmsg "Assertion failed") None q)
