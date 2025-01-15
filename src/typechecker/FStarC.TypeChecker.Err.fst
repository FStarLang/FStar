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
module FStarC.TypeChecker.Err
open FStarC.Effect

open FStarC
open FStarC.Syntax.Syntax
open FStarC.Util
open FStarC.TypeChecker.Env
open FStarC.Range
open FStarC.Ident
open FStarC.Pprint
module N = FStarC.TypeChecker.Normalize

open FStarC.Errors.Msg
open FStarC.Class.Show

let info_at_pos env file row col : option (either string lident & typ & Range.range) =
    match TypeChecker.Common.id_info_at_pos !env.identifier_info file row col with
    | None -> None
    | Some info ->
      match info.identifier with
      | Inl bv -> Some (Inl (show bv.ppname), info.identifier_ty,
                       FStarC.Syntax.Syntax.range_of_bv bv)
      | Inr fv -> Some (Inr (FStarC.Syntax.Syntax.lid_of_fv fv), info.identifier_ty,
                       FStarC.Syntax.Syntax.range_of_fv fv)

(* Will attempt to enable certain printing flags to make x and y
 * visibly different. It will try to enable the least possible
 * subset of implicits, universes, effect_args and full_names.
 * It will also prioritize them in that order, prefering to show
 * a discrepancy of implicits before one of universes, etc.
 *)
let print_discrepancy (#a:Type) (#b:eqtype) (f : a -> b) (x : a) (y : a) : b & b =
    let print () : b & b & bool =
        let xs = f x in
        let ys = f y in
        xs, ys, xs <> ys
    in
    let rec blist_leq (l1 : list bool) (l2 : list bool) =
        match l1, l2 with
        | h1::t1, h2::t2 ->
            (not h1 || h2) && blist_leq t1 t2
        | [], [] ->
            true
        | _ ->
            failwith "print_discrepancy: bad lists"
    in
    let rec succ (l : list bool) : list bool =
        match l with
        | false::t -> true::t
        | true::t -> false::(succ t)
        | [] -> failwith ""
    in
    let full (l : list bool) : bool =
        List.for_all (fun b -> b) l
    in
    let get_bool_option (s:string) : bool =
        match Options.get_option s with
        | Options.Bool b -> b
        | _ -> failwith "print_discrepancy: impossible"
    in
    let set_bool_option (s:string) (b:bool) : unit =
        Options.set_option s (Options.Bool b)
    in
    let get () : list bool =
        let pi  = get_bool_option "print_implicits" in
        let pu  = get_bool_option "print_universes" in
        let pea = get_bool_option "print_effect_args" in
        let pf  = get_bool_option "print_full_names" in
        [pi; pu; pea; pf]
    in
    let set (l : list bool) : unit =
        match l with
        | [pi; pu; pea; pf] ->
          set_bool_option "print_implicits"   pi;
          set_bool_option "print_universes"   pu;
          set_bool_option "print_effect_args" pea;
          set_bool_option "print_full_names " pf
        | _ -> failwith "impossible: print_discrepancy"
    in
    let bas = get () in
    let rec go (cur : list bool) =
        match () with
        (* give up, nothing more we can do *)
        | () when full cur ->
            let xs, ys, _ = print () in
            xs, ys

        (* skip this configuration, we do not want to disable any flag
         * given by the user *)
        | () when not (blist_leq bas cur) ->
            go (succ cur)

        | () ->
            set cur;
            match print () with
            (* got a discrepancy! we're done *)
            | xs, ys, true ->
                xs, ys

            (* keep trying *)
            | _ ->
                go (succ cur)
    in
    Options.with_saved_options (fun () -> go bas)

let errors_smt_detail env
        (errs : list Errors.error)
        (smt_detail : Errors.error_message)
: list Errors.error
=
    let errs =
        errs
        |> List.map
          (fun (e, msg, r, ctx) ->
            let e, msg, r, ctx =
                let msg = msg @ smt_detail in
                if r = dummyRange
                then e, msg, Env.get_range env, ctx
                else let r' = Range.set_def_range r (Range.use_range r) in
                     if Range.file_of_range r' <> Range.file_of_range (Env.get_range env) //r points to another file
                     then
                       let msg =
                         let open FStarC.Pprint in
                         msg @ [doc_of_string ("Also see: " ^ Range.string_of_use_range r)
                               ; (if Range.use_range r <> Range.def_range r
                                  then doc_of_string ("Other related locations: " ^ Range.string_of_def_range r)
                                  else empty)]
                       in
                       e, msg, Env.get_range env, ctx
                     else e, msg, r, ctx
            in
            e, msg, r, ctx)
    in
    errs

let add_errors env errs =
    FStarC.Errors.add_errors (errors_smt_detail env errs [])

let log_issue env r (e, m) : unit =
 add_errors env [e, m, r, Errors.get_ctx ()]

let log_issue_text env r (e, m) : unit =
  log_issue env r (e, [Errors.text m])

let err_msg_type_strings env t1 t2 :(string & string) =
  print_discrepancy (N.term_to_string env) t1 t2

// let err_msg_type_docs env t1 t2 :(Pprint.document * Pprint.document) =

//   print_discrepancy (N.term_to_doc env) t1 t2

let err_msg_comp_strings env c1 c2 :(string & string) =
  print_discrepancy (N.comp_to_string env) c1 c2

(* Error messages for labels in VCs *)
let exhaustiveness_check = [
  FStarC.Errors.Msg.text "Patterns are incomplete"
]

let subtyping_failed : env -> typ -> typ -> unit -> error_message =
     fun env t1 t2 () ->
      //  let s1, s2 = err_msg_type_strings env t1 t2 in
      let ppt = N.term_to_doc env in
       [text "Subtyping check failed";
        prefix 2 1 (text "Expected type") (ppt t2) ^/^
        prefix 2 1 (text "got type") (ppt t1);
       ]

let ill_kinded_type = Errors.mkmsg "Ill-kinded type"

let unexpected_signature_for_monad #a env (rng:Range.range) (m:lident) k : a =
  Errors.raise_error rng Errors.Fatal_UnexpectedSignatureForMonad
    (format2 "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type -> WP a -> Effect); got %s"
    (show m) (N.term_to_string env k))

let expected_a_term_of_type_t_got_a_function env (rng:Range.range) msg (t:typ) (e:term) =
  Errors.raise_error rng Errors.Fatal_ExpectTermGotFunction
    (format3 "Expected a term of type \"%s\"; got a function \"%s\" (%s)"
    (N.term_to_string env t) (show e) msg)

let unexpected_implicit_argument =
  (Errors.Fatal_UnexpectedImplicitArgument, ("Unexpected instantiation of an implicit argument to a function that only expects explicit arguments"))

let expected_expression_of_type #a env (rng:Range.range) t1 e t2 : a =
  // let s1, s2 = err_msg_type_strings env t1 t2 in
  // MISSING: print discrepancy!
  let d1 = N.term_to_doc env t1 in
  let d2 = N.term_to_doc env t2 in
  let ed = N.term_to_doc env e in
  let open FStarC.Errors.Msg in
  Errors.raise_error rng Errors.Fatal_UnexpectedExpressionType [
    prefix 4 1 (text "Expected expression of type") d1 ^/^
    prefix 4 1 (text "got expression") ed ^/^
    prefix 4 1 (text "of type") d2
  ]

let expected_pattern_of_type env (t1 e t2 : term) =
  let s1, s2 = err_msg_type_strings env t1 t2 in
  (Errors.Fatal_UnexpectedPattern, (format3 "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\""
    s1 (show e) s2))

let basic_type_error env (rng:Range.range) eopt t1 t2 =
  let s1, s2 = err_msg_type_strings env t1 t2 in
  let open FStarC.Errors.Msg in
  let msg = match eopt with
    | None -> [
      prefix 4 1 (text "Expected type") (N.term_to_doc env t1) ^/^
      prefix 4 1 (text "got type") (N.term_to_doc env t2);
    ]
    | Some e -> [
      prefix 4 1 (text "Expected type") (N.term_to_doc env t1) ^/^
      prefix 4 1 (text "but") (N.term_to_doc env e) ^/^
      prefix 4 1 (text "has type") (N.term_to_doc env t2);
    ]
  in
  Errors.log_issue rng Errors.Error_TypeError msg

(* It does not make sense to use the same code for a catcheable and uncatcheable
error, but that's what this was doing. *)
let raise_basic_type_error #a env (rng:Range.range) eopt t1 t2 : a =
  let s1, s2 = err_msg_type_strings env t1 t2 in
  let open FStarC.Errors.Msg in
  let msg = match eopt with
    | None -> [
      prefix 4 1 (text "Expected type") (N.term_to_doc env t1) ^/^
      prefix 4 1 (text "got type") (N.term_to_doc env t2);
    ]
    | Some e -> [
      prefix 4 1 (text "Expected type") (N.term_to_doc env t1) ^/^
      prefix 4 1 (text "but") (N.term_to_doc env e) ^/^
      prefix 4 1 (text "has type") (N.term_to_doc env t2);
    ]
  in
  Errors.raise_error rng Errors.Error_TypeError msg

let occurs_check =
  (Errors.Fatal_PossibleInfiniteTyp, "Possibly infinite typ (occurs check failed)")

let constructor_fails_the_positivity_check env (d:term) (l:lid) =
  (Errors.Fatal_ConstructorFailedCheck, (format2 "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type"
    (show d) (show l)))

let inline_type_annotation_and_val_decl (l:lid) =
  (Errors.Fatal_DuplicateTypeAnnotationAndValDecl, (format1 "\"%s\" has a val declaration as well as an inlined type annotation; remove one" (show l)))

(* CH: unsure if the env is good enough for normalizing t here *)
let inferred_type_causes_variable_to_escape env t (x:bv) =
  (Errors.Fatal_InferredTypeCauseVarEscape, (format2 "Inferred type \"%s\" causes variable \"%s\" to escape its scope"
    (N.term_to_string env t) (show x)))

let expected_function_typ #a env (rng:Range.range) t : a =
  Errors.raise_error rng Errors.Fatal_FunctionTypeExpected [
      text "Expected a function.";
      prefix 2 1 (text "Got an expression of type:")
        (N.term_to_doc env t);
    ]

let expected_poly_typ env (f:term) t targ =
  (Errors.Fatal_PolyTypeExpected, (format3 "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\""
    (show f) (N.term_to_string env t) (N.term_to_string env targ)))

let disjunctive_pattern_vars (v1 v2 : list bv) =
  let vars v =
    v |> List.map show |> String.concat ", " in
  (Errors.Fatal_DisjuctivePatternVarsMismatch, (format2
    "Every alternative of an 'or' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")"
    (vars v1) (vars v2)))

let name_and_result c = match c.n with
  | Total t -> "Tot", t
  | GTotal t -> "GTot", t
  | Comp ct -> show ct.effect_name, ct.result_typ
  // TODO: ^ Use the resugaring environment to possibly shorten the effect name

let computed_computation_type_does_not_match_annotation #a env (r:Range.range) e c c' : a =
  let ppt = N.term_to_doc env in
  let f1, r1 = name_and_result c in
  let f2, r2 = name_and_result c' in
  Errors.raise_error r Errors.Fatal_ComputedTypeNotMatchAnnotation [
    prefix 2 1 (text "Computed type") (ppt r1) ^/^
    prefix 2 1 (text "and effect") (text f1) ^/^
    prefix 2 1 (text "is not compatible with the annotated type") (ppt r2) ^/^
    prefix 2 1 (text "and effect") (text f2)
  ]

let computed_computation_type_does_not_match_annotation_eq #a env (r:Range.range) e c c' : a =
  let ppc = N.comp_to_doc env in
  Errors.raise_error r Errors.Fatal_ComputedTypeNotMatchAnnotation [
    prefix 2 1 (text "Computed type") (ppc c) ^/^
    prefix 2 1 (text "does not match annotated type") (ppc c') ^/^
    text "and no subtyping was allowed";
  ]

let unexpected_non_trivial_precondition_on_term #a env f : a =
  Errors.raise_error env Errors.Fatal_UnExpectedPreCondition
    (format1 "Term has an unexpected non-trivial pre-condition: %s" (N.term_to_string env f))

let __expected_eff_expression (effname:string) (rng:Range.range) (e:term) (c:comp) (reason:option string) =
  let open FStarC.Class.PP in
  let open FStarC.Pprint in
  Errors.raise_error rng Errors.Fatal_ExpectedGhostExpression [
    text ("Expected a " ^ effname ^ " expression.");
    (match reason with
     | None -> empty
     | Some msg -> flow (break_ 1) (doc_of_string "Because:" :: words (msg ^ ".")));
    prefix 2 1 (text "Got an expression") (pp e) ^/^
    prefix 2 1 (text "with effect") (squotes (doc_of_string (fst <| name_and_result c))) ^^ dot;
  ]

let expected_pure_expression (rng:Range.range) (e:term) (c:comp) (reason:option string) =
  __expected_eff_expression "pure" rng e c reason

let expected_ghost_expression (rng:Range.range)(e:term) (c:comp) (reason:option string) =
  __expected_eff_expression "ghost" rng e c reason

let expected_effect_1_got_effect_2 (c1:lident) (c2:lident) =
  (Errors.Fatal_UnexpectedEffect, (format2 "Expected a computation with effect %s; but it has effect %s" (show c1) (show c2)))

let failed_to_prove_specification_of (l : lbname) (lbls : list string) =
  (Errors.Error_TypeCheckerFailToProve, (format2 "Failed to prove specification of %s; assertions at [%s] may fail" (show l) (lbls |> String.concat ", ")))

let warn_top_level_effect (rng:Range.range) : unit =
  Errors.log_issue rng
    Errors.Warning_TopLevelEffect
    "Top-level let-bindings must be total; this term may have effects"
