(*
   Copyright 2008-2026 Microsoft Research

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
module FStarC.Custard.Mono

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Class.Show
open FStarC.Class.Setlike
open FStarC.Syntax.Syntax

module Free  = FStarC.Syntax.Free
module Ident = FStarC.Ident
module PC    = FStarC.Parser.Const
module S     = FStarC.Syntax.Syntax
module SS    = FStarC.Syntax.Subst
module TcEnv = FStarC.TypeChecker.Env
module TcUtil = FStarC.TypeChecker.Util
module U     = FStarC.Syntax.Util
module N     = FStarC.TypeChecker.Normalize
module Prof  = FStarC.Custard.Prof

(* Custard reduces terms nobody wrote for it, and reduction need not
   terminate: with [zeta] on, which is the default, a recursive definition is
   unfolded without bound.  The failure mode is the worst kind -- not a wrong
   answer or a rejection, but a compiler that never finishes and never says
   why -- so *every* normalization Custard performs runs under a step budget.
   [Extract.norm_bounded] is the same wrapper reading the request chain of
   section 3.6 out of its own state; this one is for the callers below the
   extractor, which have no state to read.

   A budget nests by saving and restoring, so wrapping a call that is already
   inside one is harmless: the inner limit applies and the outer count
   resumes where it left off. *)

(* The chain is the whole diagnostic value of the message -- a budget is
   exhausted on a *term*, and which term that is is a question about the
   definition being extracted, not about this module.  This module is below
   the extractor and cannot ask it, so the extractor leaves a way to ask
   behind.  Nothing installs it in a plugin or a unit-test run, hence the
   default that reports nothing rather than a dependency that would have to
   be threaded through every arity test.

   Without it a budget exhausted in a *type-level* normalization -- an arity
   spine, a binder's kind -- named no definition at all, which is what the
   EverParse report ran into on
   [LowParse.Pulse.Recursive.validate_recursive_step_count]: the term was
   printed and the reader still had to bisect the module to learn what was
   being extracted when it appeared. *)
let chain_reporter : ref (unit -> ML (list Pprint.document)) =
  mk_ref (fun () -> [])

let norm_bounded (env:TcEnv.env) (what:string) (steps:list TcEnv.step) (t:typ)
  : ML typ =
  try Prof.timed "Mono.norm" (fun () ->
        N.with_budget (FStarC.Options.custard_norm_budget ())
                      (fun () -> N.normalize steps env t))
  with
  | N.Budget_exceeded ->
    FStarC.Errors.raise_error0 FStarC.Errors.Codes.Error_CustardFuelExhausted ([
      Pprint.arbitrary_string
        ("Custard exceeded --custard_norm_budget (" ^
         show (FStarC.Options.custard_norm_budget ()) ^
         " reduction steps) while normalizing " ^ what ^ ".");
      Pprint.arbitrary_string
        ("The term being normalized, before reduction, was: " ^
         FStarC.Syntax.Print.term_to_string' (TcEnv.dsenv env) t)
    ] @ (!chain_reporter) ())

(* Section 19.7.  A normalizer does not promise to hand back a term whose
   outermost node is the one you are looking for.  It hands back one that
   *means* what you are looking for, and F* has two nodes that mean nothing at
   all: [Tm_ascribed], which records a type the elaborator wrote down, and
   [Tm_refine], which records a proposition erased long before any of this.
   [SS.compress] resolves unification variables and delayed substitutions and
   strips neither.

   That is not a corner case here, it is the common case.  Over one extraction
   of EverParse's [jump_header], six of the terms this module tested for
   [Tm_arrow] were arrows wrapped in an ascription, and twenty-four more were
   refinements likewise wrapped.  Reading the tag off the wrapper silently
   answers "not an arrow" and "not an arity", and both answers are wrong in
   the direction that miscompiles rather than the direction that rejects.

   So no shape test in this module reads a tag directly.  They all go through
   here, which is a fixed point rather than one peel: an ascription can hide a
   refinement and a refinement's base can be ascribed, and the two have to
   alternate away.  The bound is for the same reason every other loop in
   Custard has one -- this runs on terms nobody wrote for it. *)
let rec strip_aux (fuel:int) (t:typ) : ML typ =
  let t = SS.compress t in
  if fuel <= 0 then t
  else match t.n with
       | Tm_ascribed _ -> strip_aux (fuel - 1) (U.unascribe t)
       | Tm_refine _ -> strip_aux (fuel - 1) (U.unrefine t)
       | _ -> t

let strip (t:typ) : ML typ = strip_aux 16 t

let bclass_to_string (c:bclass) : string =
  match c with
  | Mono -> "Mono"
  | Poly -> "Poly"
  | Dropped -> "Dropped"

instance showable_bclass : showable bclass = { show = bclass_to_string }

(* Rule 2, first half: [{| c |}] desugars to an implicit binder whose qualifier
   is [Meta tcresolve]. *)
let is_tcresolve_binder (b:binder) : ML bool =
  match b.binder_qual with
  | Some (Meta t) ->
    (* The tactic term may have been eta-expanded or applied, so look at the
       head. *)
    let hd, _ = U.head_and_args_full t in
    U.is_fvar PC.tcresolve_lid hd
  | _ -> false

(* Rule 2, second half: a dictionary passed explicitly rather than through
   [{| |}] still has a class type. *)
let is_tcclass_binder (env:TcEnv.env) (b:binder) : ML bool =
  let hd, _ = U.head_and_args_full (U.unrefine (SS.compress b.binder_bv.sort)) in
  match (U.un_uinst hd).n with
  | Tm_fvar fv -> TcEnv.fv_has_attr env fv PC.tcclass_lid
  | _ -> false

(* Rule 2's opt-out.  [@@custard_no_monomorphize] on the class says that its
   instances are runtime values and not compile-time dictionaries, which is the
   truth about [embedding]: [e_list e_sigelt] is computed, stored and passed
   around like any other value, and there is nothing to specialize on.  Without
   the opt-out every function that takes one -- [unembed] is the one that
   matters -- rejects each of its callers under section 3.2b.

   It is the *binder's type* that is consulted, not how the binder was written,
   so it applies to a [{| |}] binder and an explicit one alike. *)
let is_unspecializable_binder (env:TcEnv.env) (b:binder) : ML bool =
  let hd, _ = U.head_and_args_full (U.unrefine (SS.compress b.binder_bv.sort)) in
  match (U.un_uinst hd).n with
  | Tm_fvar fv -> TcEnv.fv_has_attr env fv PC.custard_no_monomorphize_attr
  | _ -> false

(* Does this sort classify types rather than values -- [Type], but also
   [Type -> Type], the kind of the [m] in [class monad (m:Type -> Type)]?

   [eqtype] and [Type0] are abbreviations, not [Tm_type]s, so the sort has to
   be unfolded before it can be recognised.  Getting this wrong is not
   harmless: the parameters of an inductive are exactly its type binders, and
   a missed one becomes an unbound type variable in the emitted type -- or,
   for a higher kind, an unbound *term* variable, because the binder is then
   taken for a runtime one and its uses are compiled as values. *)
let rec is_arity_aux (normed:bool) (env:TcEnv.env) (t:typ) : ML bool =
  let t = strip t in
  match t.n with
  | Tm_type _ -> true
  (* Through [arrow_formals_comp], which opens the binders: normalizing a
     codomain with loose de Bruijn indices in it fails outright. *)
  | Tm_arrow _ ->
    let bs, c = U.arrow_formals_comp t in
    is_arity_aux false (TcEnv.push_binders env bs) (U.comp_result c)
  (* Only a name can still be hiding one, and only normalization can tell.
     Paying for it once, at the end, rather than at every step: this runs on
     every binder of every definition the extraction visits. *)
  | Tm_fvar _ | Tm_app _ | Tm_uinst _ ->
    not normed &&
    is_arity_aux true env
      (norm_bounded env "a binder's sort"
                    [TcEnv.AllowUnboundUniverses; TcEnv.EraseUniverses;
                     TcEnv.Beta; TcEnv.Iota;
                     TcEnv.UnfoldUntil delta_constant]
                    t)
  | _ -> false

let is_arity (env:TcEnv.env) (t:typ) : ML bool =
  Prof.timed "Mono.is_arity" (fun () -> is_arity_aux false env t)

let is_type_binder (env:TcEnv.env) (b:binder) : ML bool =
  is_arity env b.binder_bv.sort

(* Of the sorts [is_arity] accepts, the ones of kind [Type] exactly.

   The distinction is the target's, not F*'s.  Every arity binder is erased
   from the value world alike -- that is [is_type_binder] -- but only a binder
   of kind [Type] can become a *parameter* of a target type: neither OCaml nor
   C has a type variable standing for a type constructor, so the [m] of [class
   monad (m:Type -> Type)] can be neither declared nor passed.  Uniform
   compilation (section 5.0) is what makes dropping it sound: [monad m] is
   represented the same way whatever [m] is, and every field whose type
   mentions [m] is already [any].  What is left is a parameterless [monad],
   which is exactly what the fields say. *)
let rec is_star_aux (normed:bool) (env:TcEnv.env) (t:typ) : ML bool =
  match (strip t).n with
  | Tm_type _ -> true
  | Tm_fvar _ | Tm_app _ | Tm_uinst _ ->
    not normed &&
    is_star_aux true env
      (norm_bounded env "a binder's kind"
                    [TcEnv.AllowUnboundUniverses; TcEnv.EraseUniverses;
                     TcEnv.Beta; TcEnv.Iota;
                     TcEnv.UnfoldUntil delta_constant]
                    t)
  | _ -> false

(* Section 18.2.  An arity that is not [Type] itself still denotes a single
   target type, provided every argument it takes is a *value*: values are
   erased from the target's type language, so [b : header -> Type] has one
   representation for every [h] and [b h] is that representation.  Only an
   argument of kind [Type] makes it a real type constructor -- the [m] of
   [class monad (m:Type -> Type)] -- and that is what neither OCaml nor C can
   name.

   This is what [Prims.dtuple2 header (fun h -> payload h)] needs.  Dropping
   [b] leaves the second field typed by a name that no parameter binds, so it
   is [any]; kept, it is an ordinary type parameter, and a monomorphizing run
   fills it in with [payload].  EverParse's whole validate/parse/serialize
   idiom is a value-indexed [dtuple2] and was [any] throughout.

   The arrow is looked for *syntactically*, before anything is normalized.
   [is_type_param] is asked about every binder of every definition the
   extraction visits, the overwhelming majority of which are values, and
   [is_arity] on a sort like [int] costs a normalization.  [U.arrow_formals]
   of a non-arrow is [([], t)], so those stop at [Cons?] having done nothing.
   The cost of that is an arity hidden behind an abbreviation, which is not
   recognized; it is the same trade [is_star_aux] makes one level up. *)
let is_value_indexed_arity (env:TcEnv.env) (t:typ) : ML bool =
  let bs, res = U.arrow_formals t in
  Cons? bs &&
  is_star_aux false env res &&
  bs |> List.for_all (fun (b:binder) -> not (is_arity env b.binder_bv.sort))

let is_type_param (env:TcEnv.env) (b:binder) : ML bool =
  is_star_aux false env b.binder_bv.sort ||
  is_value_indexed_arity env b.binder_bv.sort

(* Rule 1: a non-informative binder carries no runtime value, so it is deleted
   rather than passed.  The *unit-shaped* ones are excluded here, and
   [U.is_unit] is the right test because it treats [unit], [squash p] and
   [_:unit{p}] as the one thing they are.  They are deleted too, but only from
   a *signature*, by [classify] below, where the codomain is in hand: a unit
   binder is also how F* writes a thunk, and dropping the wrong one turns an
   impure function into a value whose effect then runs at module
   initialization.  This predicate is the one applied to the binders that come
   from a definition's own lambdas rather than from its type, where there is no
   codomain to consult and so no way to tell a thunk apart. *)
let is_dropped_binder (env:TcEnv.env) (b:binder) : ML bool =
  let sort = b.binder_bv.sort in
  not (U.is_unit sort) &&
  not (is_type_binder env b) &&
  Prof.timed "Mono.must_erase" (fun () ->
    TcUtil.must_erase_for_extraction env sort)

let is_unit_binder (b:binder) : ML bool = U.is_unit b.binder_bv.sort

(* The term-level counterpart of [is_type_binder]: a spine whose head no
   declaration describes is filtered with this instead.  Structural, like the
   ML extraction's [is_type]: what a term denotes is decided by its head. *)
let rec is_type_term (env:TcEnv.env) (t:term) : ML bool =
  match (SS.compress t).n with
  | Tm_type _
  | Tm_arrow _
  | Tm_refine _ -> true
  | Tm_uinst (t, _)
  | Tm_ascribed {tm=t}
  | Tm_meta {tm=t} -> is_type_term env t
  | Tm_name bv -> is_arity env bv.sort
  | Tm_fvar fv ->
    (match TcEnv.try_lookup_lid env (S.lid_of_fv fv) with
     | Some ((_, ty), _) -> is_arity env ty
     | None -> false)
  | Tm_app _ -> is_type_term env (fst (U.head_and_args_full t))
  | Tm_abs _ ->
    let bs, body, _ = U.abs_formals t in
    is_type_term (TcEnv.push_binders env bs) body
  | _ -> false

let is_erased_binder (env:TcEnv.env) (b:binder) : ML bool =
  is_type_binder env b || is_dropped_binder env b

(* The guard that makes deleting a binder from a *definition* safe.  Two things
   can go wrong.  Deleting every binder turns the definition into a value, so
   its body runs at module initialization instead of when it is called, and any
   partial application of it at a call site silently becomes a saturated one.
   And a unit-shaped binder in front of an impure codomain is
   indistinguishable, from the type alone, from the thunk F* writes the same
   way -- [unit -> ML a] and [squash p -> ML a] are the same arrow.

   So the last binder is retained when it is dropped and either the definition
   would otherwise become a value, or it is unit-shaped and the codomain is
   impure.  It carries no information -- its argument is [()] either way, see
   [unit_binders] -- it just keeps the definition a function.  Both the
   signature and the call sites derive their filtering from the same F* type,
   so they agree without communicating.

   The first clause does not test purity, even though a pure body may be run at
   initialization without changing what the program computes, because F*'s
   notion of purity is not Custard's: a Pulse [fn f () : stt unit] is a [Tot]
   function returning an [stt] value, and section 7.2 is what makes it an
   impure arrow.  Keeping the arity is the answer that does not depend on
   which of the two notions is meant. *)
let keep_thunk (env:TcEnv.env) (bs:binders) (c:comp) (flags:list bool) : ML (list bool) =
  let last (l:list 'a) : ML (option 'a) =
    match List.rev l with x :: _ -> Some x | [] -> None in
  let becomes_value = Cons? flags && List.for_all (fun b -> b) flags in
  let is_thunk =
    not (U.is_pure_or_ghost_comp c) &&
    (match last bs with Some b -> is_unit_binder b | None -> false) in
  if last flags = Some true && (becomes_value || is_thunk)
  then (match List.rev flags with
        | _ :: rest -> List.rev (false :: rest)
        | [] -> flags)
  else flags

(* A constructor is a value, so neither hazard applies to it: deleting all of
   its arguments is exactly what a nullary constructor is.  The one case that
   would still be wrong is an impure one, which does not exist. *)
let erased_binders (env:TcEnv.env) (t:typ) : ML (list bool) =
  let bs, _ = U.arrow_formals_comp t in
  bs |> List.map (is_erased_binder env)

(* [U.arrow_formals_comp] flattens nested arrows, but an abbreviation is not an
   arrow node: it stops there.  A declaration whose type is written
   [a:hash_alg -> compute_st a], with [compute_st] an [inline_for_extraction]
   abbreviation hiding nine more binders, therefore looks like a one-binder
   function.  Every argument past the first is then unclassified, and the
   permissive default -- leave the surplus spine alone -- passes the erased
   ones at runtime.  The caller, whose own erased binders were correctly
   deleted, has no such values to send, so the call names variables that no
   longer exist: EverCrypt's [compute] is the case that showed this up.

   So the spine is walked with an unfolding step at each name, exactly as
   [Extract.extract_letbinding]'s result-type peel does, and bounded for the
   same reason -- one unfolding can expose another, and a self-referential
   abbreviation must not spin.  Only a *total* codomain is peeled: an effectful
   one is where the function ends, whatever it abbreviates. *)
let rec arrow_formals_unfold_aux (fuel:int) (env:TcEnv.env) (t:typ)
  : ML (binders & comp) =
  let bs, c = U.arrow_formals_comp t in
  if fuel <= 0 || not (U.is_total_comp c) then bs, c
  else
    let env = TcEnv.push_binders env bs in
    let r = norm_bounded env "an arrow spine"
              [TcEnv.AllowUnboundUniverses; TcEnv.EraseUniverses;
               TcEnv.Beta; TcEnv.Weak; TcEnv.HNF;
               TcEnv.UnfoldUntil delta_constant]
              (U.comp_result c) in
    (* Section 19.7: the normalizer returns the arrow inside the ascription
       the elaborator wrote, and the tag of an ascription is not [Tm_arrow].
       This is the whole of the EverParse [jumper] miscompilation. *)
    let r = strip r in
    match r.n with
    | Tm_arrow _ ->
      let bs', c' = arrow_formals_unfold_aux (fuel - 1) env r in
      bs @ bs', c'
    | _ -> bs, c

let arrow_formals_unfold (env:TcEnv.env) (t:typ) : ML (binders & comp) =
  Prof.timed "Mono.arrow_formals_unfold" (fun () ->
    arrow_formals_unfold_aux 8 env t)

(* {!erased_binders} against the *whole* arrow spine, abbreviations included.

   Which of the two a caller wants depends on what it is filtering.  Filtering
   a definition's own binders, or a type's own arrows, wants the plain one:
   the binders in hand came from [arrow_formals_comp] and the flags have to be
   positionally aligned with them.  Filtering a *call spine* wants this one,
   because the spine is as long as the call is, and a call may go straight
   through an abbreviation that the type stops at.

   [classify], [unit_binders] and [type_binders] already unfold, which is why
   a call through a name is right and a call through a *variable* was not: the
   local's sort is the abbreviation as written, so [erased_binders] saw no
   arrows past it, every argument beyond them was left alone, and the erased
   ones went out at runtime -- as a [()] where the callee had deleted the
   parameter, so the whole spine shifted by one.  A [fn rec] hands its own
   recursive call to the body as a closure, which is exactly a local of
   abbreviated arrow type; section 18.1. *)
let erased_binders_unfold (env:TcEnv.env) (t:typ) : ML (list bool) =
  let bs, _ = arrow_formals_unfold env t in
  bs |> List.map (is_erased_binder env)

(* The sorts of the binders [erased_binders] retains, in order: exactly what a
   caller still has to supply.  Used to type the binders introduced when a
   primitive has to be eta-expanded, which would otherwise be [TAny]. *)
let retained_sorts (env:TcEnv.env) (t:typ) : ML (list typ) =
  let bs, _ = U.arrow_formals_comp t in
  bs |> List.filter (fun b -> not (is_erased_binder env b))
     |> List.map (fun b -> b.binder_bv.sort)

(* The binders of [t] that are kept but carry no value, so a call site may --
   and should -- pass [()] rather than whatever the source supplies.

   Two kinds.  A unit-shaped binder is the one rule 1 declines to delete, and
   what the source supplies for it can be a [Prims.magic ()] that aborts at
   runtime, or an arbitrarily expensive piece of ghost code.  A *type* binder
   is normally deleted outright, but {!keep_thunk} puts the last one back when
   deleting it would turn the definition into a value; what the source supplies
   for that one is a type, and a type is not a term.  Passing it produces
   either an [Obj.magic ()] (when the argument is a concrete type, which
   happens to work) or a reference to a type variable in value position (when
   it is not, which does not). *)
let unit_binders (env:TcEnv.env) (t:typ) : ML (list bool) =
  let bs, _ = arrow_formals_unfold env t in
  bs |> List.map (fun b -> U.is_unit b.binder_bv.sort || is_type_binder env b)

let type_binders (env:TcEnv.env) (t:typ) : ML (list bool) =
  let bs, _ = arrow_formals_unfold env t in
  bs |> List.map (is_type_binder env)

(* The binders that become parameters of the target type, positionally: a
   higher-kinded one is erased like any other type binder but is not one of
   them (see {!is_type_param}). *)
let type_params (env:TcEnv.env) (t:typ) : ML (list bool) =
  let bs, _ = U.arrow_formals_comp t in
  bs |> List.map (is_type_param env)

(* Rule 4b (section 30.9).  A binder whose type is an inductive one of whose
   constructors takes a *type* -- [Mkbundle : (b_impl_type: Type0) -> (b_dflt:
   b_impl_type) -> bundle] -- cannot be a runtime parameter, because there is
   no runtime representation for it to have: its own contents decide the
   representation, and taking it apart binds a type to a variable, which is
   exactly what error 364 reports.  Such a binder is [Mono] whether or not
   anyone wrote the attribute, because the alternative is not a slower
   program but no program.

   The inductive's own *parameters* do not count.  [Cons : (a:Type) -> a ->
   list a -> list a] takes a type and [list int] is an ordinary runtime value;
   what matters is a type that a constructor stores, which is the arguments
   past the first [num_ty_params]. *)
let ctor_stores_type (env:TcEnv.env) (l:Ident.lident) : ML bool =
  match TcEnv.lookup_sigelt env l with
  | Some ({ sigel = Sig_datacon { t; num_ty_params } }) ->
    let bs, _ = U.arrow_formals t in
    if List.length bs <= num_ty_params then false
    else
      (* Section 32.6.  A stored [Type0] is only an existential when some
         *later* field's type mentions it.  Storing one that nothing depends
         on is not: the field is erased like any other type (section 5.1) and
         what remains has a perfectly uniform representation.  Rule 4b used to
         ask only whether a type was stored, and so made [| D : (ty:Type0) ->
         len:UInt32.t -> desc] unusable as a runtime value for no reason.

         The condition is the one section 30.4's warning already states in
         prose -- "a field of kind Type0 whose siblings' types mention it" --
         which is what makes the representation depend on the contents. *)
      let fields = List.splitAt num_ty_params bs |> snd in
      let rec scan (bs:list binder) : ML bool =
        match bs with
        | [] -> false
        | b :: rest ->
          (match (SS.compress b.binder_bv.sort).n with
           | Tm_type _ ->
             rest |> List.existsb (fun (b2:binder) ->
               elems (Free.names b2.binder_bv.sort)
               |> List.existsb (fun v -> bv_eq v b.binder_bv))
             || scan rest
           | _ -> scan rest) in
      scan fields
  | _ -> false

(* Section 32.6.  Which constructor and which field made a type an
   existential, for the diagnostic: error 364 otherwise reports rule 4b's
   *consequence* -- "there is nothing to specialize on" -- and sends the
   reader to look for an annotation, when the cause is a property of the type
   that no annotation changes. *)
let existential_field (env:TcEnv.env) (b:binder)
  : ML (option (Ident.lident & Ident.lident)) =
  let hd, _ = U.head_and_args_full (U.unrefine (SS.compress b.binder_bv.sort)) in
  match (U.un_uinst hd).n with
  | Tm_fvar fv ->
    (match TcEnv.lookup_sigelt env (S.lid_of_fv fv) with
     | Some ({ sigel = Sig_inductive_typ { ds } }) ->
       let rec first (ds:list Ident.lident) : ML (option (Ident.lident & Ident.lident)) =
         match ds with
         | [] -> None
         | c :: ds' ->
           if not (ctor_stores_type env c) then first ds'
           else
             (match TcEnv.lookup_sigelt env c with
              | Some ({ sigel = Sig_datacon { t; num_ty_params } }) ->
                let bs, _ = U.arrow_formals t in
                let fields = if List.length bs <= num_ty_params then []
                             else List.splitAt num_ty_params bs |> snd in
                let rec pick (bs:list binder) : ML (option Ident.lident) =
                  match bs with
                  | [] -> None
                  | b :: rest ->
                    (match (SS.compress b.binder_bv.sort).n with
                     | Tm_type _ when
                         rest |> List.existsb (fun (b2:binder) ->
                           elems (Free.names b2.binder_bv.sort)
                           |> List.existsb (fun v -> bv_eq v b.binder_bv)) ->
                       Some (Ident.lid_of_ids [b.binder_bv.ppname])
                     | _ -> pick rest) in
                (match pick fields with
                 | Some f -> Some (c, f)
                 | None -> first ds')
              | _ -> first ds')
       in first ds
     | _ -> None)
  | _ -> None

let is_type_carrying_binder (env:TcEnv.env) (b:binder) : ML bool =
  let hd, _ = U.head_and_args_full (U.unrefine (SS.compress b.binder_bv.sort)) in
  match (U.un_uinst hd).n with
  | Tm_fvar fv ->
    (match TcEnv.lookup_sigelt env (S.lid_of_fv fv) with
     | Some ({ sigel = Sig_inductive_typ { ds } }) ->
       ds |> List.existsb (ctor_stores_type env)
     | _ -> false)
  | _ -> false

(* [demanded] is section 30.11's rule 4c: names that something marked
   [@@custard_compile_time] is applied to, computed from the *body* and so
   supplied by the caller, since a classification otherwise only sees a type.
   They are seeded as [Mono] before rule 5's fixpoint, which is the point --
   the demand has to propagate to whatever the demanded binder's type mentions
   exactly as a written annotation would. *)
let classify_demand (env:TcEnv.env) (attrs:list attribute) (t:typ)
                    (demanded:list int) : ML (list bclass) =
  let bs, comp = arrow_formals_unfold env t in
  let all_mono = U.has_attribute attrs PC.monomorphize_attr in
  let mono_types = Options.custard_monomorphize_types () in
  let init (i:int) (b:binder) : ML bclass =
    if is_dropped_binder env b || is_unit_binder b                (* rule 1 *)
    then Dropped
    else if U.has_attribute b.binder_attrs PC.monomorphize_attr   (* rule 3 *)
    then Mono
    (* Rule 2's opt-out beats the rules that infer [Mono], and loses to the
       one that is written on the binder itself: a class can say that it is
       not a compile-time dictionary, but it cannot overrule a specific
       binder that asks to be specialized anyway. *)
    else if is_unspecializable_binder env b
    then Poly
    else if all_mono                                              (* rule 3 *)
    || is_tcresolve_binder b                                      (* rule 2 *)
    || is_tcclass_binder env b                                    (* rule 2 *)
    || (mono_types && is_type_binder env b)                           (* rule 4 *)
    || is_type_carrying_binder env b                             (* rule 4b *)
    || List.mem i demanded                                       (* rule 4c *)
    then Mono
    else Poly
  in
  let cs = List.mapi init bs in
  (* Rule 5: if [b_j] is Mono and [b_i] is free in [b_j]'s type, [b_i] becomes
     Mono too.  Iterate to a fixpoint; the set only grows and is bounded by the
     number of binders, so at most [n] passes are needed. *)
  let bcs = List.zip bs cs in
  let pass (bcs:list (binder & bclass)) : ML (bool & list (binder & bclass)) =
    let needed =
      bcs |> List.collect (fun (b, c) ->
        match c with
        | Mono -> elems (Free.names b.binder_bv.sort)
        | _ -> [])
    in
    let changed = mk_ref false in
    let bcs = bcs |> List.map (fun (b, c) ->
      match c with
      | Mono | Dropped -> (b, c)
      | Poly ->
        if needed |> List.existsb (fun v -> bv_eq v b.binder_bv)
        then (changed := true; (b, Mono))
        else (b, Poly))
    in
    (!changed, bcs)
  in
  let rec fixpoint (n:int) (bcs:list (binder & bclass)) : ML (list (binder & bclass)) =
    if n <= 0 then bcs
    else let changed, bcs = pass bcs in
         if changed then fixpoint (n - 1) bcs else bcs
  in
  let bcs = fixpoint (List.length bs) bcs in
  (* A type binder that came out of the fixpoint still [Poly] is compiled
     uniformly (section 5.0), so it carries nothing at runtime and is deleted
     from the signature and from every call site -- exactly like an erased
     value binder.  This has to happen *after* the fixpoint, or rule 5 could
     not promote it to [Mono] when a [Mono] binder's type mentions it. *)
  let cs = bcs |> List.map (fun (b, c) ->
    match c with
    | Poly -> if is_type_binder env b then Dropped else Poly
    | c -> c) in
  (* Same guard as [erased_binders]: keep the last binder rather than turn the
     definition into a value or delete what may be a thunk.  (A definition all
     of whose binders are [Mono] has the same problem and would need thunking
     to fix; that is a known gap.) *)
  let flags = keep_thunk env bs comp (cs |> List.map Dropped?) in
  List.zip cs flags |> List.map (fun (c, dropped) ->
    match c with
    | Dropped -> if dropped then Dropped else Poly
    | c -> c)

(* Section 19.4.  [classify] reads a definition's binders off its *type*, and
   an abbreviation stops that type short of the definition's real arity: the
   [jumper p] of LowParse is four binders that [unit -> jumper p] shows as
   one.  [arrow_formals_unfold] exists to unfold past exactly that, and does
   not always manage it -- the abbreviation may not be reducible in the
   environment the classification runs in.

   The definition itself never had this problem, because it works from its
   *lambda*, which has every binder written out.  [Extract.extract_letbinding]
   says so directly: a binder past the end of the classification is filtered
   by [is_erased_binder] on the spot.  A call site had no such rule, so it
   passed the erased arguments the definition had deleted -- section 18.1's
   miscompilation once more, reached by neither the variable path nor a
   missing declaration but by a classification that is simply too short.

   So the extension happens here, once, in the same order and by the same
   predicate.  Every consumer of a classification -- [split_mono_args],
   [call_unit_flags], [call_type_args] -- then agrees with the definition
   without knowing that anything was extended, which is the property that was
   missing: the two sides have to be derived from one list, not from two lists
   that usually coincide.

   Only [is_erased_binder] and not [is_unit_binder], deliberately: the
   definition keeps a unit-shaped binder past its classification, so a call
   site must keep passing one. *)
let classify (env:TcEnv.env) (attrs:list attribute) (t:typ) : ML (list bclass) =
  classify_demand env attrs t []

(* Section 30.14.  A view of a type keeping only what can reach the emitted
   code: refinements gone, and a computation reduced to its result.  It is used
   to answer "does this binder still occur?" and for nothing else -- it is not
   a type, and nothing is compiled from it.

   The two omissions are the two ways a specification hides inside a signature.
   A refinement is a proposition.  A computation's pre- and postconditions are
   slprops, and Pulse writes the interesting half of a signature there: the
   [s] of [impl_serialize] occurs exactly once, inside a [pure (...)] in a
   postcondition, and it is 9 MB.

   Descending through arrows and refinements only is deliberate.  Anything else
   is left whole, so a name that occurs somewhere this does not understand is
   reported as occurring, which is the safe direction. *)
let rec observable (t:typ) : ML typ =
  match (SS.compress t).n with
  | Tm_refine {b} -> observable b.sort
  | Tm_ascribed {tm} -> observable tm
  | Tm_arrow {b; comp} ->
    let b = { b with binder_bv = { b.binder_bv with sort = observable b.binder_bv.sort } } in
    U.arrow [b] (S.mk_Total (observable (U.comp_result comp)))
  | _ -> t

(* Section 30.14.  A parameter that nothing observable depends on.

   [is_dropped_binder] asks whether a binder's *type* carries information.
   This asks the other question: whether anything left in the program still
   mentions it.  A parameter that occurs neither in the body nor in
   {!observable} of the rest of the signature cannot influence a single byte of
   the output, and the cost of keeping it is not the parameter -- it is that a
   [Mono] one is specialized on, so its argument is normalized, rendered into a
   key and compared.  Round 32 measured 1.2 s of that for an argument that
   provably could not matter.

   The body test is what makes it sound.  A parameter absent from the type can
   still be read at run time, and deleting one of those is section 18.1's
   miscompilation; the type test alone would do exactly that. *)
let dead_binders (env:TcEnv.env) (t:typ) (d:term) : ML (list int) =
  let bs_t, comp = arrow_formals_unfold env t in
  let bs_d, body, _ = U.abs_formals d in
  let live_in_body = Free.names body in
  let n = List.length bs_t in
  let rec tail (i:int) (bs:binders) : binders =
    if i <= 0 then bs else match bs with [] -> [] | _ :: bs -> tail (i - 1) bs in
  let res_names = elems (Free.names (observable (U.comp_result comp))) in
  (* Section 18.1's thunk again.  The last binder of a definition is the one
     that decides whether it is a function at all, and a unit-shaped last
     binder in front of an impure codomain is a thunk whose whole purpose is to
     be absent from both the body and the rest of the type.  Deleting one turns
     a suspended computation into a run-once value.  So the last binder is
     never dead, and asking costs nothing. *)
  let rec go (i:int) : ML (list int) =
    if i >= n - 1 then []
    else
      let bt = List.nth bs_t i in
      let later = tail (i + 1) bs_t |> List.collect (fun (b:binder) ->
                    elems (Free.names (observable b.binder_bv.sort))) in
      let in_type = (later @ res_names) |> List.existsb (fun v -> bv_eq v bt.binder_bv) in
      (* The type can have more binders than the lambda: a projector for
         [class monad] is written as four abstractions over an arrow of six,
         and a record field's own arguments are inside the [match].  Those
         positions have no binder in the body to ask about, so they are live.
         Reading [in_body] as [false] there deleted [mbind]'s first argument. *)
      let in_body =
        List.length bs_d <= i ||
        mem (List.nth bs_d i).binder_bv live_in_body in
      (if in_type || in_body then [] else [i]) @ go (i + 1)
  in
  go 0

let classify_def (env:TcEnv.env) (attrs:list attribute) (t:typ) (def:option term)
                 (demanded:list int)
  : ML (list bclass) =
  let cs = classify_demand env attrs t demanded in
  let cs =
    match def with
    | None -> cs
    | Some d ->
      let dead = dead_binders env t d in
      cs |> List.mapi (fun i c ->
        (* Only a [Mono] binder.  A [Mono] argument is not passed at run time
           already -- it is a key -- so turning one into [Dropped] removes the
           specialization and nothing else, and the emitted signature is
           unchanged.  Doing the same to a [Poly] binder would delete a
           parameter callers still pass: [RetArity.f]'s [frame] and [post] are
           unread and unmentioned, and are part of its ABI all the same. *)
        if c = Mono && List.mem i dead then Dropped else c) in
  match def with
  | None -> cs
  | Some d ->
    let bs, _, _ = U.abs_formals d in
    let rec extra (n:int) (bs:binders) : ML (list bclass) =
      match bs with
      | [] -> []
      | b :: bs ->
        if n > 0 then extra (n - 1) bs
        else (if is_erased_binder env b then Dropped else Poly) :: extra 0 bs in
    cs @ extra (List.length cs) bs

let has_mono (cs:list bclass) : ML bool =
  cs |> List.existsb Mono?

let has_dropped (cs:list bclass) : ML bool =
  cs |> List.existsb Dropped?
