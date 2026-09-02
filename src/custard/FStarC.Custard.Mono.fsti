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

(** Classification of a definition's binders into monomorphized and
    polymorphic ones -- section 3.1 of doc/ref/custard.md. *)
module FStarC.Custard.Mono

open FStarC
open FStarC.Effect
open FStarC.Syntax.Syntax

module Ident = FStarC.Ident
module TcEnv = FStarC.TypeChecker.Env

type bclass =
  (* Substituted away at specialization time; one copy of the definition is
     emitted per distinct argument. *)
  | Mono
  (* Kept as a parameter of the specialized definition. *)
  | Poly
  (* Non-informative (section 5.1): the binder is deleted from the specialized
     definition's signature, and the corresponding argument is deleted from
     every call site.  This is rule 1 of section 3.1. *)
  | Dropped

(** A callback the extractor installs so that this module's errors can report
    the request chain of section 3.6.  Everything here runs below the
    extractor and so has no state to read it from; the default reports
    nothing.  See {!norm_bounded}. *)
val chain_reporter : ref (unit -> ML (list FStarC.Pprint.document))

(** Normalize under [--custard_norm_budget], raising
    [Error_CustardFuelExhausted] rather than running forever.  Every
    normalization Custard performs goes through this or through
    [Extract.norm_bounded], which is the same thing with a request chain
    attached; see section 3.6. *)
val norm_bounded (env:TcEnv.env) (what:string) (steps:list TcEnv.step) (t:typ)
  : ML typ

(** [strip t] peels the nodes that carry no meaning -- [Tm_ascribed] and
    [Tm_refine] -- until neither is outermost, compressing as it goes.  A
    normalizer returns a term that *means* an arrow, not necessarily one whose
    tag is [Tm_arrow], so every shape test in this module goes through here.
    Section 19.7. *)
val strip (t:typ) : ML typ


val bclass_to_string : bclass -> string

instance val showable_bclass : Class.Show.showable bclass

(** True when a binder carries no runtime value, either because it is a type
    (types are compiled uniformly, section 5.0, so a type argument cannot
    change any layout) or because its sort is non-informative (section 5.1).

    Custard decides deletion with this predicate alone, and never by looking at
    whether a binder is implicit or explicit.  The implicit/explicit
    distinction is a source-level convenience with no bearing on what has to
    exist at runtime, and Custard has no interoperability obligation that would
    make the source arity worth preserving. *)
val is_type_binder (env:TcEnv.env) (b:binder) : ML bool

(** [is_value_indexed_arity env t] holds of an arity all of whose arguments are
    values: [header -> Type], not [Type -> Type].  Values are erased from the
    target's type language, so such an arity denotes one target type and can be
    a type parameter; section 18.2. *)
val is_value_indexed_arity (env:TcEnv.env) (t:typ) : ML bool

(** [is_type_param env b] holds of an arity binder the target can express as a
    type parameter: one of kind [Type], or one indexed only by values (see
    {!is_value_indexed_arity}).  A genuinely higher-kinded one -- the [m] of
    [class monad (m:Type -> Type)] -- is erased like any other type binder but
    cannot be declared or passed, so it is not one. *)
val is_type_param (env:TcEnv.env) (b:binder) : ML bool

(** Is this *argument* a type rather than a value?

    A spine is usually filtered by its head's binders, but a head can be a
    term no declaration describes -- a [match], a [let], a lambda left over
    from beta-reducing a specialized definition.  Its type arguments still
    have to go: types are erased, and one left behind is emitted as a term and
    comes out as an unbound variable. *)
val is_type_term (env:TcEnv.env) (t:term) : ML bool

val is_erased_binder (env:TcEnv.env) (b:binder) : ML bool

(** [keep_thunk env bs c flags] is [flags] with its last entry cleared when
    dropping every binder would turn the definition into a value, or when the
    last binder is unit-shaped in front of an impure codomain and so may be a
    thunk.  Applied both to a definition's own binders and to its type, so
    that the two agree on the arity. *)
val keep_thunk (env:TcEnv.env) (bs:binders) (c:comp) (flags:list bool) : ML (list bool)

(** [erased_binders env t] applies [is_erased_binder] to each binder of [t]'s
    outermost arrow, in order.  Used wherever a spine has to be filtered but no
    full [classify] is available: constructor applications and type
    applications, where the flags are aligned against binders that came from
    [arrow_formals_comp] too. *)
val erased_binders (env:TcEnv.env) (t:typ) : ML (list bool)

(** [erased_binders_unfold env t] is [erased_binders] over the whole arrow
    spine, unfolding abbreviations in the codomain as [classify] does.  This is
    what filtering a *call spine* wants: a call may run straight through an
    abbreviation that the type stops at, and leaving the surplus alone passes
    erased arguments the callee has deleted. *)
val erased_binders_unfold (env:TcEnv.env) (t:typ) : ML (list bool)

(** [retained_sorts env t] is the sorts of the binders [erased_binders] keeps,
    in order: exactly what a caller still has to supply.  Used to type the
    binders introduced when a primitive has to be eta-expanded. *)
val retained_sorts (env:TcEnv.env) (t:typ) : ML (list typ)

(** [unit_binders env t] marks the binders of [t] whose type is unit-shaped
    ([unit], [squash p], [_:unit{p}]).  They are kept -- a unit binder is how
    F* writes a thunk -- but carry no value, so a call site passes [()]. *)
val unit_binders (env:TcEnv.env) (t:typ) : ML (list bool)

(** [type_binders env t] marks the binders of [t] that are types.  This is the
    dual filter, used at the *type* level: the arguments of a type constructor
    that survive into a [cty] are exactly its type parameters. *)
val type_binders (env:TcEnv.env) (t:typ) : ML (list bool)

(** [type_params env t] marks the binders of [t] that {!is_type_param}
    accepts: the parameters the emitted type declaration actually binds. *)
val type_params (env:TcEnv.env) (t:typ) : ML (list bool)

(** [ctor_stores_type env l] is true when the data constructor [l] takes a
    [Type] argument that is not one of its inductive's parameters -- the
    [b_impl_type] of [Mkbundle], not the [a] of [Cons] -- *and* some later
    field's type mentions it.  Matching on such a constructor binds a type to
    a variable, which monomorphization has no answer for, so the match has to
    be resolved at specialization time (section 30.8), and a binder of such a
    type has to be [Mono] (rule 4b).

    The dependence is what makes it an existential, and so what makes the
    representation depend on the contents.  A stored type nothing mentions is
    erased like any other (section 32.6). *)
val ctor_stores_type (env:TcEnv.env) (l:Ident.lident) : ML bool

(** [existential_field env b] is the constructor and the [Type0] field that
    make [b]'s type an existential, if any: the reason rule 4b classified [b]
    as [Mono].  Error 364 reports the consequence -- "there is nothing to
    specialize on" -- and its advice is to write an annotation; when this is
    the cause, no annotation helps, and saying which field is responsible is
    the only useful thing to say (section 32.6). *)
val existential_field (env:TcEnv.env) (b:binder)
  : ML (option (Ident.lident & Ident.lident))

(** [classify env attrs t] classifies the binders of a definition of type [t]
    carrying the top-level attributes [attrs].  The returned list has one
    entry per binder of [t]'s outermost arrow, in order. *)
val classify (env:TcEnv.env) (attrs:list attribute) (t:typ) : ML (list bclass)

(** [classify_def env attrs t def] is {!classify}, extended to the binders of
    [def]'s own lambda that [t]'s arrow spine stops short of -- which is what
    an abbreviation in the codomain does.  Those are filtered by
    {!is_erased_binder}, which is the rule the emitted definition applies to
    them, so a call site and the definition agree.  Section 19.4.

    [demanded] is section 30.11's rule 4c: the binders that an application of
    a [@@custard_compile_time] definition needs to be known.  Only the body
    shows those, so the caller computes them. *)
val classify_def (env:TcEnv.env) (attrs:list attribute) (t:typ) (def:option term)
                 (demanded:list int)
  : ML (list bclass)

(** True if any binder is [Mono], i.e. uses of this definition have to be
    specialized. *)
val has_mono (cs:list bclass) : ML bool

(** True if any binder is [Dropped], i.e. uses of this definition have to have
    arguments deleted. *)
val has_dropped (cs:list bclass) : ML bool
