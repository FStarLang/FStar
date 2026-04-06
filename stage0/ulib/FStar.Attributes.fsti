[@@"no_prelude"]
module FStar.Attributes

open Prims

/// Attributes:
///
/// An attribute is any F* term.
///
/// Attributes are desugared and checked for being well-scoped. But,
/// they are not type-checked.
///
/// It is associated with a definition using the [[@@attribute]]
/// notation, just preceding the definition.

(** We collect several internal ocaml attributes into a single
    inductive type.

    This may be unnecessary. In the future, we are likely to flatten
    this definition into several definitions of abstract top-level
    names.

    An example:

     {[
        [@@ CInline ] let f x = UInt32.(x +%^ 1)
      ]}

    is extracted to C by KaRaMeL to a C definition tagged with the
    [inline] qualifier. *)
type __internal_ocaml_attributes =
  | PpxDerivingShow (* Generate [@@@ deriving show ] on the resulting OCaml type *)
  | PpxDerivingShowConstant of string (* Similar, but for constant printers. *)
  | PpxDerivingYoJson (* Generate [@@@ deriving yojson ] on the resulting OCaml type *)
  | CInline
  (* KaRaMeL-only: generates a C "inline" attribute on the resulting
     * function declaration. When used on a local definition (i.e. a letbinding)
     KaRaMeL will try to inline this binding in the extracted C code. *)
  | Substitute
  (* KaRaMeL-only: forces KaRaMeL to inline the function at call-site; this is
     * deprecated and the recommended way is now to use F*'s
     * [inline_for_extraction], which now also works for stateful functions. *)
  | Gc
  (* KaRaMeL-only: instructs KaRaMeL to heap-allocate any value of this
     * data-type; this requires running with a conservative GC as the
     * allocations are not freed. *)
  | Comment of string
  (* KaRaMeL-only: attach a comment to the declaration. Note that using F*-doc
     * syntax automatically fills in this attribute. *)
  | CPrologue of string
  (* KaRaMeL-only: verbatim C code to be prepended to the declaration.
     * Multiple attributes are valid and accumulate, separated by newlines. *)
  | CEpilogue of string (* Ibid. *)
  | CConst of string
  (* KaRaMeL-only: indicates that the parameter with that name is to be marked
     * as C const.  This will be checked by the C compiler, not by KaRaMeL or F*.
     *
     * This is deprecated and doesn't work as intended. Use
     * LowStar.ConstBuffer.fst instead! *)
  | CCConv of string (* A calling convention for C, one of stdcall, cdecl, fastcall *)
  | CAbstractStruct
  (* KaRaMeL-only: for types that compile to struct types (records and
     * inductives), indicate that the header file should only contain a forward
     * declaration, which in turn forces the client to only ever use this type
     * through a pointer. *)
  | CIfDef (* KaRaMeL-only: on a given `val foo`, compile if foo with #ifdef. *)
  | CMacro
(* KaRaMeL-only: for a top-level `let v = e`, compile as a macro *)
  | CNoInline
    (* For security-sensitive functions only: generate special attributes in C
       to prevent inlining; if the function is subjected to a -static-header
       option, the `inline` attribute will be removed, but the static will
       remain. *)

(** The [inline_let] attribute on a local let-binding, instructs the
    extraction pipeline to inline the definition. This may be both to
    avoid generating unnecessary intermediate variables, and also to
    enable further partial evaluation. Note, use this with care, since
    inlining all lets can lead to an exponential blowup in code
    size. *)
val inline_let : unit

(** The [inline_let_vc] attribute on a local let-binding, instructs the
    verification condition generator to try to inline the definition in the
    VC of the continuation. Note, use this with care, since
    inlining all lets can lead to an exponential blowup in VC
    size. It is however useful for VCs where a local definition
    must be normalized, e.g., in conjunction with assert_norm. 
    Note, inline_let and inline_let_vc are both implied by `unfold let` *)
val inline_let_vc : unit

(** The [no_inline_let] attribute on a local let-binding prevents the
    normalizer from unfolding the definition of a local let-binding. This
    attribute can be useful when processing definitions with tactics, as
    otherwise the normalizer will eagerly unfold all pure definitions. *)
val no_inline_let : unit

(** The [rename_let] attribute support a form of metaprogramming for
    the names of let-bound variables used in extracted code.

    This is useful, particularly in conjunction with partial
    evaluation, to ensure that names reflect their usage context.

    See tests/micro-benchmarks/Renaming*.fst *)
val rename_let (new_name: string) : Tot unit

(** The [plugin] attribute is used in conjunction with native
    compilation of F* components, accelerating their reduction
    relative to the default strategy of just interpreting them.

    See examples/native_tactics for several examples. *)
val plugin (x: int) : Tot unit

(** An attribute to mark things that the typechecker should *first*
    elaborate and typecheck, but unfold before verification. *)
val tcnorm : unit

(** This attribute is used with the Dijkstra Monads for Free
    construction to track position information in generated VCs *)
val dm4f_bind_range : unit

(** We erase all ghost functions and unit-returning pure functions to
    [()] at extraction. This creates a small issue with abstract
    types. Consider a module that defines an abstract type [t] whose
    (internal) definition is [unit] and also defines [f: int -> t]. [f]
    would be erased to be just [()] inside the module, while the
    client calls to [f] would not, since [t] is abstract. To get
    around this, when extracting interfaces, if we encounter an
    abstract type, we tag it with this attribute, so that
    extraction can treat it specially.

    Note, since the use of cross-module inlining (the [--cmi] option),
    this attribute is no longer necessary. We retain it for legacy,
    but will remove it in the future. *)
val must_erase_for_extraction : unit

(** When attached a top-level definition, the typechecker will succeed
    if and only if checking the definition results in an error. The
    error number list is actually OPTIONAL. If present, it will be
    checked that the definition raises exactly those errors in the
    specified multiplicity, but order does not matter. *)
val expect_failure (errs: list int) : Tot unit

(** When --admit_smt_queries true is present, with the previous attribute since some
  definitions only fail when verification is turned on. With this
  attribute, one can ensure that a definition fails while lax-checking
  too. Same semantics as above, but lax mode will be turned on for the
  definition.  *)
val expect_lax_failure (errs: list int) : Tot unit

(** Print the time it took to typecheck a top-level definition *)
val tcdecltime : unit

(** This attribute is to be used as a hint for the unifier.  A
    function-typed symbol `t` marked with this attribute will be treated
    as being injective in all its arguments by the unifier.  That is,
    given a problem `t a1..an =?= t b1..bn` the unifier will solve it by
    proving `ai =?= bi` for all `i`, without trying to unfold the
    definition of `t`. *)
val unifier_hint_injective : unit

(**
 This attribute is used to control the evaluation order
 and unfolding strategy for certain definitions.

  In particular, given
     {[
        [@@(strict_on_arguments [1;2])]
        let f x0 (x1:list x0) (x1:option x0) = e
     ]}

 An application [f e0 e1 e2] is reduced by the normalizer by:

     1. evaluating [e0 ~>* v0, e1 ~>* v1, e2 ~>* v2]

     2 a.
        If, according to the positional arguments [1;2],
        if v1 and v2 have constant head symbols
              (e.g., v1 = Cons _ _ _, and v2 = None _)
       then [f] is unfolded to [e] and reduced as
         {[e[v0/x0][v1/x1][v2/x2]]}

     2 b.

      Otherwise, [f] is not unfolded and the term is [f e0 e1 e2]
      reduces to [f v0 v1 v2]. *)
val strict_on_arguments (x: list int) : Tot unit

(**
 * An attribute to tag a tactic designated to solve any
 * unsolved implicit arguments remaining at the end of type inference.
 **)
val resolve_implicits : unit

(**
 * Implicit arguments can be tagged with an attribute [abc] to dispatch
 * their solving to a user-defined tactic also tagged with the same
 * attribute and resolve_implicits [@@abc; resolve_implicits].

 * However, sometimes it is useful to have multiple such
 * [abc]-tagged tactics in scope. In such a scenario, to choose among them,
 * one can use the attribute as shown below to declare that [t] overrides
 * all the tactics [t1...tn] and should be used to solve [abc]-tagged
 * implicits, so long as [t] is not iself overridden by some other tactic.

   [@@resolve_implicits; abc; override_resolve_implicits_handler abc [`%t1; ... `%tn]]
   let t = e

 **)
val override_resolve_implicits_handler : #a:Type -> a -> list string -> Tot unit

(** A tactic registered to solve implicits with the (handle_smt_goals)
    attribute will receive the SMT goal generated during typechecking
    just before it is passed to the SMT solver.
   *)
val handle_smt_goals : unit

(** This attribute can be added to an inductive type definition,
    indicating that it should be erased on extraction to `unit`.

    However, any pattern matching on the inductive type results
    in a `Ghost` effect, ensuring that computationally relevant
    code cannot rely on the values of the erasable type.

    See tests/micro-benchmarks/Erasable.fst, for examples.  Also
    see https://github.com/FStarLang/FStar/issues/1844 *)
val erasable : unit

(** [commute_nested_matches]
    This attribute can be used to decorate an inductive type [t]

    During normalization, if reduction is blocked on matching the
    constructors of [t] in the following sense:

    [
     match (match e0 with | P1 -> e1 | ... | Pn -> en) with
     | Q1 -> f1 ... | Qm -> fm
    ]

    i.e., the outer match is stuck due to the inner match on [e0]
    being stuck, and if the head constructor the outer [Qi] patterns
    are the constructors of the decorated inductive type [t], then,
    this is reduced to

    [
     match e0 with
     | P1 -> (match e1 with | Q1 -> f1 ... | Qm -> fm)
     | ...
     | Pn -> (match en with | Q1 -> f1 ... | Qm -> fm)
    ]

    This is sometimes useful when partially evaluating code before
    extraction, particularly when aiming to obtain first-order code
    for KaRaMeL. However, this attribute should be used with care,
    since if after the rewriting the inner matches do not reduce, then
    this can cause an explosion in code size.

    See tests/micro-benchmarks/CommuteNestedMatches.fst
    and examples/layeredeffects/LowParseWriters.fsti
  *)
val commute_nested_matches : unit

(** This attribute controls extraction: it can be used to disable
    extraction of a given top-level definition into a specific backend,
    such as "OCaml". If any extracted code must call into an erased
    function, an error will be raised (code 340).
  *)
val noextract_to (backend:string) : Tot unit


(** A layered effect definition may optionally be annotated with
    (ite_soundness_by t) attribute, where t is another attribute
    When so, the implicits and the smt guard generated when
    checking the soundness of the if-then-else combinator, are
    dispatched to the tactic in scope that has the t attribute (in addition
    to the resolve_implicits attribute as usual)

    See examples/layeredeffects/IteSoundess.fst for a few examples
  *)
val ite_soundness_by (attribute: unit): Tot unit

(** By-default functions that have a layered effect, need to have a type
    annotation for their bodies
    However, a layered effect definition may contain the default_effect
    attribute to indicate to the typechecker that for missing annotations,
    use the default effect.
    The default effect attribute takes as argument a string, that is the name
    of the default effect, two caveats:
      - The argument must be a string constant (not a name, for example)
      - The argument should be the fully qualified name
    For example, the TAC effect in FStar.Tactics.Effect.fsti specifies
    its default effect as FStar.Tactics.Tac
    F* will typecheck that the default effect only takes one argument,
      the result type of the computation
  *)
val default_effect (s:string) : Tot unit

(** A layered effect may optionally be annotated with the
    top_level_effect attribute so indicate that this effect may
    appear at the top-level
    (e.g., a top-level let x = e, where e has a layered effect type)

    The top_level_effect attribute takes (optional) string argument, that is the
    name of the effect abbreviation that may constrain effect arguments
    for the top-level effect

    As with default effect, the string argument must be a string constant,
    and fully qualified

    E.g. a Hoare-style effect `M a pre post`, may have the attribute
    `@@ top_level_effect "N"`, where the effect abbreviation `N` may be:

    effect N a post = M a True post

    i.e., enforcing a trivial precondition if `M` appears at the top-level

    If the argument to `top_level_effect` is absent, then the effect itself
    is allowed at the top-level with any effect arguments

    See tests/micro-benchmarks/TopLevelIndexedEffects.fst for examples

    *)
val top_level_effect (s:string) : Tot unit

(** This attribute can be annotated on the binders in an effect signature
    to indicate that they are effect parameters. For example, for a
    state effect that is parametric in the type of the state, the state
    index may be marked as an effect parameter.

    Also see https://github.com/FStarLang/FStar/wiki/Indexed-effects

    *)
val effect_param : unit

(** Bind definition for a layered effect may optionally contain range
    arguments, that are provided by the typechecker during reification
    This attribute on the effect definition indicates that the bind
    has range arguments.
    See for example the TAC effect in FStar.Tactics.Effect.fsti
  *)
val bind_has_range_args : unit


(** An indexed effect definition may be annotated with
    this attribute to indicate that the effect should be
    extracted "natively". E.g., the `bind` of the effect is
    extracted to primitive `let` bindings

    As an example, `Steel` effects (the effect for concurrent
    separation logic) are marked as such

  *)
val primitive_extraction : unit

(** A qualifier on a type definition which when used in co-domain position
    on an arrow type will be extracted as if it were an impure effect type.

    e.g., if you have

    [@@extract_as_impure_effect]
    val stt (a:Type) (pre:_) (post:_) : Type

    then arrows of the form `a -> stt b p q` will be extracted
    similarly to `a -> Dv b`.
 *)
val extract_as_impure_effect : unit


(** A binder in a definition/declaration may optionally be annotated as strictly_positive
    When the let definition is used in a data constructor type in an inductive
    definition, this annotation is used to check the positivity of the inductive

    Further F* checks that the binder is actually positive in the let definition

    See tests/micro-benchmarks/Positivity.fst and NegativeTests.Positivity.fst for a few examples
  *)
val strictly_positive : unit

(** A binder in a definition/declaration may optionally be annotated as unused.
    This is used in the strict positivity checker. E.g., a type such as the one
    below is accepted

    let f ([@@@unused] a:Type) = unit
    type t = | MkT: f t -> t

    F* checks that the binder is actually unused in the definition

    See tests/micro-benchmarks/Positivity.fst for a few examples
  *)
val unused : unit

(** This attribute may be added to an inductive type
    to disable auto generated projectors

    Normally there should not be any need to use this unless:
    for some reason F* cannot typecheck the auto-generated projectors.

    Another reason to use this attribute may be to avoid generating and
    typechecking lot of projectors, most of which are not going to be used
    in the rest of the program
  *)
val no_auto_projectors : unit

(** As [no_auto_projectors] but also do not even generate declarations
    for them. *)
val no_auto_projectors_decls : unit

(** This attribute can be added to a let definition
    and indicates to the typechecker to typecheck the signature of the definition
    without using subtyping. This is sometimes useful for indicating that a lemma
    can be applied by the tactic engine without requiring to check additional
    subtyping obligations
*)
val no_subtyping : unit

(* This can be attached to a top-level declaration to admit its verification
   conditions. *)
val admitted : unit

(* This can be attached to a recursive definition to admit its proof
   of termination (but nothing else). *)
val admit_termination : unit

(* This marks a given definition as a coercion to be automatically
   applied by the typechecker. See doc/rec/coercions.txt for more
   information. *)
val coercion : unit

(** Marks a record type as being the result of an automatic desugar of
    a constructor with a record payload.
    For example, in a module `M`, `type foo = | A {x: int}` desugars
    to the type `M.foo` and a type `M.foo__A__payload`. That latter
    type `foo__A__payload` is decorated with an attribute
    `desugar_of_variant_record ["M.A"]`. *)
val desugar_of_variant_record (type_name: string): unit

(** Tag for implicits that are to be solved by a tactic. *)
val defer_to (#a:Type) (tag : a) : unit
