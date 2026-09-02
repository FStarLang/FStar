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

(** The Custard IR.

    Custard is a whole-program, demand-driven, monomorphizing extraction
    pipeline.  See doc/ref/custard.md for the design; this module defines the
    intermediate representation described in section 2 of that document.

    The IR is similar to the ML extraction IR (FStarC.Extraction.ML.Syntax) but
    kept separate so that the two can evolve independently.  The salient
    differences:

      - there is no [MLTY_Erased]: erasure is a property computed by the
        representation analysis, and erased things are deleted rather than
        replaced by [unit];
      - discriminators are IR nodes ([EDiscrim]), not generated functions;
      - a coercion node ([ECoerce]) stands for all of [Obj.magic],
        [Ghost.reveal]/[hide] and representation changes, and is kept
        distinct from the machine-integer conversion ([ECast]) even though
        both are spelled as a cast in C: only the former is a no-op;
      - there are no function-local recursive let-bindings: they are lifted to
        the top level, which breaks the cycle between the declaration and term
        types.
*)
module FStarC.Custard.Syntax

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Ident
open FStarC.Const
open FStarC.BaseTypes

open FStarC.Class.Show
open FStarC.Class.PP

(** {1 Names} *)

(** A name in the IR refers to one *specialization* of one source definition.
    [spec] is [None] for a definition that was not specialized at all, and
    otherwise the suffix distinguishing this specialization from its siblings
    -- a human-readable reminder of what it was for ("string", "3"), made
    unique by the extractor.  *Every* specialization has one, including the
    only one: a bare name would then mean two different things depending on
    how many siblings happened to exist, which is exactly the sort of thing
    that makes generated code hard to read. *)
type name = {
  ns:   list string;
  id:   string;
  spec: option string;
}

val mangled_name : name -> ML string
val string_of_name : name -> ML string

(** {1 Local names} *)

(** A local name is the source [ppname] plus a uniquifying suffix, because two
    distinct F* [bv]s routinely share a [ppname].  The separator is a character
    no F* identifier and no target-language identifier can contain, so the two
    halves can always be told apart again -- which is what lets
    {!FStarC.Custard.Rename} hand the source spelling back at the very end of
    the pipeline, and what makes a name that escaped it obvious on sight. *)
val uniq : string -> int -> ML string

(** The part of a local name before the uniquifying suffix. *)
val base_name : string -> ML string

(** {1 Effects} *)

(** The effect lattice, ordered [E_Ghost < E_Pure < E_Impure].  We deliberately
    do not subdivide [E_Impure]: Custard's only effect-directed question is
    whether a term may be dropped, duplicated or reordered, and all impure
    effects answer it the same way. *)
type eff =
  | E_Ghost
  | E_Pure
  | E_Impure

(** [join e1 e2] is the least upper bound. *)
val join_eff : eff -> eff -> eff

(** [is_pure e] holds when a term with effect [e] may be freely dropped,
    duplicated and reordered. *)
val is_pure : eff -> bool

(** {1 Types} *)

(** The floating-point formats, section 38.  Named after the source modules
    [FStar.Float32] and [FStar.Float64], and matching karamel's [width] so
    that the krml backend can hand them straight over. *)
type fwidth =
  | Float32
  | Float64

type cty =
  | TVar   of string
  | TInt   of signedness & width
  (** A machine integer.  Installed by a builtin rule (section 8): the source
      [FStar.UInt32.t] is a record wrapping a refined [nat], which Custard must
      not look inside. *)
  | TFloat of fwidth
  (** An IEEE 754 binary float, [float] or [double] in C (section 38).  As
      with [TInt] the source type is opaque -- [FStar.Float64.t] is a [new
      val t : Type0] -- and a builtin rule installs this in its place. *)
  | TArrow of cty & eff & cty
  | TApp   of name & list cty
  | TBuf   of cty
  (** A pointer to a mutable, contiguous run of values: Pulse's [array], [vec]
      and [ptr] (section 8.4).  One node for all of them is what lets the C
      backend emit a real pointer instead of a call into a runtime. *)
  | TInline of cty
  (** Only meaningful on a constructor field: the field's contents are stored
      in the constructor itself rather than behind a pointer to them, so its
      record type's fields take the place of it (section 5.7).  [Extract] puts
      it there, [Simplify.inline_fields] takes every one of them away again;
      no later pass and no backend ever sees one. *)
  | TRef   of cty
  (** A pointer to a single mutable value: Pulse's [ref] and [box].  C makes no
      distinction -- both are [t*], and the buffer operations apply to either
      -- but OCaml does, and a [t ref] is both the honest translation and a
      far better one than a one-element array (section 8.4). *)
  | TExn
  (** [Prims.exn], the one extensible variant.  It has no parameters and no
      layout to derive: its constructors arrive one at a time, as [DExn]
      declarations (section 8.5).  Only OCaml has a representation for it. *)
  | TTuple of list cty
  | TUnit
  (** The sole inhabited erased value.  Erased *types* have no
      representation at all and are deleted; [TUnit] is only for the residual
      positions where a value must exist. *)
  | TAny
  (** Representation unknown; the analogue of the ML extraction's [MLTY_Top].
      Because the program is whole and monomorphic, this should be rare, and
      each occurrence is worth reporting. *)

(** {1 Constants} *)

(** A floating-point literal, section 39.  IEEE 754 is sign-and-magnitude and
    so is this: [-0.0] and [0.0] are different floats, and
    [FStar.Float64.bit_eq] can tell them apart, but they are the same *real
    number* and [FStarC.Real.real] is canonical, so a sign folded into the
    magnitude would be a sign lost.

    [fl_mag] denotes the exact rational [mantissa * 10^exponent] and is never
    negative.  What it cannot denote -- an infinity, a NaN -- is what
    [of_literal]'s grammar does not accept either. *)
type float_lit = {
  fl_neg : bool;
  fl_mag : Real.real;
}

type constant =
  | CUnit
  | CBool   of bool
  | CInt    of int & int_base & option (signedness & width)
  (** An integer literal, section 39: the mathematical integer it denotes,
      and the base it was written in.  The base has no bearing on the value
      and is carried for the reader of the generated code, who wrote [0xff]
      and should not be shown 255. *)
  | CFloat  of float_lit & fwidth
  | CChar   of char
  | CString of string

(** The literal as it is spelled in generated code, e.g. ["-1.5"], ["314e-7"].
    Always parseable back by [float_lit_of_string], and always denoting the
    same number: section 39.2. *)
val float_lit_to_string : float_lit -> string

(** Parse the argument of [FStar.Float64.of_literal].  [None] if it is not a
    decimal floating-point literal -- an optional sign, a mantissa with at
    least one digit and at most one point, and an optional decimal exponent.
    Section 39.2. *)
val float_lit_of_string : string -> option float_lit

(** The literal as it is spelled in generated code, in the base it was
    written in.  Never carries a suffix or a cast: those are a backend's. *)
val int_lit_to_string : int -> int_base -> string

(** Equality of the *values* two constants denote.  Structural equality is not
    that: an integer literal also carries the base it was written in, which is
    for the reader and not part of the number, so [1] and [0x1] are equal here
    and distinct to [=].  Section 39.1. *)
val const_eq : constant -> constant -> bool

(** {1 Patterns and terms} *)

type pat =
  | PWild
  | PVar   of string
  | PConst of constant
  | PCtor  of name & list pat
  (* A record's fields, named.  The layout analysis gives a
     single-constructor type a record representation, and a match on it has to
     be spelled the way the target language spells one; [PCtor] cannot say it
     because the constructor no longer exists.  The list need not mention every
     field. *)
  | PRecord of name & list (string & pat)
  | PTuple of list pat
  | POr    of list pat

type binder = {
  b_name: string;
  b_ty:   cty;
}

(** Where a buffer allocated by [BufCreate] lives, and hence who frees it. *)
type lifetime =
  | LStack
  | LHeap

(** The primitive operators a builtin rule (section 8) may introduce.  The
    names and the grouping deliberately follow karamel's, since that is the
    backend that has to give them a C meaning. *)
type op =
  | Add | AddW | Sub | SubW | Mult | MultW | Div | DivW | Mod
  (** The [W] variants wrap around instead of being undefined on overflow. *)
  | BOr | BAnd | BXor | BShiftL | BShiftR | BNot
  | Eq | Neq | Lt | Lte | Gt | Gte
  | And | Or | Not
  (** The buffer operations (section 8.4).  All of them are impure except
      [BufSub] and [BufNull], which only compute an address. *)
  | BufCreate of lifetime  (** [init; len] *)
  | BufRead                (** [buf; idx] *)
  | BufWrite               (** [buf; idx; v] *)
  | BufSub                 (** [buf; idx] *)
  | BufFree                (** [buf] *)
  | BufNull                (** no arguments; the element type is the node's *)
  | BufIsNull              (** [buf] *)
  | BufBlit                (** [src; srcidx; dst; dstidx; len] *)

(** The machine type a primitive operation works at. *)
type prim_ty =
  | PInt   of signedness & width
  | PFloat of fwidth

(** A primitive operation, together with the machine type it operates at.
    [po_ty = None] means the operands are booleans or mathematical integers,
    i.e. the operation is not width-directed.

    Section 38: this used to be [po_int : option (signedness & width)].  The
    distinction that matters at most sites is still "is there a width here",
    but a few of them -- [And] and [Or] are bitwise at a width, narrow
    integer results need truncating -- mean *integer* specifically, and a
    float must not be swept in with them. *)
type prim_op = {
  po_op:  op;
  po_ty:  option prim_ty;
}

(** Does this operation work at an *integer* width?  [And], [Or] and [Not] are
    the bitwise operators there and the connectives otherwise, and a narrow
    integer result may need truncating; neither question is about floats. *)
val at_int_width : prim_op -> bool

(** Every expression node carries its type and effect: monomorphization means
    both are always known, and the simplification passes need the effect at
    every node to decide what they may move. *)
type expr = {
  e:   expr';
  ty:  cty;
  eff: eff;
}

and expr' =
  | EConst   of constant
  | EVar     of string
  | EQual    of name & list cty
  (** A reference to a top-level declaration, applied to its remaining
      (i.e. not monomorphized away) type arguments. *)
  | ELet     of string & cty & expr & expr
  (** Non-recursive only. *)
  | EApp     of expr & list expr
  | EFun     of list binder & expr
  | EMatch   of expr & list branch
  | EIf      of expr & expr & expr
  | ESeq     of expr & expr
  | ECtor    of name & list expr
  | ETuple   of list expr
  | ERecord  of name & list (string & expr)
  | EProj    of expr & name & string
  | EDiscrim of expr & name
  | ECoerce  of expr & cty
  (** A change of *representation*: [Obj.magic], [Ghost.reveal]/[hide], and
      the boundaries section 5.4 inserts where [TAny] meets a concrete type.
      It computes nothing, so nested coercions fuse and a coercion to the type
      the operand already has is dropped. *)
  | ECast    of expr & cty
  (** A numeric conversion: [FStar.Int.Cast.uint32_to_uint8] and friends
      (section 5.5), and [FStar.Float64.of_int] (section 38).  It is *not* a
      no-op -- narrowing loses bits, a sign change reinterprets them, and an
      integer-to-float conversion rounds -- so it never fuses with anything.
      The target is always a [TInt] or a [TFloat]. *)
  | EAny
  (** An arbitrary value of the node's type: what an uninitialized stack
      allocation is filled with.  Only a rule may introduce it. *)
  | EAbort   of string
  (** Control never reaches here; the string says why.  Only a rule may
      introduce it (Pulse's [unreachable], section 8.3). *)
  | EOp      of prim_op & list expr
  | EWhile   of expr & expr
  | ERaise   of expr
  (** Raise an exception value.  The value is an ordinary [ECtor] of a
      constructor declared by a [DExn] (section 8.5), so nothing here is
      special-cased; only the control flow is. *)
  | ETry     of expr & list branch
  (** [try e with | p -> ...].  The branches match on a [TExn], so they are
      the same [branch] as an [EMatch]'s, and the last one is a catch-all
      rather than exhaustive -- an uncaught exception propagates. *)

and branch = pat & option expr & expr

(** {1 Declarations} *)

type flag =
  | Rec of list name       (** the SCC this declaration belongs to *)
  | Private
  | Root
  (** A root of the extraction, named by [--custard_entry]: it must survive
      dead-code elimination even though nothing in the program calls it. *)
  | Entrypoint
  (** The definition named by [--custard_main], which the generated program
      invokes on startup.  There is at most one. *)
  | NoNewtype
  | Inline
  (** Substitute this definition at its fully applied uses and do not emit it.
      Set for the record projectors and discriminators F* generates, whose
      bodies are a single field access or tag test: emitting them as functions
      turns every field read into a call, which the backends have no way to
      undo. *)
  | Erased
  (** The type has no runtime representation at all (section 5.1).  Set by the
      extractor for types F* considers non-informative; the layout analysis
      propagates it structurally. *)
  | Comment of string
  | Prologue of string
  (** Section 36.3.  Text to emit immediately before this declaration's
      definition in the generated C, and nothing at all in OCaml.  A CUDA
      kernel is an ordinary function with [__global__] in front of it, so for
      a plugin generating device code this flag is the difference between a
      kernel and a host function.  Custard does not read the string. *)
  | Epilogue of string
  (** Text to emit immediately after the definition; the counterpart of
      {!Prologue}. *)
  | CInline
  (** Ask the C compiler to inline this definition.  [inline] in the generated
      C, nothing in OCaml.  Custard's own inlining decisions are {!Inline},
      which is a different thing: that one substitutes and emits nothing. *)
  | Realized
  (** The declaration is realized by hand-written OCaml, in the support module
      named by its own namespace (section 8.2): [FStarC.Platform.Base.sys] is
      [FStarC_Platform_Base.sys].  Custard keeps the declaration so that its
      shape -- constructors, fields, arities -- is visible to the passes, but
      does not emit it, and prints every reference to it, to its constructors
      and to its fields with the realization's own unmangled names.  Its
      representation is therefore fixed outside F*: no erasure, no newtype
      collapse and no inline-field expansion may touch it. *)
  | Modelled
  (** karamel supplies this declaration itself on the backend being emitted
      for, and recognizes it by its F* name (section 20).
      [Pulse.Lib.Slice.slice] under [--custard_backend KrmlRust] is the case
      and today the only one: karamel matches
      [TApp ((["Pulse"; "Lib"; "Slice"], "slice"), [t])] and rewrites it to
      Rust's own borrowed slice, and matches each operation as an [ETApp] of
      its own lid and rewrites it at the *use site*.

      So Custard keeps the declaration for its shape and emits nothing at all
      for it -- not even the abstract declaration an {!Extern} gets, because
      karamel is going to supply its own answer and two would conflict -- and
      the type must additionally stay *polymorphic*, since the shape karamel
      matches is an application and an application with no arguments is not
      one.  {!FStarC.Custard.Monomorphize} freezes it for that reason.

      Deliberately not {!Realized}, though the two say almost the same thing.
      A realization is hand-written OCaml, so on the karamel path a [Realized]
      declaration is still Custard's to emit; a model is the target compiler's
      and never is.  Sharing the flag dropped [FStar.Pervasives.Native.tuple2]
      from the karamel output, which every [split] needs. *)
  | Extern of option string & option string
  (** The type is defined outside F*: an abstract [val t : Type0] carrying
      [@@custard_extern] (section 8.1, kind 4).  Custard keeps the declaration
      so that uses of the type have a name to refer to, but emits no
      definition for it; the C backends spell it with the name in the first
      component -- the mangled one when it is [None] -- and, when the second
      is set, include that header.  Its representation is fixed outside F*,
      so no erasure and no newtype collapse may touch it. *)
  | SourceRecord
  (** The source declaration was written as a record, [type t = { a; b }],
      rather than as a one-constructor inductive.  Custard represents both the
      same way and decides which to emit by layout (section 5.5), so the
      distinction only matters for a [Realized] type: there the OCaml shape is
      the hand-written one, and a realization mirrors what the F* source said
      -- [FStarC.Parser.ParseIt.code_fragment] is an OCaml record and
      [FStar.Pervasives.dtuple4] an OCaml variant. *)
  | Existential of string & string
  (** Section 33.4.  The source inductive is an existential package: the
      constructor named first stores a [Type0] field, named second, that a
      later field's type mentions, so the representation depends on the
      contents and there is no C layout for it (section 30.3).

      Nothing reads this flag to make a decision -- the type is rejected
      either way, by whichever of its fields lost its representation first.
      It exists so that the rejection can say *why*.  Error 364 could
      already, because a monomorphized binder has the source type in hand;
      368 could not, because it fires in the backend on an [IR] type from
      which the [Type0] field has already been erased, and so guessed --
      "that is a Custard bug, please report it" -- at the one shape that is
      not one. *)
  | Imported of string & option string
  (** This declaration was compiled by an already-built unit (section 12), the
      one named first.  It is present so that this unit's passes can see its
      shape -- a type's layout, a function's signature -- but it is not emitted
      and its uses print qualified by that unit's namespace.

      The second component is the F* module whose file it was emitted into,
      when the upstream unit split its output (section 12.9): a reference then
      has to name that file rather than the unit, and the declaration may be
      spelled by its plain identifier rather than its mangled one. *)

type tydef =
  | TAbbrev  of cty
  | TRecord  of list (string & cty)
  | TVariant of list (name & list (string & cty))
  | TAbstract

type dtype = {
  dt_name:   name;
  dt_params: list string;
  dt_body:   tydef;
  dt_flags:  list flag;
}

type dlet = {
  dl_name:    name;
  dl_typars:  list string;
  dl_binders: list binder;
  dl_ret:     cty;
  dl_eff:     eff;
  dl_body:    expr;
  dl_flags:   list flag;
}

type dexternal = {
  dx_name:  name;
  dx_typars: list string;
  (** The type parameters [dx_ty] is abstract in, as [dl_typars] is for a
      compiled definition.  An external is not printed as a declaration, but a
      call site still has to instantiate its signature: a realization written
      polymorphically -- which they all are -- would otherwise make every
      result [any]. *)
  dx_ty:    cty;
  dx_target: option string;
  (** The symbol's name in the target language, when it is not the one derived
      from [dx_name]; set by [@@custard_extern "..."]. *)
  dx_header: option string;
  (** The C header that declares it, for the direct-to-C backend; set by
      [@@custard_c_header "..."]. *)
  dx_flags: list flag;
}

type dexn = {
  de_name: name;
  de_args: list cty;
  de_flags: list flag;
}

type decl =
  | DType     of dtype
  | DLet      of dlet
  | DExternal of dexternal
  | DExn      of dexn

(** A whole program: topologically sorted, with recursive groups marked by the
    [Rec] flag rather than by a syntactic grouping, so that the extraction loop
    can emit declarations as it discovers them. *)
type program = list decl

(** {1 Layout verdicts} *)

(** A layout is not just a tag: it records *which* source field survives in
    *which* target slot, because every constructor application, projection and
    pattern has to be rewritten accordingly.  Knowing only that
    [type foo = { a: prop; b: bool }] "is a newtype" does not say whether
    [Mkfoo a b] translates to [a] or to [b].

    These live here rather than in {!FStarC.Custard.Layout}, which is what
    derives them, because a *linked* unit's verdicts arrive from its interface
    instead (section 12.2) and both modules have to name them. *)

(** Where a source field ends up in the target representation. *)
type slot =
  | S_erased            (** the field has no runtime representation *)
  | S_at of int         (** the field lives at target position i *)

type ctor_layout = {
  cl_name:   name;
  cl_tag:    option int;          (** [None] when the type has a single ctor *)
  cl_slots:  list slot;           (** one per *source* field, in source order *)
  cl_arity:  int;                 (** number of surviving fields *)
  cl_fields: list (string & cty); (** the surviving fields, in target order *)
}

type newtype_layout = {
  nt_ctor:  name;
  nt_field: string;
  nt_index: int;   (** index of the surviving field in the *source* field list *)
  nt_ty:    cty;   (** the payload type, in terms of the type's parameters *)
}

type layout =
  | L_erased                            (** no runtime representation at all *)
  | L_newtype of newtype_layout         (** exactly one field survives *)
  | L_struct  of list ctor_layout
  | L_abbrev  of cty                    (** a transparent abbreviation *)
  | L_opaque                            (** abstract or externally realized *)

(** How one inlined field is stored.

    [| Bar of a & b] is how F* source spells a two-argument constructor, but
    what it denotes is a constructor with *one* argument pointing at a pair, so
    every [Bar] costs an allocation and an indirection nobody asked for
    (FStarLang/FStar#4382).  An inline field says instead: keep the inner
    record's fields in the constructor itself.  [Extract] marks such a field by
    wrapping its type in [TInline] -- tuples without being asked, anything else
    on [@@@custard_inline_field] -- and the layout analysis decides what to do
    with the marker. *)
noeq
type expansion = {
  ex_ty:    cty;                  (** the field's declared type, [TApp (R, _)] *)
  ex_type:  name;                 (** R *)
  ex_ctor:  option name;          (** R's constructor, when R is still a variant *)
  ex_src:   list (string & cty);  (** R's fields, instantiated *)
  ex_dst:   list (string & cty);  (** what they become in the outer constructor *)
}

(** A plan for one constructor, in field order: each field's name before and
    after, and what it expands to.  A field can be renamed without expanding,
    because expanding its neighbour shifts the positional names along. *)
type fplan = list (string & string & option expansion)

(** Everything a *downstream* unit has to be told about a type: not just its
    declaration but the verdict reached about it, which the downstream unit
    must adopt rather than re-derive.  A verdict is recorded for every type a
    unit reached, including the ones that came out with no runtime
    representation at all -- that is as much a verdict as any other. *)
type type_info = {
  ti_erased: bool;
  ti_layout: layout;
  ti_ctors:  list ctor_layout;
  (** The constructor layouts, recorded separately because [L_newtype],
      [L_erased] and [L_opaque] do not carry them and the rewriter still needs
      them: an application or a pattern of a collapsed type's constructor has
      to be rewritten just the same. *)
  ti_record: bool;
  (** Whether the type is represented as a record rather than as a
      one-constructor variant. *)
  ti_plans:  list (name & fplan);
  (** How each of its constructors stores its inlined fields. *)
}

(** The representation verdicts, keyed on the constructor they are about, for
    every type the program uses -- the ones it compiled and the ones it linked
    against alike.  The layout analysis derives them; the passes that apply
    them look them up here and never decide anything themselves, which is what
    keeps a representation a function of the type. *)
noeq
type verdicts = {
  vd_records: FStarC.SMap.t name;
  (** constructor -> the record type it becomes.  Deliberately not the field
      names: [inline_fields] changes those, so the only correct source for
      them is the declaration the rewriter is looking at. *)
  vd_plans:   FStarC.SMap.t fplan;
  (** constructor -> how its inlined fields are stored *)
}

(** {1 Helpers} *)

(* Instantiate type variables, e.g. to specialize a polymorphic declaration's
   signature to a particular call site. *)
val subst_cty : list (string & cty) -> cty -> ML cty

val mk : expr' -> cty -> eff -> expr
val unit_expr : expr
val name_of_decl : decl -> name
val decl_flags : decl -> list flag
val has_flag : list flag -> flag -> ML bool

(** Every type name a type mentions, as [string_of_name] keys. *)
val type_names_of_cty : cty -> ML (list string)

(** Every type name a declaration's *signature* mentions -- what a caller has
    to be able to name in order to use it.  A declaration's body is not
    consulted: an interface does not export one. *)
val type_names_of_decl : decl -> ML (list string)

(** The unit a declaration was imported from, or [None] if this run compiled
    it.  An imported declaration is never emitted. *)
val imported_unit : decl -> ML (option string)

(** The file an imported declaration lives in, for an upstream unit that split
    its output; [None] for a local declaration or a whole-program upstream. *)
val imported_home : decl -> ML (option string)

(** {1 Printing} *)

val program_to_doc : program -> ML FStarC.Pprint.document
val program_to_string : program -> ML string

instance val showable_name     : showable name
instance val showable_eff      : showable eff
instance val showable_cty      : showable cty
instance val showable_constant : showable constant
instance val showable_pat      : showable pat
instance val showable_expr     : showable expr
instance val showable_decl     : showable decl

instance val pp_cty  : pretty cty
instance val pp_expr : pretty expr
instance val pp_decl : pretty decl
