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
      - there is a single coercion node ([ECast]) standing for all of
        [Obj.magic], [Ghost.reveal]/[hide] and representation changes;
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

type cty =
  | TVar   of string
  | TInt   of signedness & width
  (** A machine integer.  Installed by a builtin rule (section 8): the source
      [FStar.UInt32.t] is a record wrapping a refined [nat], which Custard must
      not look inside. *)
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

type constant =
  | CUnit
  | CBool   of bool
  | CInt    of string & option (signedness & width)
  | CChar   of char
  | CString of string

(** {1 Patterns and terms} *)

type pat =
  | PWild
  | PVar   of string
  | PConst of constant
  | PCtor  of name & list pat
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

(** A primitive operation, together with the machine type it operates at.
    [po_int = None] means the operands are booleans or mathematical integers,
    i.e. the operation is not width-directed. *)
type prim_op = {
  po_op:  op;
  po_int: option (signedness & width);
}

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
  | ECast    of expr & cty
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
  | Imported of string
  (** This declaration was compiled by an already-built unit (section 12), the
      one named here.  It is present so that this unit's passes can see its
      shape -- a type's layout, a function's signature -- but it is not emitted
      and its uses print qualified by that unit's namespace. *)

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
  ti_pre:    option dtype;
  (** The declaration as the layout analysis left it -- *before* [Simplify]
      reshaped it.  A downstream unit's [Simplify] has to reach the same
      conclusions this one did, and the passes that draw them read the
      declaration at this point in the pipeline, not at the end of it: at the
      time [inline_fields] asks whether a field's type is a one-constructor
      variant, that type is still a variant even if [records] is about to turn
      it into a record. *)
  ti_record: bool;
  (** Whether [Simplify.records] turned it into a record.  This one *is* a
      whole-program decision -- a constructor pattern surviving anywhere
      disqualifies its type, because the IR has no record pattern to rewrite
      one to -- so a downstream unit cannot re-derive it and must be told. *)
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
