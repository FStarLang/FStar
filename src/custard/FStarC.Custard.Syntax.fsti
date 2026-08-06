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
    [uniq] is 0 for a definition that was not specialized, and n > 0 for its
    n-th specialization.  [hint] is a human-readable reminder of what the
    specialization was for (e.g. "string"); it is only used when building the
    mangled name, which is the only debugging aid Custard provides, so it
    should be kept readable. *)
type name = {
  ns:   list string;
  id:   string;
  uniq: int;
  hint: option string;
}

val mangled_name : name -> ML string
val string_of_name : name -> ML string

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

(** The primitive operators a builtin rule (section 8) may introduce.  The
    names and the grouping deliberately follow karamel's, since that is the
    backend that has to give them a C meaning. *)
type op =
  | Add | AddW | Sub | SubW | Mult | MultW | Div | DivW | Mod
  (** The [W] variants wrap around instead of being undefined on overflow. *)
  | BOr | BAnd | BXor | BShiftL | BShiftR | BNot
  | Eq | Neq | Lt | Lte | Gt | Gte
  | And | Or | Not

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
  | EOp      of prim_op & list expr
  | EWhile   of expr & expr
  | ERaise   of name & list expr
  | ETry     of expr & list branch

and branch = pat & option expr & expr

(** {1 Declarations} *)

type flag =
  | Rec of list name       (** the SCC this declaration belongs to *)
  | Private
  | Entrypoint
  | NoNewtype
  | Erased
  (** The type has no runtime representation at all (section 5.1).  Set by the
      extractor for types F* considers non-informative; the layout analysis
      propagates it structurally. *)
  | Comment of string

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

(** {1 Helpers} *)

val mk : expr' -> cty -> eff -> expr
val unit_expr : expr
val name_of_decl : decl -> name
val decl_flags : decl -> list flag
val has_flag : list flag -> flag -> ML bool

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
