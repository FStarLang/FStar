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
module FStarC.Parser.AST

open FStarC
open FStarC.Effect
open FStarC.Range
open FStarC.Const
open FStarC.Ident
open FStarC.Class.Show
open FStarC.Class.HasRange

(* AST produced by the parser, before desugaring
   It is not stratified: a single type called "term" containing
   expressions, formulas, types, and so on
 *)
type level = | Un | Expr | Type_level | Kind | Formula

type let_qualifier =
  | NoLetQualifier
  | Rec

type local_let_qualifier =
  | LocalNoLetQualifier
  | LocalRec
  | LocalUnfold

type quote_kind =
  | Static
  | Dynamic

type term' =
  | Wild
  | Const     of sconst
  | Op        of ident & list term
  | Uvar      of ident                                (* universe variable *)

  | Var       of lid // a (possibly) qualified identifier that starts with a lowercase (Foo.Bar.baz)
  | Name      of lid // a (possibly) qualified identifier that starts with an uppercase (Foo.Bar.Baz)

  | Projector of lid & ident (* a data constructor followed by one of
                                its formal parameters, or an effect
                                followed by one  of its actions or
                                "fields" *)
  | Construct of lid & list (term&imp)               (* data, type: bool in each arg records an implicit *)
  | Abs       of list pattern & term                 (* fun p1 p2 .. pn -> body *)
  | Function  of list branch & range                 (* function | p1 -> e1 | ... | pn -> en; range is for binder *)
  | App       of term & term & imp                    (* aqual marks an explicitly provided implicit parameter *)
  | Let       of local_let_qualifier & list (option attributes_ & (pattern & term)) & term
  | LetOperator   of list (ident & pattern & term) & term
  | LetOpen   of lid & term
  | LetOpenRecord of term & term & term
  | Seq       of term & term
  | Bind      of ident & term & term (* do notation bind ('x <-- foo ()' or 'f;;g'). DEPRECATED. *)
  | If        of term & option ident (* is this a regular if or a if operator (i.e. [if*]) *)
                      & option match_returns_annotation & term & term
  | Match     of term & option ident (* is this a regular match or a match operator (i.e. [match*]) *)
                      & option match_returns_annotation & list branch
  | TryWith   of term & list branch
  | Ascribed  of term & term & option term & bool  (* bool says whether equality ascription $: *)
  | Record    of option term & list (lid & term)
  | Project   of term & lid
  | Product   of list binder & term                (* function space *)
  | Sum       of list (either binder term) & term (* dependent tuple *)
  | QForall   of list binder & patterns & term
  | QExists   of list binder & patterns & term
  | QuantOp   of ident & list binder & patterns & term
  | Refine    of binder & term
  | NamedTyp  of ident & term
  | Paren     of term
  | Requires  of term
  | Ensures   of term
  | LexList   of list term  (* a decreases clause mentions either a lexicographically ordered list, *)
  | WFOrder   of term & term  (* or a well-founded relation or some type and an expression of the same type *)
  | Decreases of term
  | Labeled   of term & string & bool
  | Discrim   of lid   (* Some?  (formerly is_Some) *)
  | Attributes of list term   (* attributes decorating a term *)
  | Antiquote of term  (* Antiquotation within a quoted term *)
  | Quote     of term & quote_kind
  | VQuote    of term        (* Quoting an lid, this gets removed by the desugarer *)
  | CalcProof of term & term & list calc_step (* A calculational proof with relation, initial expression, and steps *)
  | IntroForall of list binder & term & term                     (* intro_forall x1..xn. P with e *)
  | IntroExists of list binder & term & list term & term        (* intro_exists x1...xn.P using v1..vn with e *)
  | IntroImplies of term & term & binder & term                   (* intro_implies P Q with x. e *)
  | IntroOr of bool & term & term & term                          (* intro_or_{left ,right} P Q with e *)
  | IntroAnd of term & term & term & term                         (* intro_and P Q with e1 and e2 *)
  | ElimForall  of list binder & term & list term               (* elim_forall x1..xn. P using v1..vn *)
  | ElimExists  of list binder & term & term & binder & term     (* elim_exists x1...xn.P to Q with e *)
  | ElimImplies of term & term & term                             (* elim_implies P Q with e *)
  | ElimOr of term & term & term & binder & term & binder & term  (* elim_or P Q to R with x.e1 and y.e2 *)
  | ElimAnd of term & term & term & binder & binder & term        (* elim_and P Q to R with x y. e *)
  | ListLiteral of list term
  | SeqLiteral of list term


and term = {tm:term'; range:range; level:level}



(* (as y)? returns t *)
and match_returns_annotation = option ident & term & bool

and patterns = list ident & list (list term)

and calc_step =
  | CalcStep of term & term & term (* Relation, justification and next expression *)

and attributes_ = list term

and binder' =
  | Variable of ident
  | Annotated of ident & term
  | NoName of term

and binder = {b:binder'; brange:range; blevel:level; aqual:aqual; battributes:attributes_}

and pattern' =
  | PatWild     of aqual & attributes_
  | PatConst    of sconst
  | PatApp      of pattern & list pattern
  | PatVar      of ident & aqual & attributes_
  | PatName     of lid
  | PatList     of list pattern
  | PatRest     (* For '..', which matches all extra args *)
  | PatTuple    of list pattern & bool (* dependent if flag is set *)
  | PatRecord   of list (lid & pattern)
  | PatAscribed of pattern & (term & option term)
  | PatOr       of list pattern
  | PatOp       of ident
  | PatVQuote   of term (* [`%foo], transformed into "X.Y.Z.foo" by the desugarer *)
and pattern = {pat:pattern'; prange:range}

and branch = (pattern & option term & term)
and arg_qualifier =
    | Implicit
    | Equality
    | Meta of term
    | TypeClassArg
and aqual = option arg_qualifier
and imp =
    | FsTypApp
    | Hash
    | UnivApp
    | HashBrace of term
    | Infix
    | Nothing

instance val tagged_term : Class.Tagged.tagged term

instance val hasRange_term    : hasRange term
instance val hasRange_pattern : hasRange pattern
instance val hasRange_binder  : hasRange binder

type knd = term
type typ = term
type expr = term

type tycon_record = list (ident & aqual & attributes_ & term)

(** The different kinds of payload a constructor can carry *)
type constructor_payload
  = (** constructor of arity 1 for a type of kind [Type] (e.g. [C of int]) *)
    | VpOfNotation of typ
    (** constructor of any arity & kind (e.g. [C:int->ind] or [C:'a->'b->ind 'c]) *)
    | VpArbitrary of typ
    (** constructor whose payload is a record (e.g. [C {a: int}] or [C {x: Type} -> ind x]) *)
    | VpRecord of (tycon_record & option typ)

(* TODO (KM) : it would be useful for the printer to have range information for those *)
type tycon =
  | TyconAbstract of ident & list binder & option knd
  | TyconAbbrev   of ident & list binder & option knd & term
  | TyconRecord   of ident & list binder & option knd & attributes_ & tycon_record
  | TyconVariant  of ident & list binder & option knd & list (ident & option constructor_payload & attributes_)

type qualifier =
  | Private
  | Noeq
  | Unopteq
  | Assumption
  | TotalEffect
  | Effect_qual
  | New
  | Inline                                 //a definition that *should* always be unfolded by the normalizer
  | Visible                                //a definition that may be unfolded by the normalizer, but only if necessary (default)
  | Unfold_for_unification_and_vcgen       //a definition that will be unfolded by the normalizer, during unification and for SMT queries
  | Inline_for_extraction                  //a definition that will be inlined only during compilation
  | Irreducible                            //a definition that can never be unfolded by the normalizer
  | NoExtract                              // a definition whose contents won't be extracted (currently, by KaRaMeL only)
  | Reifiable
  | Reflectable
  //old qualifiers
  | Opaque
  | Logic

type qualifiers = list qualifier

type decoration =
  | Qualifier of qualifier
  | DeclAttributes of list term

type lift_op =
  | NonReifiableLift of term
  | ReifiableLift    of term & term //lift_wp, lift
  | LiftForFree      of term

type lift = {
  msource: lid;
  mdest:   lid;
  lift_op: lift_op;
  braced: bool; //a detail: for incremental parsing, we need to know if it is delimited by bracces  
}

type pragma =
  | ShowOptions
  | SetOptions of string
  | ResetOptions of option string
  | PushOptions of option string
  | PopOptions
  | RestartSolver
  | PrintEffectsGraph
  | Check of term

type dep_scan_callbacks = {
   scan_term: term -> unit;
   scan_binder: binder -> unit;
   scan_pattern: pattern -> unit;
   add_lident: lident -> unit;
   add_open: lident -> unit;
}

type to_be_desugared = {
  lang_name: string;
  blob: FStarC.Dyn.dyn;
  idents: list ident;
  to_string: FStarC.Dyn.dyn -> string;
  eq: FStarC.Dyn.dyn -> FStarC.Dyn.dyn -> bool;
  dep_scan: dep_scan_callbacks -> FStarC.Dyn.dyn -> unit
}

type decl' =
  | TopLevelModule of lid
  | Open of lid & FStarC.Syntax.Syntax.restriction
  | Friend of lid
  | Include of lid & FStarC.Syntax.Syntax.restriction
  | ModuleAbbrev of ident & lid
  | TopLevelLet of let_qualifier & list (pattern & term)
  | Tycon of bool & bool & list tycon
    (* first bool is for effect *)
    (* second bool is for typeclass *)
  | Val of ident & term  (* bool is for logic val *)
  | Exception of ident & option term
  | NewEffect of effect_decl
  | LayeredEffect of effect_decl
  | SubEffect of lift
  | Polymonadic_bind of lid & lid & lid & term
  | Polymonadic_subcomp of lid & lid & term
  | Pragma of pragma
  | Assume of ident & term
  | Splice of bool & list ident & term  (* bool is true for a typed splice *)
  (* The first range is the entire range of the blob.
     The second range is the start point of the extension syntax itself *)
  | DeclSyntaxExtension of string & string & range & range
  | UseLangDecls of string
  | DeclToBeDesugared of to_be_desugared
  | Unparseable

and decl = {
  d:decl';
  drange:range;
  quals: qualifiers;
  attrs: attributes_;
  interleaved: bool;
}
and effect_decl =
  (* KM : Is there really need of the generality of decl here instead of e.g. lid * term ? *)
  | DefineEffect   of ident & list binder & term & list decl
  | RedefineEffect of ident & list binder & term

instance val hasRange_decl : hasRange decl

type modul =
  | Module {
    no_prelude : bool;
    mname : lid;
    decls : list decl;
  }
  | Interface {
    no_prelude : bool;
    mname : lid;
    decls : list decl;
    admitted : bool; (* flag to mark admitted interfaces *)
  }
type file = modul
type inputFragment = either file (list decl)

val lid_of_modul : modul -> lid

(* Smart constructors *)
val mk_decl : decl' -> range -> list decoration -> decl
val add_decorations: decl -> list decoration -> decl
val mk_binder_with_attrs : binder' -> range -> level -> aqual -> list term -> binder
val mk_binder : binder' -> range -> level -> aqual -> binder
val mk_term : term' -> range -> level -> term

val mk_uminus : term -> range -> range -> level -> term
val mk_pattern : pattern' -> range -> pattern

val un_curry_abs : list pattern -> term -> term'
val mk_function : list branch -> range -> range -> term
val un_function : pattern -> term -> option (pattern & term)

val consPat : range -> pattern -> pattern -> pattern'
val consTerm : range -> term -> term -> term

val unit_const : range -> term
val ml_comp : term -> term
val tot_comp : term -> term

val mkApp : term -> list (term & imp) -> range -> term
val mkExplicitApp : term -> list term -> range -> term

val mkRefSet : range -> list term -> term

val focusLetBindings : list (bool & (pattern & term)) -> range -> list (pattern & term)
val focusAttrLetBindings : list (option attributes_ & (bool & (pattern & term))) -> range -> list (option attributes_ & (pattern & term))

val mkFsTypApp : term -> list term -> range -> term
val mkTuple : list term -> range -> term
val mkDTuple : list term -> range -> term
val mkRefinedBinder : ident -> term -> bool -> option term -> range -> aqual -> list term -> binder
val mkRefinedPattern : pattern -> term -> (*should_bind_pat:*)bool -> option term -> range -> range -> pattern
val extract_named_refinement : bool -> term -> option (ident & term & option term)

val as_frag : list decl -> inputFragment

// TODO: Move to something like FStarC.Util
val strip_prefix : string -> string -> option string

val compile_op : int -> string -> range -> string
val compile_op' : string -> range -> string
val string_to_op : string -> option (string & option int) // returns operator symbol and optional arity

val string_of_fsdoc : string & list (string & string) -> string
val string_of_let_qualifier : let_qualifier -> string

val term_to_string : term -> string

val lids_of_let : list (pattern & term) -> list lident
val id_of_tycon : tycon -> string

val string_of_pragma : pragma -> string
val pat_to_string : pattern -> string
val binder_to_string : binder -> string
val modul_to_string : modul -> string
val decl_to_string : decl -> string

val decl_is_val : ident -> decl -> bool

val thunk : term -> term

val check_id : ident -> unit

val ident_of_binder : range -> binder -> ident
val idents_of_binders : list binder -> range -> list ident

instance val showable_decl : showable decl
instance val showable_term : showable term
instance val showable_pattern : showable pattern
instance val showable_binder : showable binder
instance val showable_modul   : showable modul
instance val showable_pragma : showable pragma

val as_interface (m:modul) : modul

val inline_let_attribute : term
val inline_let_vc_attribute : term
