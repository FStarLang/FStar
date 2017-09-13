module FStar.Reflection.Data

open FStar.Reflection.Types

noeq
type vconst =
  | C_Unit : vconst
  | C_Int : int -> vconst // Not exposing the full details of our integer repr.
  | C_True : vconst
  | C_False : vconst
  | C_String : string -> vconst
  (* TODO: complete *)

// This is shadowing `pattern` from Prims (for smt_pats)
noeq
type pattern =
    | Pat_Constant : vconst -> pattern                   // A built-in constant
    | Pat_Cons     : fv -> list pattern -> pattern      // A fully applied constructor
    | Pat_Var      : binder -> pattern                  // Pattern bound variable
    | Pat_Wild     : binder -> pattern                  // Wildcard (GM: why is this not Pat_var too?)

type branch = pattern * term  // | pattern -> term

type aqualv =
    | Q_Implicit
    | Q_Explicit

type argv = term * aqualv

noeq
type term_view =
  | Tv_Var    : binder -> term_view
  | Tv_FVar   : fv -> term_view
  | Tv_App    : term -> argv -> term_view
  | Tv_Abs    : binder -> term -> term_view
  | Tv_Arrow  : binder -> term -> term_view
  | Tv_Type   : unit -> term_view
  | Tv_Refine : binder -> term -> term_view
  | Tv_Const  : vconst -> term_view
  | Tv_Uvar   : int -> typ -> term_view
  | Tv_Let    : binder -> term -> term -> term_view
  | Tv_Match  : term -> list branch -> term_view
  | Tv_Unknown : term_view // Baked in "None"

noeq
type ctor =
  | Ctor :
    (name:name) ->              // constructor name "C"
    (typ:typ) ->                // type of the constructor "C : xn:tn -> I ps"
    ctor

noeq
type sigelt_view =
  // Sg_Inductive basically coallesces the Sig_bundle used internally,
  // where the type definition and its constructors are split.
  // While that might be better for typechecking, this is probably better for metaprogrammers
  // (no mutually defined types for now)
  | Sg_Inductive :
      (name:name) ->            // name of the inductive type being defined
      (params:binders) ->       // parameters
      (typ:typ) ->              // the type annotation for the inductive, i.e., indices -> Type #u
      list ctor ->              // constructors
      sigelt_view

  | Sg_Let :
      (fv:fv) ->
      (typ:typ) ->
      (def:term) ->
      sigelt_view

  | Unk
