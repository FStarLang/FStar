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
    | Pat_Constant : vconst -> pattern                  // A built-in constant
    | Pat_Cons     : fv -> list pattern -> pattern      // A fully applied constructor
    | Pat_Var      : binder -> pattern                  // Pattern bound variable
    | Pat_Wild     : binder -> pattern                  // Wildcard (GM: why is this not Pat_var too?)

type branch = pattern * term  // | pattern -> term

type aqualv =
    | Q_Implicit
    | Q_Explicit

type argv = term * aqualv

noeq
type bv_view = {
    ppname : string;
    index : int;
    sort : typ;
}

noeq
type term_view =
  | Tv_Var    : bv -> term_view
  | Tv_BVar   : bv -> term_view
  | Tv_FVar   : fv -> term_view
  | Tv_App    : term -> argv -> term_view
  | Tv_Abs    : binder -> term -> term_view
  | Tv_Arrow  : binder -> comp -> term_view
  | Tv_Type   : unit -> term_view
  | Tv_Refine : bv -> term -> term_view
  | Tv_Const  : vconst -> term_view
  | Tv_Uvar   : int -> typ -> term_view
  | Tv_Let    : bool -> bv -> term -> term -> term_view
  | Tv_Match  : term -> list branch -> term_view
  | Tv_Unknown : term_view // Baked in "None"

// Very basic for now
noeq
type comp_view =
  | C_Total     : typ -> comp_view
  | C_Lemma     : term -> term -> comp_view // pre & post
  | C_Unknown   : comp_view

noeq
type sigelt_view =
  | Sg_Let :
      (r:bool) ->
      (fv:fv) ->
      (typ:typ) ->
      (def:term) ->
      sigelt_view

  // Sg_Inductive basically coallesces the Sig_bundle used internally,
  // where the type definition and its constructors are split.
  // While that might be better for typechecking, this is probably better for metaprogrammers
  // (no mutually defined types for now)
  | Sg_Inductive :
      (nm:name) ->              // name of the inductive type being defined
      (params:binders) ->       // parameters
      (typ:typ) ->              // the type annotation for the inductive, i.e., indices -> Type #u
      (cts:list name) ->        // constructor names
      sigelt_view

  | Sg_Constructor :
      (name:name) ->
      (typ:typ) ->
      sigelt_view

  | Unk

type decls = list sigelt

let rec forall_list (p:'a -> Type) (l:list 'a) : Type =
    match l with
    | [] -> True
    | x::xs -> p x /\ forall_list p xs

(* Comparison of a term_view to term. Allows to recurse while changing the view *)
val smaller : term_view -> term -> Type0
let smaller tv t =
    match tv with
    | Tv_App l r ->
        l << t /\ r << t /\ fst r << t

    | Tv_Abs b t'
    | Tv_Arrow b t' ->
        b << t /\ t' << t

    | Tv_Refine b t' ->
        bv << t /\ t' << t

    | Tv_Let r bv t1 t2 ->
        bv << t /\ t1 << t /\ t2 << t

    | Tv_Match t1 brs ->
        t1 << t /\ (forall_list (fun (b, t') -> t' << t) brs)

    | Tv_Type _
    | Tv_Const _
    | Tv_Unknown
    | Tv_Var _
    | Tv_BVar _
    | Tv_Uvar _ _
    | Tv_FVar _ -> True

val smaller_comp : comp_view -> comp -> Type0
let smaller_comp cv c =
    match cv with
    | C_Total t ->
        t << c
    | C_Lemma pre post ->
        pre << c /\ post << c
    | C_Unknown ->
        True

val smaller_bv : bv_view -> bv -> Type0
let smaller_bv bvv bv =
    bvv.sort << bv

val smaller_binder : binder -> (bv * aqualv) -> Type0
let smaller_binder b (bv, _) =
    bv << b
