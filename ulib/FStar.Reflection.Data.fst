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
    | Pat_Constant : vconst -> pattern              // A built-in constant
    | Pat_Cons     : fv -> list pattern -> pattern  // A fully applied constructor
    | Pat_Var      : bv -> pattern                  // Pattern bound variable
    | Pat_Wild     : bv -> pattern                  // Wildcard (GM: why is this not Pat_var too?)
    | Pat_Dot_Term : bv -> term -> pattern          // Dot pattern: resolved by other elements in the pattern and type

type branch = pattern * term  // | pattern -> term

type aqualv =
    | Q_Implicit
    | Q_Explicit

type argv = term * aqualv

noeq
type bv_view = {
    bv_ppname : string;
    bv_index : int;
    bv_sort : typ;
}

noeq
type term_view =
  | Tv_Var    : v:bv -> term_view
  | Tv_BVar   : v:bv -> term_view
  | Tv_FVar   : v:fv -> term_view
  | Tv_App    : hd:term -> a:argv -> term_view
  | Tv_Abs    : bv:binder -> body:term -> term_view
  | Tv_Arrow  : bv:binder -> c:comp -> term_view
  | Tv_Type   : unit -> term_view
  | Tv_Refine : bv:bv -> ref:term -> term_view
  | Tv_Const  : vconst -> term_view
  | Tv_Uvar   : int -> ctx_uvar_and_subst -> term_view
  | Tv_Let    : recf:bool -> bv:bv -> def:term -> body:term -> term_view
  | Tv_Match  : scrutinee:term -> brs:(list branch) -> term_view
  | Tv_AscribedT : e:term -> t:term -> tac:option term -> term_view
  | Tv_AscribedC : e:term -> c:comp -> tac:option term -> term_view  
  | Tv_Unknown  : term_view // Baked in "None"

// Very basic for now
noeq
type comp_view =
  | C_Total     : ret:typ -> decr:(option term) -> comp_view
  | C_Lemma     : term -> term -> comp_view // pre & post
  | C_Unknown   : comp_view

noeq
type sigelt_view =
  | Sg_Let :
      (r:bool) ->
      (fv:fv) ->
      (us:list univ_name) ->
      (typ:typ) ->
      (def:term) ->
      sigelt_view

  // Sg_Inductive basically coallesces the Sig_bundle used internally,
  // where the type definition and its constructors are split.
  // While that might be better for typechecking, this is probably better for metaprogrammers
  // (no mutually defined types for now)
  | Sg_Inductive :
      (nm:name) ->              // name of the inductive type being defined
      (univs:list univ_name) -> // universe variables
      (params:binders) ->       // parameters
      (typ:typ) ->              // the type annotation for the inductive, i.e., indices -> Type #u
      (cts:list name) ->        // constructor names
      sigelt_view

  | Sg_Constructor :
      (name:name) ->
      (typ:typ) ->
      sigelt_view

  | Unk

let var : eqtype = nat

type exp : Type =
  | Unit : exp
  | Var : var -> exp
  | Mult : exp -> exp -> exp


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

    | Tv_AscribedT e ty tac ->
      e << t /\ ty << t /\ tac << t

    | Tv_AscribedC e c tac ->
      e << t /\ c << t /\ tac << t

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
    | C_Total t md ->
        t << c /\ (match md with | Some d -> d << c | None -> True)
    | C_Lemma pre post ->
        pre << c /\ post << c
    | C_Unknown ->
        True

val smaller_bv : bv_view -> bv -> Type0
let smaller_bv bvv bv =
    bvv.bv_sort << bv

val smaller_binder : binder -> (bv * aqualv) -> Type0
let smaller_binder b (bv, _) =
    bv << b
