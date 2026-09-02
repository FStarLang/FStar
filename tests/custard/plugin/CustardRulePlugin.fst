module CustardRulePlugin

(* Section 34: a worked {!FStarC.Custard.Builtins.register_rule} example.

   A rule is the extension point for a symbol that F* declares but does not
   define, or defines in a way that is not what the target should run.  It is
   consulted in step 1 of the extraction loop, before the definition is looked
   up, so a name with a rule is never requested and never appears in the
   output; the rule builds an IR term from the call's arguments instead.

   The interesting case, and the one this file exists to demonstrate, is a
   rule whose argument is *compile-time input to code generation*: a
   descriptor that says what to emit, which has no runtime representation and
   is not meant to have one.  The rule reads it, emits something else, and the
   descriptor's types are then unreachable and dead-code elimination removes
   them -- so the fact that they have no C layout never comes up.

   Two facts about the arguments a rule receives, which are what this test
   pins:

   - They are *reduced*.  A [let]-bound descriptor is unfolded before the rule
     sees it, provided the definition is one the extractor may unfold, so a
     record literal arrives as a record literal and a list literal as a chain
     of [Prims.Cons].  It is not an opaque reference to the [let].

   - They are *pre-layout*.  Rules run during extraction, before section 6's
     passes, so a single-constructor type is still an [ECtor] and not yet the
     [ERecord] the final dump shows, and an argument that the layout analysis
     would later erase is still present.  Match on the constructor, not on the
     representation. *)

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Class.Show
open FStarC.Const
open FStarC.Custard.Syntax

module B      = FStarC.Custard.Builtins
module Ident  = FStarC.Ident
module BU     = FStarC.Util

(* The shape of a node, for the error messages below.  A rule that silently
   accepts the wrong shape is worse than one that stops: the wrong shape means
   the descriptor did not reduce, and the resulting program would be wrong
   rather than absent. *)
let tag (e:expr) : string =
  match e.e with
  | EConst _   -> "a constant"
  | EVar _     -> "a local variable"
  | EQual _    -> "a reference to a top-level definition"
  | ELet _     -> "a let"
  | EApp _     -> "an application"
  | EFun _     -> "a lambda"
  | EMatch _   -> "a match"
  | EIf _      -> "an if"
  | ESeq _     -> "a sequence"
  | ECtor _    -> "a constructor application"
  | ETuple _   -> "a tuple"
  | ERecord _  -> "a record literal"
  | EProj _    -> "a projection"
  | EDiscrim _ -> "a discriminator"
  | ECoerce _  -> "a coercion"
  | ECast _    -> "a cast"
  | EAny       -> "an arbitrary value"
  | EAbort _   -> "an abort"
  | EOp _      -> "a primitive operation"
  | EWhile _   -> "a while"
  | ERaise _   -> "a raise"
  | ETry _     -> "a try"

let die (#a:Type) (what:string) (e:expr) : ML a =
  failwith ("CustardRulePlugin: expected " ^ what ^ ", but the argument arrived as "
            ^ tag e ^ ":\n" ^ show e)

(* A field of a single-constructor value.  Pre-layout it is an [ECtor] whose
   arguments are positional, so the field is selected by index; the [ERecord]
   case is here because a rule must not depend on which of the two it gets. *)
let field_at (i:int) (fname:string) (e:expr) : ML expr =
  match e.e with
  | ECtor (_, args) ->
    if i < List.length args then List.nth args i else die "a wider constructor" e
  | ERecord (_, fs) ->
    (match BU.try_find (fun (f, _) -> f = fname) fs with
     | Some (_, v) -> v
     | None -> die ("a record with a field " ^ fname) e)
  | _ -> die "a constructor application or record literal" e

(* [Prims.Cons]/[Prims.Nil] as they arrive: a constructor application named by
   its lid.  [Cons] carries the element type as an argument in some spines and
   not others, so the *last two* arguments are the head and the tail. *)
let rec elements (e:expr) : ML (list expr) =
  match e.e with
  | ECtor (n, args) ->
    let id = n.id in
    if id = "Nil" then []
    else if id = "Cons" then
      (match List.rev args with
       | tl :: hd :: _ -> hd :: elements tl
       | _ -> die "a two-argument Cons" e)
    else die "Prims.Nil or Prims.Cons" e
  | _ -> die "a list literal" e

let int_of_const (e:expr) : ML string =
  match e.e with
  | EConst (CInt (s, _)) -> s
  | _ -> die "an integer literal" e

(* The rule proper.

   [CustardRuleTest.launch d n] is an [assume val]: it has no F* definition,
   and without a rule Custard would emit a [DExternal] for it and then reject
   the program, because [d]'s type stores a [Type0] that a later field's type
   mentions and so has no C layout (section 30.3, error 368).

   With the rule, [d] is read here and never reaches the backend.  What is
   emitted is [n] plus the total size the descriptor asks for -- a number this
   plugin computed at extraction time out of a separation of concerns that
   exists only in F*. *)
(* [DArr (ty:Type0) (s:sized ty) (len:nat)] arrives as [DArr(s, len)]: the
   type argument is erased on the way in, so [s] is at index 0, and [sz] is
   the first of [sized]'s two fields. *)
let size_of_desc (d:expr) : ML int =
  BU.int_of_string (int_of_const (field_at 0 "sz" (field_at 0 "s" d)))

let rec total_size (ds : list expr) : ML int =
  match ds with
  | []      -> 0
  | d :: ds -> size_of_desc d + total_size ds

let launch (tys : list cty) (args : list expr) : ML expr =
  match args with
  | [d; n] ->
    let n_bytes = total_size (elements (field_at 1 "shmems" d)) in
    let lit = mk (EConst (CInt (show n_bytes, Some (Unsigned, Int32))))
                 n.ty E_Pure in
    mk (EOp ({ po_op = Add; po_int = Some (Unsigned, Int32) }, [n; lit]))
       n.ty E_Pure
  | _ -> failwith "CustardRulePlugin: launch applied to the wrong number of arguments"

let _ =
  B.register_rule (Ident.lid_of_str "CustardRuleTest.launch") (B.Rule_prim (2, launch))
