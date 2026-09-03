(*
   Copyright 2008-2025 Microsoft Research

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
module FStarC.Custard.PrintKrml

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Class.Show
open FStarC.Const
open FStarC.Custard.Syntax

module K    = FStarC.Extraction.KrmlAst
module Krml = FStarC.Extraction.Krml
module SMap = FStarC.SMap
module BU   = FStarC.Util
module E    = FStarC.Errors
module Options = FStarC.Options
module B    = FStarC.Custard.Builtins

open FStarC.Errors.Msg

(* -------------------------------------------------------------------- *)
(* Environment                                                          *)
(* -------------------------------------------------------------------- *)

(* karamel's terms are in De Bruijn form, so the only state the translation
   needs is the two scopes.  [ctor_arity] is here because karamel has no
   discriminator node: [Foo? e] has to become a match, and writing the match
   requires knowing how many fields to ignore. *)
type kenv = {
  names:      list string;
  names_t:    list string;
  ctor_arity: SMap.t int;
  (* An external symbol has no type-parameter list in karamel's AST -- and C has
     no polymorphism to give it one -- so a type variable in its signature is
     approximated by [any] instead of being reported as unbound. *)
  tvars_any:  bool;
}

let extend (env:kenv) (x:string) : kenv = { env with names = x :: env.names }
let extend_t (env:kenv) (x:string) : kenv = { env with names_t = x :: env.names_t }

let find (env:kenv) (x:string) : ML int =
  try List.index (fun y -> y = x) env.names
  with _ -> failwith ("Custard: unbound variable " ^ x ^ " reached the karamel backend")

let find_t (env:kenv) (x:string) : ML int =
  try List.index (fun y -> y = x) env.names_t
  with _ -> failwith ("Custard: unbound type variable " ^ x ^ " reached the karamel backend")

(* A name for a binder Custard invents, that no reference in scope can resolve
   to.  [find] takes the first match, so reusing a name already bound would
   capture every outer use of it. *)
let fresh_local (env:kenv) (base:string) : ML string =
  let rec go (n:int) : ML string =
    let x = if n = 0 then base else base ^ show n in
    if env.names |> List.existsb (fun y -> y = x) then go (n + 1) else x in
  go 0

(* -------------------------------------------------------------------- *)
(* Names                                                                *)
(* -------------------------------------------------------------------- *)

(* karamel joins an lident with underscores to make a C identifier, so the
   namespace may as well be the F* one -- and it has to be, because karamel
   recognizes its own builtins ([Prims.op_Addition], the [FStar.UInt32]
   operators, the Pulse primitives) by their fully qualified name.  Only the
   specialization suffix is new. *)
let lident_of_name (n:name) : ML K.lident =
  (* Every value name reaches karamel through here, which is what
     [B.krml_compat_name] needs: mapping a reference but not the declaration it
     resolves to renames the use away from its own definition.  Before the
     specialization suffix, since the table is keyed on the source name. *)
  let ns, id = B.krml_compat_name n.ns n.id in
  let id = match n.spec with
           | None -> id
           | Some s -> id ^ "__" ^ s in
  (ns, id)

(* The external types of the program being printed, by mangled name, mapped to
   the C name they are declared under.  karamel does not prefix an lident whose
   namespace is empty, so an entry here reaches the C output verbatim. *)
let extern_types : ref (SMap.t string) = mk_ref (SMap.create 0)

let type_lident_of_name (n:name) : ML K.lident =
  let lid = lident_of_name n in
  match SMap.try_find !extern_types (string_of_name n) with
  | Some t -> ([], t)
  | None -> lid

(* [FStar.Pervasives.Native.tupleN] and its constructor, recognized by name
   because that is all a printer has.  Only ever true on the Rust path: on
   every other the declaration is compiled and these are ordinary names. *)
let is_tuple_type_name (n:name) : ML bool =
  n.ns = ["FStar"; "Pervasives"; "Native"] &&
  FStarC.Util.starts_with n.id "tuple" &&
  Options.custard_backend () = "KrmlRust"

let is_tuple_ctor_name (n:name) : ML bool =
  n.ns = ["FStar"; "Pervasives"; "Native"] &&
  FStarC.Util.starts_with n.id "Mktuple" &&
  Options.custard_backend () = "KrmlRust"

(* Section 38.  karamel's [width] carries the two float formats itself, so
   this is a rename and nothing more. *)
let krml_fwidth (fw:fwidth) : K.width =
  match fw with
  | Float32 -> K.Float32
  | Float64 -> K.Float64

(* Section 43.2.  karamel's [EConstant] carries the literal as text, and what
   may go in that text depends on who reads it back.

   The Rust backend prints it very nearly verbatim, and Rust spells every base
   exactly as F* does, so Rust keeps all four.  karamel's C path does not print
   it verbatim -- something on the way renormalizes -- and an octal [017] comes
   back out as decimal *seventeen*.  So the C path is given only the base that
   survives the trip, and decimal for the rest.  A base is for the reader; the
   value is not negotiable. *)
let krml_int_lit (v:int) (b:int_base) : ML string =
  if Options.custard_backend () = "KrmlRust" then int_lit_to_string v b
  else match b with
       | Hex -> int_lit_to_string v Hex
       | _   -> int_lit_to_string v Dec

(* Section 43.3.  karamel's C printer has no suffix for [Float32]
   (karamel/lib/PrintC.ml:245 falls through to [empty]), so a binary32 constant
   goes out bare -- which is a [double] -- and the [(float)] karamel then
   inserts fixes the type and not the value.  Decimal to binary64 to binary32
   is a double rounding, and for some decimals the two land on different
   floats.  Writing the suffix here makes the literal a [float] before the cast
   sees it, and the cast becomes the no-op it was meant to be.

   Not on the Rust path, where the suffix is [f32] and karamel writes it, and
   not at [Float64], where bare is already [double]. *)
let krml_float_lit (fw:fwidth) (v:float_lit) : ML string =
  let s = float_lit_to_string v in
  if Float32? fw && Options.custard_backend () = "KrmlC" then s ^ "f" else s

let krml_width (sw : signedness & width) : K.width =
  match sw with
  | (Signed, Int8) -> K.Int8
  | (Signed, Int16) -> K.Int16
  | (Signed, Int32) -> K.Int32
  | (Signed, Int64) -> K.Int64
  | (Signed, Sizet) -> K.PtrdiffT
  | (Unsigned, Int8) -> K.UInt8
  | (Unsigned, Int16) -> K.UInt16
  | (Unsigned, Int32) -> K.UInt32
  | (Unsigned, Int64) -> K.UInt64
  | (Unsigned, Sizet) -> K.SizeT

let krml_op (o:op) : K.op =
  match o with
  | Add -> K.Add | AddW -> K.AddW | Sub -> K.Sub | SubW -> K.SubW
  | Mult -> K.Mult | MultW -> K.MultW | Div -> K.Div | DivW -> K.DivW
  | Mod -> K.Mod
  | BOr -> K.BOr | BAnd -> K.BAnd | BXor -> K.BXor
  | BShiftL -> K.BShiftL | BShiftR -> K.BShiftR | BNot -> K.BNot
  | Eq -> K.Eq | Neq -> K.Neq | Lt -> K.Lt | Lte -> K.Lte
  | Gt -> K.Gt | Gte -> K.Gte
  | And -> K.And | Or -> K.Or | Not -> K.Not

(* -------------------------------------------------------------------- *)
(* Types                                                                *)
(* -------------------------------------------------------------------- *)

(* The primitive types karamel knows natively.  Everything else is a
   [TQualified], which karamel resolves against the declarations we emit. *)
let prim_type (n:name) : option K.typ =
  match String.concat "." (n.ns @ [n.id]) with
  | "Prims.unit" -> Some K.TUnit
  | "Prims.bool" -> Some K.TBool
  | "Prims.int" -> Some (K.TInt K.CInt)
  | "Prims.string" -> Some (K.TQualified (["Prims"], "string"))
  | _ -> None

(* The definitions karamel supplies itself.  It prepends a [Prims] file of its
   own to every program ([Krml.Builtin.prepare]) holding the arithmetic on
   [Prims.int] -- which it compiles to [krml_checked_int_t], a machine integer
   with an overflow check, since C has no unbounded integer.  Custard reaches
   the same operators as ordinary externals, and emitting a declaration for
   one is a duplicate that karamel rejects outright ("duplicate global name in
   identical namespace").  Ours is the one to drop: karamel's is what its own
   translation of the *uses* refers to. *)
let karamel_declares (n:name) : ML bool =
  let ns, id = lident_of_name n in
  match String.concat "." (ns @ [id]) with
  | "Prims.op_Addition"
  | "Prims.op_Subtraction"
  | "Prims.op_Multiply"
  | "Prims.op_Division"
  | "Prims.op_Modulus"
  | "Prims.op_Minus"
  | "Prims.op_LessThan"
  | "Prims.op_LessThanOrEqual"
  | "Prims.op_GreaterThan"
  | "Prims.op_GreaterThanOrEqual"
  | "Prims.pow2"
  | "Prims.abs"
  | "Prims.strcat"
  | "Prims.string_of_int" -> true
  | _ -> false

let rec krml_typ (env:kenv) (t:cty) : ML K.typ =
  match t with
  | TUnit -> K.TUnit
  | TAny -> K.TAny
  (* karamel has no exceptions; every *use* of one is already an [EAbortS],
     so the type only has to be something it can carry. *)
  | TExn -> K.TAny
  | TInt sw -> K.TInt (krml_width sw)
  | TFloat fw -> K.TInt (krml_fwidth fw)
  | TVar x -> if env.tvars_any then K.TAny else K.TBound (find_t env x)
  | TArrow (a, _, b) -> K.TArrow (krml_typ env a, krml_typ env b)
  | TTuple ts -> K.TTuple (ts |> List.map (krml_typ env))
  (* karamel has no separate reference type: a [ref] is a one-element buffer,
     which is exactly what the operations on it already say. *)
  | TBuf t | TRef t -> K.TBuf (krml_typ env t)
  | TApp (n, []) ->
    (match prim_type n with
     | Some t -> t
     | None -> K.TQualified (type_lident_of_name n))
  (* Section 20.  On the Rust path a tuple has to reach karamel as a tuple:
     [split_at]'s result is destructured by [OptimizeMiniRust.retrieve_pair_
     type], which fails -- crashes, rather than reporting -- on anything that
     is not [Tuple [t; t]].  The type stays polymorphic and undeclared
     ([Builtins.is_krml_model_name]) so that it is still an application here
     and its arguments are still visible. *)
  | TApp (n, args) when is_tuple_type_name n -> K.TTuple (args |> List.map (krml_typ env))
  | TApp (n, args) -> K.TApp (type_lident_of_name n, args |> List.map (krml_typ env))

let binder_of (env:kenv) (b:binder) : ML K.binder =
  { K.name = b.b_name; K.typ = krml_typ env b.b_ty; K.mut = false; K.meta = [] }

let dummy_binder (x:string) : K.binder =
  { K.name = x; K.typ = K.TAny; K.mut = false; K.meta = [] }

(* -------------------------------------------------------------------- *)
(* Constants                                                            *)
(* -------------------------------------------------------------------- *)

let krml_const (c:constant) : ML K.expr =
  match c with
  | CUnit -> K.EUnit
  | CBool b -> K.EBool b
  | CString s -> K.EString s
  (* karamel's [EConstant] carries the literal as text, so this is where the
     value is spelled again -- in whichever base the target reads back
     unchanged (section 43.2). *)
  | CInt (v, b, None) -> K.EConstant (K.CInt, krml_int_lit v b)
  | CInt (v, b, Some sw) -> K.EConstant (krml_width sw, krml_int_lit v b)
  | CFloat (v, fw) -> K.EConstant (krml_fwidth fw, krml_float_lit fw v)
  (* karamel has no character type; a program that reaches this is not a C
     program, and saying so here is better than emitting something that means
     something else. *)
  | CChar _ -> K.EAbortS "Custard: character constants are not supported by the C backend"

(* Section 44.1.  A construct karamel's AST cannot hold has to stop the
   extraction, and it has to say so the way the C backend says it: a numbered
   diagnostic naming the construct, not a [failwith].  The three sites that
   used one also said "the C backend" from a file that is not it, which sends
   a reader looking in the wrong printer. *)
let krml_reject (#a:Type) (what:string) : ML a =
  E.raise_error0 E.Error_CustardNoCRepresentation
    [text ("Custard: " ^ what ^ " has no karamel representation.");
     text "The karamel backend's AST has no node for it, so there is no \
           translation to give.  The direct C backend (--custard_backend C) \
           may accept it."]

(* -------------------------------------------------------------------- *)
(* Patterns                                                             *)
(* -------------------------------------------------------------------- *)

(* Pattern variables are bound left to right, and the environment threaded
   through says in which order karamel will see them. *)
let rec krml_pat (env:kenv) (p:pat) : ML (kenv & K.pattern) =
  match p with
  | PWild -> (extend env "_", K.PVar (dummy_binder "_"))
  | PVar x -> (extend env x, K.PVar (dummy_binder x))
  | PConst CUnit -> (env, K.PUnit)
  | PConst (CBool b) -> (env, K.PBool b)
  | PConst (CInt (v, b, None)) -> (env, K.PConstant (K.CInt, krml_int_lit v b))
  | PConst (CInt (v, b, Some sw)) ->
    (env, K.PConstant (krml_width sw, krml_int_lit v b))
  (* Section 44.1.  karamel's [pattern] has no case for a string, float or
     character constant.  This used to fall to a fresh variable pattern -- and
     a variable pattern matches *everything*, so the branch swallowed the
     scrutinee and every branch after it was dead code, with no diagnostic on
     either krml backend.  A pattern the backend cannot translate has to stop
     the extraction, as [POr] above already does: the alternative is not a
     worse translation, it is a different program. *)
  | PConst c ->
    let what =
      match c with
      | CString _ -> "a string pattern"
      | CFloat _ -> "a floating-point pattern"
      | CChar _ -> "a character pattern"
      | _ -> "this constant pattern" in
    krml_reject what
  | PCtor (n, ps) when is_tuple_ctor_name n ->
    let env, ps = krml_pats env ps in
    (env, K.PTuple ps)

  | PCtor (n, ps) ->
    let env, ps = krml_pats env ps in
    (env, K.PCons (mangled_name n, ps))
  | PRecord (_, fs) ->
    let env, ps = krml_pats env (fs |> List.map snd) in
    (env, K.PRecord (List.zip (fs |> List.map fst) ps))
  | PTuple ps ->
    let env, ps = krml_pats env ps in
    (env, K.PTuple ps)
  (* karamel has no or-pattern; the first alternative is not a sound choice, so
     refuse rather than miscompile. *)
  | POr _ ->
    krml_reject "a pattern disjunction"

and krml_pats (env:kenv) (ps:list pat) : ML (kenv & list K.pattern) =
  match ps with
  | [] -> (env, [])
  | p :: ps ->
    let env, p = krml_pat env p in
    let env, ps = krml_pats env ps in
    (env, p :: ps)

(* -------------------------------------------------------------------- *)
(* Expressions                                                          *)
(* -------------------------------------------------------------------- *)

let rec krml_expr (env:kenv) (e:expr) : ML K.expr =
  match e.e with
  | EConst c -> krml_const c
  | EVar x -> K.EBound (find env x)
  | EQual (n, []) -> K.EQualified (lident_of_name n)
  | EQual (n, tys) ->
    K.ETypApp (K.EQualified (lident_of_name n), tys |> List.map (krml_typ env))

  | ELet (x, t, e1, e2) ->
    let b = { K.name = x; K.typ = krml_typ env t; K.mut = false; K.meta = [] } in
    K.ELet (b, krml_expr env e1, krml_expr (extend env x) e2)

  | EApp (hd, args) -> K.EApp (krml_expr env hd, args |> List.map (krml_expr env))

  | EFun (bs, body) ->
    let env' = bs |> List.fold_left (fun env (b:binder) -> extend env b.b_name) env in
    K.EFun (bs |> List.map (binder_of env), krml_expr env' body, krml_typ env body.ty)

  | EMatch (scrut, brs) ->
    K.EMatch (krml_expr env scrut, brs |> List.map (krml_branch env))

  | EIf (c, t, f) -> K.EIfThenElse (krml_expr env c, krml_expr env t, krml_expr env f)

  (* [ESequence] is variadic in karamel, but nesting is equivalent and keeps
     this a local rewrite.  karamel requires every element but the last to
     have type unit, though, so a discarded value has to be bound instead. *)
  | ESeq (e1, e2) when e1.ty = TUnit ->
    K.ESequence [krml_expr env e1; krml_expr env e2]
  | ESeq (e1, e2) ->
    (* [TAny] rather than [krml_typ env e1.ty]: a discarded value's type is of
       no interest to anyone, and Custard is happy to leave a call's result
       type as [TAny], which would then clash with what karamel infers.

       The name matters, and must not be [_].  karamel's use analysis, finding
       the binder unread, rewrites the binding into [let b = e1 in ignore b],
       and its Rust backend prints a binder's name verbatim: a binder named
       [_] then yields [ignore(_)], and [_] is not an expression in Rust.  (In
       C it is harmless, because that backend renames.)  Any ordinary
       identifier works, and karamel prepends its own [_] if the binder really
       does end up unread, which is what Rust wants anyway.

       Freshened against the enclosing scope because [find] resolves a
       reference by the *first* matching name: [Rename] gives a local its bare
       source spelling, so a program with its own [discarded] in scope would
       otherwise have every reference to it captured by this binder. *)
    let x = fresh_local env "discarded" in
    let b = { K.name = x; K.typ = K.TAny; K.mut = false; K.meta = [] } in
    K.ELet (b, krml_expr env e1, krml_expr (extend env x) e2)

  | ECtor (n, args) when is_tuple_ctor_name n ->
    K.ETuple (args |> List.map (krml_expr env))

  | ECtor (n, args) ->
    K.ECons (krml_typ env e.ty, mangled_name n, args |> List.map (krml_expr env))

  | ETuple es -> K.ETuple (es |> List.map (krml_expr env))

  | ERecord (_, fs) ->
    K.EFlat (krml_typ env e.ty, fs |> List.map (fun (f, x) -> (f, krml_expr env x)))

  | EProj (e1, _, f) -> K.EField (krml_typ env e1.ty, krml_expr env e1, f)

  (* karamel has no discriminator, so [Foo? e] becomes a match whose first
     branch ignores all of [Foo]'s fields and whose second is a catch-all --
     which in karamel is a variable pattern, there being no wildcard. *)
  | EDiscrim (e1, n) ->
    let arity = match SMap.try_find env.ctor_arity (mangled_name n) with
                | Some n -> n
                | None -> 0 in
    let wilds = List.map (fun _ -> K.PVar (dummy_binder "_")) (repeat_unit arity) in
    K.EMatch (krml_expr env e1,
              [ (K.PCons (mangled_name n, wilds), K.EBool true);
                (K.PVar (dummy_binder "_"), K.EBool false) ])

  (* Karamel has the one node; the distinction has already done its work in
     the passes above, and both are a cast in the C it emits. *)
  | ECast (e1, t) | ECoerce (e1, t) -> K.ECast (krml_expr env e1, krml_typ env t)

  (* The buffer operations are karamel nodes rather than operators: the C
     backend needs to see the address computation, not a call. *)
  | EOp ({ po_op = BufCreate l }, [init; len]) ->
    K.EBufCreate ((match l with LStack -> K.Stack | LHeap -> K.ManuallyManaged),
                  krml_expr env init, krml_expr env len)
  | EOp ({ po_op = BufRead }, [b; i]) ->
    K.EBufRead (krml_expr env b, krml_expr env i)
  | EOp ({ po_op = BufWrite }, [b; i; v]) ->
    K.EBufWrite (krml_expr env b, krml_expr env i, krml_expr env v)
  | EOp ({ po_op = BufSub }, [b; i]) ->
    K.EBufSub (krml_expr env b, krml_expr env i)
  | EOp ({ po_op = BufFree }, [b]) -> K.EBufFree (krml_expr env b)
  | EOp ({ po_op = BufNull }, []) ->
    K.EBufNull (match e.ty with TBuf t | TRef t -> krml_typ env t | _ -> K.TAny)
  | EOp ({ po_op = BufIsNull }, [b]) ->
    (* karamel has no [is_null], so compare against a null of the same type.
       Equality on pointers is the *polymorphic* one, and karamel types that
       only through an explicit type application naming the operand type -- as
       the [Eq]/[Neq] case below does.  Left as a bare [EOp (Eq, Bool)] the
       checker reads the width as the operand type, decides the arguments
       should be booleans, and drops the whole declaration as not Low\*. *)
    let t = match b.ty with TBuf t | TRef t -> krml_typ env t | _ -> K.TAny in
    let pt = K.TBuf t in
    K.EApp (K.ETypApp (K.EOp (K.Eq, K.Bool), [pt]),
            [krml_expr env b; K.EBufNull t])
  | EOp ({ po_op = BufBlit }, [src; srci; dst; dsti; len]) ->
    K.EBufBlit (krml_expr env src, krml_expr env srci,
                krml_expr env dst, krml_expr env dsti, krml_expr env len)

  (* Decidable equality at no particular width is *polymorphic*: karamel types
     it only through an explicit type application naming the operand type
     ([Checker.infer], the [ETApp (EOp (Eq|Neq), _)] case). *)
  | EOp ({ po_op = o; po_ty = None }, args)
      when (Eq? o || Neq? o) && Cons? args ->
    let t = match args with a :: _ -> krml_typ env a.ty | [] -> K.TAny in
    K.EApp (K.ETypApp (K.EOp (krml_op o, K.Bool), [t]),
            args |> List.map (krml_expr env))

  (* An operator is a value in karamel, so it is always applied. *)
  | EOp (o, args) ->
    let w = match o.po_ty with
            | Some (PInt sw) -> krml_width sw
            | Some (PFloat fw) -> krml_fwidth fw
            | None -> (match o.po_op with
                       (* [Eq]/[Neq] at no particular width is F*'s decidable
                          equality; karamel's convention for it is [Bool]. *)
                       | And | Or | Not | Eq | Neq -> K.Bool
                       | _ -> K.CInt) in
    K.EApp (K.EOp (krml_op o.po_op, w), args |> List.map (krml_expr env))

  | EWhile (c, body) -> K.EWhile (krml_expr env c, krml_expr env body)

  | EAny -> K.EAny
  | EAbort s -> K.EAbortS s

  | ERaise _ | ETry _ ->
    K.EAbortS "Custard: exceptions are not supported by the C backend"

and krml_branch (env:kenv) (br:branch) : ML K.branch =
  let p, g, body = br in
  let env', p = krml_pat env p in
  match g with
  | None -> (p, krml_expr env' body)
  | Some _ -> krml_reject "a pattern guard"

and repeat_unit (n:int) : ML (list unit) =
  if n <= 0 then [] else () :: repeat_unit (n - 1)

(* -------------------------------------------------------------------- *)
(* Declarations                                                         *)
(* -------------------------------------------------------------------- *)

let krml_flags (fs : list flag) : ML (list K.flag) =
  fs |> List.collect (fun f ->
    match f with
    | Private -> [K.Private]
    (* An erased declaration has no runtime content; telling karamel so lets it
       complain if one ever survives into C. *)
    | Erased -> [K.MustDisappear]
    (* Section 36.3.  These say nothing to Custard and everything to the C
       karamel emits, which is why they exist: a CUDA kernel *is* the
       [__global__] qualifier on its definition, and a plugin that lifts one
       has no other way to say so.  Carried through rather than interpreted --
       Custard does not know what the string means and does not need to. *)
    | Comment c -> [K.Comment c]
    | Prologue s -> [K.Prologue s]
    | Epilogue s -> [K.Epilogue s]
    | CInline -> [K.CInline]
    | _ -> [])

let with_typars (env:kenv) (ps : list string) : ML kenv =
  ps |> List.fold_left extend_t env

let krml_decl (env:kenv) (d:decl) : ML (option K.decl) =
  match d with
  (* A type karamel knows natively must not be redeclared: uses of it are
     translated to the native form, so the declaration would be dead at best
     and contradictory at worst. *)
  | DType { dt_name = n } when Some? (prim_type n) -> None
  | DLet l ->
    let env = with_typars env l.dl_typars in
    let n_t = List.length l.dl_typars in
    let flags = krml_flags l.dl_flags in
    let env' = l.dl_binders |> List.fold_left
                 (fun env (b:binder) -> extend env b.b_name) env in
    let body = krml_expr env' l.dl_body in
    (match l.dl_binders with
     | [] -> Some (K.DGlobal (flags, lident_of_name l.dl_name, n_t,
                              krml_typ env l.dl_ret, body))
     | bs -> Some (K.DFunction (None, flags, n_t, krml_typ env l.dl_ret,
                                lident_of_name l.dl_name,
                                bs |> List.map (binder_of env), body)))

  (* Section 20: karamel supplies a modelled *type* itself and recognizes it at
     the use, as [TApp (lid, [t])], which [krml_typ] already emits for any
     applied name.  A declaration here would be a second and conflicting
     answer to what the type is -- karamel drops its own models' type
     declarations for exactly that reason ([Builtin.make_abstract] keeps only
     abbreviations).  The model's *operations* are a different matter and are
     emitted: karamel's checker resolves every reference before the Rust pass
     rewrites it, so dropping them is "no corresponding implementation". *)
  | DType t when has_flag t.dt_flags Modelled -> None

  | DType t ->
    let env = with_typars env t.dt_params in
    let n_t = List.length t.dt_params in
    let flags = krml_flags t.dt_flags in
    let lid = lident_of_name t.dt_name in
    (match t.dt_body with
     | TAbbrev c -> Some (K.DTypeAlias (lid, flags, n_t, krml_typ env c))
     | TRecord fs ->
       Some (K.DTypeFlat (lid, flags, n_t,
                          fs |> List.map (fun (f, c) -> (f, (krml_typ env c, false)))))
     | TVariant cs ->
       Some (K.DTypeVariant (lid, flags, n_t,
               cs |> List.map (fun (cn, fs) ->
                 (mangled_name cn,
                  fs |> List.map (fun (f, c) -> (f, (krml_typ env c, false)))))))
     | TAbstract ->
       (* An external type is declared by a header karamel does not know
          about, so emitting an abstract struct for it would be a conflicting
          redeclaration.  Its uses already print as the plain C name. *)
       if t.dt_flags |> List.existsb Extern? then None
       else Some (K.DTypeAbstractStruct lid))

  | DExternal x when None? x.dx_target && karamel_declares x.dx_name -> None

  | DExternal x ->
    (* A [@@custard_extern "f"] symbol is declared under exactly that C name;
       karamel does not prefix a lident whose namespace is empty. *)
    let lid = match x.dx_target with
              | Some t -> ([], t)
              | None -> lident_of_name x.dx_name in
    (* Section 20.  An ordinary external's type variables print as [TAny],
       because the hand-written realization really is polymorphic and C's
       answer to that is a void pointer.  A model's do not: karamel is going
       to rewrite every use of it into a Rust operator, and Rust has no cast
       from [any] -- the translation fails outright with "no casts in Low* ->
       Rust".  The variables it binds are the right answer, and reach karamel
       as [TBound]. *)
    let env = if has_flag x.dx_flags Modelled
              then with_typars env x.dx_typars
              else { env with tvars_any = true } in
    (* And a model is only good for the operations karamel really rewrites.
       An unrecognized one reaches Rust as a call to a function nothing ever
       defines, so say so here rather than let rustc find it. *)
    if has_flag x.dx_flags Modelled &&
       not (B.is_known_krml_model_op x.dx_name.ns x.dx_name.id)
    then E.raise_error0 E.Fatal_ExtractionUnsupported [
      text ("Custard: " ^ string_of_name x.dx_name ^ " is in a module karamel \
            models on this backend, but karamel has no translation for it.");
      text "Only the operations karamel recognizes can be used from a modelled \
           module; use the F* definition through --custard_backend KrmlC, or \
           extend the model in karamel."
    ];
    Some (K.DExternal (None, krml_flags x.dx_flags, lid,
                       krml_typ env x.dx_ty, []))

  | DExn e ->
    E.log_issue0 E.Warning_DefinitionNotTranslated [
      text ("Custard: the exception " ^ string_of_name e.de_name ^
            " has no karamel counterpart and was dropped.")
    ];
    None

(* -------------------------------------------------------------------- *)
(* Entry point                                                          *)
(* -------------------------------------------------------------------- *)

let ctor_table (p:program) : ML (SMap.t int) =
  let t = SMap.create 100 in
  p |> List.iter (fun d ->
    match d with
    | DType { dt_body = TVariant cs } ->
      cs |> List.iter (fun (cn, fs) -> SMap.add t (mangled_name cn) (List.length fs))
    | _ -> ());
  t

let extern_type_table (p:program) : ML (SMap.t string) =
  let t = SMap.create 20 in
  p |> List.iter (fun d ->
    match d with
    | DType ty ->
      ty.dt_flags |> List.iter (fun f ->
        match f with
        | Extern (Some target, _) -> SMap.add t (string_of_name ty.dt_name) target
        | _ -> ())
    | _ -> ());
  t

let print_program (p:program) : ML (list Krml.file) =
  extern_types := extern_type_table p;
  let env = { names = []; names_t = []; ctor_arity = ctor_table p; tvars_any = false } in
  let ds = p |> List.collect (fun d ->
             match krml_decl env d with
             | Some d -> [d]
             | None -> []) in
  (* Custard is whole-program, so there is exactly one karamel "file"; karamel
     is free to split the C output as it likes. *)
  [("Custard", ds)]

let write_program (fn:string) (p:program) : ML unit =
  let bin : Krml.binary_format =
    (Krml.current_version, print_program p) in
  BU.save_value_to_file fn bin
