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
module FStarC.Custard.Builtins

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Const
open FStarC.Syntax.Syntax
open FStarC.Custard.Syntax

module Ident = FStarC.Ident
module SMap  = FStarC.SMap
module S     = FStarC.Syntax.Syntax
module SS    = FStarC.Syntax.Subst
module U     = FStarC.Syntax.Util
module PC    = FStarC.Parser.Const
module Options = FStarC.Options
module String = FStarC.String

(* -------------------------------------------------------------------- *)
(* The registry                                                         *)
(* -------------------------------------------------------------------- *)

let table : SMap.t rule = SMap.create 100

let register_rule (l:Ident.lident) (r:rule) : ML unit =
  SMap.add table (Ident.string_of_lid l) r

(* -------------------------------------------------------------------- *)
(* Machine integers                                                     *)
(* -------------------------------------------------------------------- *)

(* The names, and the mapping from name to operator, deliberately follow
   [FStarC.Extraction.Krml.mk_width] and [mk_op]: karamel is the backend that
   has to give these a C meaning, and a discrepancy would show up as a
   miscompilation rather than as an error. *)
let machine_int_of_module (ns : list string) : option (signedness & width) =
  match ns with
  | ["FStar"; m] ->
    (match m with
     | "UInt8"  -> Some (Unsigned, Int8)
     | "UInt16" -> Some (Unsigned, Int16)
     | "UInt32" -> Some (Unsigned, Int32)
     | "UInt64" -> Some (Unsigned, Int64)
     | "Int8"   -> Some (Signed, Int8)
     | "Int16"  -> Some (Signed, Int16)
     | "Int32"  -> Some (Signed, Int32)
     | "Int64"  -> Some (Signed, Int64)
     (* [FStar.SizeT.t] is *defined* as [UInt64.t], so without this rule
        Custard would see through it and emit a 64-bit integer even where the
        C backend must emit [size_t]. *)
     | "SizeT"  -> Some (Unsigned, Sizet)
     | _ -> None)
  | _ -> None

(* The same mapping, keyed on the lowercase spelling that [FStar.Int.Cast]'s
   conversion names use ([uint32_to_uint8]). *)
let machine_int_of_name (s:string) : option (signedness & width) =
  match s with
  | "uint8"  -> Some (Unsigned, Int8)
  | "uint16" -> Some (Unsigned, Int16)
  | "uint32" -> Some (Unsigned, Int32)
  | "uint64" -> Some (Unsigned, Int64)
  | "int8"   -> Some (Signed, Int8)
  | "int16"  -> Some (Signed, Int16)
  | "int32"  -> Some (Signed, Int32)
  | "int64"  -> Some (Signed, Int64)
  | _ -> None

(* [Some (op, arity)].  Note [add] and [add_mod] differ: the former is only
   defined when the result fits, so a backend may compile it to an operation
   that is undefined on overflow, whereas the latter must wrap. *)
let int_op (id:string) : option (op & int) =
  match id with
  | "add" | "add_underspec" -> Some (Add, 2)
  | "add_mod"               -> Some (AddW, 2)
  | "sub" | "sub_underspec" -> Some (Sub, 2)
  | "sub_mod"               -> Some (SubW, 2)
  | "mul" | "mul_underspec" -> Some (Mult, 2)
  | "mul_mod"               -> Some (MultW, 2)
  | "div"                   -> Some (Div, 2)
  | "rem"                   -> Some (Mod, 2)
  | "logor"                 -> Some (BOr, 2)
  | "logxor"                -> Some (BXor, 2)
  | "logand"                -> Some (BAnd, 2)
  | "lognot"                -> Some (BNot, 1)
  | "shift_right"           -> Some (BShiftR, 2)
  | "shift_left"            -> Some (BShiftL, 2)
  | "eq"                    -> Some (Eq, 2)
  | "ne"                    -> Some (Neq, 2)
  | "gt"                    -> Some (Gt, 2)
  | "gte"                   -> Some (Gte, 2)
  | "lt"                    -> Some (Lt, 2)
  | "lte"                   -> Some (Lte, 2)
  | _                       -> None

(* Uniq 0 is the unspecialized declaration, which is what a primitive type
   always is; the backends recognize [Prims.bool] by name. *)
let bool_name : name = { ns = ["Prims"]; id = "bool"; spec = None }

let int_lit (sw : signedness & width) (s:string) : expr =
  mk (EConst (CInt (s, Some sw))) (TInt sw) E_Pure

let machine_int_rule (sw : signedness & width) (id:string) : ML (option rule) =
  match int_op id with
  | Some (o, arity) ->
    let po = { po_op = o; po_int = Some sw } in
    (* A comparison returns a bool, everything else stays at the width. *)
    let ret = match o with
              | Eq | Neq | Lt | Lte | Gt | Gte -> TApp (bool_name, [])
              | _ -> TInt sw in
    Some (Rule_prim (arity, fun _ args -> mk (EOp (po, args)) ret E_Pure))
  | None ->
    match id with
    | "t" -> Some (Rule_type (fun _ -> TInt sw))

    | "zero" -> Some (Rule_prim (0, fun _ _ -> int_lit sw "0"))
    | "one"  -> Some (Rule_prim (0, fun _ _ -> int_lit sw "1"))

    (* [3ul] elaborates to [FStar.UInt32.__uint_to_t 3]; recognising the
       literal here is what keeps a machine constant a constant. *)
    | "uint_to_t" | "int_to_t" | "__uint_to_t" | "__int_to_t" ->
      Some (Rule_prim (1, fun _ args ->
        match args with
        | [{ e = EConst (CInt (s, _)) }] -> int_lit sw s
        | [a] -> mk (ECast (a, TInt sw)) (TInt sw) a.eff
        | _ -> failwith "Custard: machine integer literal rule applied to the wrong arity"))

    (* Realized outside F*: the F* "definitions" of these are [admit ()]. *)
    | "v" | "to_string" | "to_string_hex" | "to_string_hex_pad" | "of_string" ->
      Some (Rule_extern { x_name = None; x_header = None })

    (* [FStar.SizeT]'s conversions.  They are ordinary width changes, and
       saying so keeps them out of the emitted program: the alternative is a
       call into a support library that C does not have. *)
    | "uint16_to_sizet" | "uint32_to_sizet" | "uint64_to_sizet"
    | "of_u32" | "of_u64" when snd sw = Sizet ->
      Some (Rule_prim (1, fun _ args ->
        match args with
        | [a] -> mk (ECast (a, TInt sw)) (TInt sw) a.eff
        | _ -> failwith "Custard: SizeT conversion applied to the wrong arity"))

    | "sizet_to_uint32" | "sizet_to_uint64" when snd sw = Sizet ->
      let target = if id = "sizet_to_uint32" then (Unsigned, Int32)
                                             else (Unsigned, Int64) in
      Some (Rule_prim (1, fun _ args ->
        match args with
        | [a] -> mk (ECast (a, TInt target)) (TInt target) a.eff
        | _ -> failwith "Custard: SizeT conversion applied to the wrong arity"))

    | _ -> None

(* -------------------------------------------------------------------- *)
(* FStar.Int.Cast                                                       *)
(* -------------------------------------------------------------------- *)

(* A width conversion is a coercion: [uint32_to_uint8] is specified as
   [v x % pow2 8] and [int32_to_int8] as [v x @% pow2 8], which is exactly
   what a C cast does.  Compiling the F* definitions instead would be correct
   but drags in [Prims.pow2] -- a recursive function over unbounded integers --
   and karamel has no rule for [FStar.Int.Cast] either: krmllib ships a header
   full of [extern] declarations and no implementation, precisely because the
   real pipeline reduces these to casts before they reach C.

   The masking that a narrowing conversion needs is therefore the backend's
   job.  C gets it for free; the OCaml backend, where every width is a
   different type, prints the coercion as the corresponding [FStar_Int_Cast]
   function (see [PrintOCaml]). *)
let int_cast_rule (id:string) : ML (option rule) =
  match String.split ['_'] id with
  | [src; "to"; dst] ->
    (match machine_int_of_name src, machine_int_of_name dst with
     | Some _, Some sw ->
       Some (Rule_prim (1, fun _ args ->
         match args with
         | [a] -> mk (ECast (a, TInt sw)) (TInt sw) a.eff
         | _ -> failwith "Custard: integer conversion applied to the wrong arity"))
     | _ -> None)
  | _ -> None

(* -------------------------------------------------------------------- *)
(* Prims                                                                *)
(* -------------------------------------------------------------------- *)

(* The boolean connectives.  Without these they would be emitted as calls to
   [Prims_op_Amp_Amp], which has no realization in C.  The comparison and
   arithmetic operators of [Prims] are deliberately *not* here: they act on
   unbounded integers, which no C backend can represent, so leaving them as
   ordinary calls keeps the failure at link time and legible. *)
(* [FStar.Pervasives.false_elim] is [Prims.magic] and [Prims.admit] in a third
   spelling: it typechecks only because the caller has [False] in scope, there
   is no value of the result type to produce, and its own definition is
   [let rec false_elim #_ _ = false_elim ()] -- a non-terminating loop standing
   in for a value that cannot exist.

   Extracting that definition literally is what #4494 is about at the other
   end of the pipeline.  Custard is not vulnerable the way the legacy backend
   is -- an unfolding that does not terminate hits --custard_norm_budget and
   becomes error 365 -- but it did emit the loop, which is worse than useless
   in two different ways.  On OCaml the residue is an infinite loop where a
   [failwith] belongs, so a program that reaches provably-unreachable code
   hangs instead of saying so.  On C it is not emitted at all: the result type
   is a type variable, so it is a hard 368, and with type monomorphization on
   it becomes a 368 about [Prims.int] instead -- an unrepresentable *return*
   type for a function that never returns.

   [EAbort] at [TAny] is what [magic] and [admit] already get, and it is right
   here for the same reason: [TAny] stands where a value of any type is
   wanted, so the C backend stops caring what the result type was. *)
let pervasives_rule (id:string) : ML (option rule) =
  match id with
  | "false_elim" ->
    Some (Rule_prim (1, fun _ _ ->
            mk (EAbort "FStar.Pervasives.false_elim") TAny E_Impure))
  | _ -> None

let prims_rule (id:string) : ML (option rule) =
  let bool_op (o:op) (arity:int) : ML (option rule) =
    let po = { po_op = o; po_int = None } in
    Some (Rule_prim (arity, fun _ args ->
            mk (EOp (po, args)) (TApp (bool_name, [])) E_Pure)) in
  match id with
  | "op_Amp_Amp" -> bool_op And 2
  | "op_Bar_Bar" -> bool_op Or 2
  | "not"        -> bool_op Not 1
  (* Decidable equality is an operator, not a call: leaving it as an external
     gives C a [void *] signature that no eqtype fits.  The type argument is
     deliberately ignored, exactly as [FStarC.Extraction.Krml.mk_bool_op] does
     -- the operands' own types say what is being compared. *)
  | "op_Equals"       -> bool_op Eq 2
  | "op_Less_Greater" -> bool_op Neq 2
  (* [Prims.exn] is the one extensible variant: it has no constructors of its
     own, so there is no layout to derive and nothing to instantiate.  Only
     OCaml has a representation for it (section 8.5). *)
  | "exn" -> Some (Rule_type (fun _ -> TExn))
  (* [magic] and [admit] only typecheck because the caller has proved the
     point unreachable -- either outright, or, as in
     [FStar.Stubs.Tactics.V2.Builtins.raise], through a [False]
     postcondition.  There is no value of the result type to produce and no
     reason to produce one, so this aborts like [Pulse.Lib.Dv.unreachable].
     [TAny] is what lets it stand where a value of any type is wanted. *)
  | "magic" | "admit" ->
    Some (Rule_prim (1, fun _ _ -> mk (EAbort ("Prims." ^ id)) TAny E_Impure))
  | _ -> None

(* -------------------------------------------------------------------- *)
(* Pulse                                                                *)
(* -------------------------------------------------------------------- *)

(* Section 8.4.  Pulse's references, boxes, vectors, arrays and array pointers
   are all one thing at runtime -- a pointer into a mutable run of values --
   and its [while] is a statement.  Compiling their F* definitions is not an
   option: they are specified against Pulse's separation-logic model, which
   has no runtime meaning at all.

   These rules deliberately mirror [ExtractPulse.pulse_translate_expr], the
   corresponding table of the ML-to-karamel pipeline, so that a Pulse program
   means the same thing through either.  The argument counts differ, though:
   the ML pipeline sees the source arity, whereas by the time a rule runs here
   the erased arguments (the permissions, the ghost sequences, the [small_type]
   dictionaries) are already gone.  *)

let size_lit (n:string) : expr =
  mk (EConst (CInt (n, Some (Unsigned, Sizet)))) (TInt (Unsigned, Sizet)) E_Pure

let elt_of (tys : list cty) : cty =
  match tys with
  | t :: _ -> t
  | [] -> TAny

(* [buf_prim n mk_ty o mk_args e]: a rule taking [n] value arguments, of result
   type [mk_ty], building [EOp (o, mk_args ...)] with effect [e]. *)
let buf_prim (n:int) (o:op) (ef:eff)
             (ret : list cty -> list expr -> ML cty)
             (mk_args : list expr -> ML (list expr)) : rule =
  Rule_prim (n, fun tys args ->
    mk (EOp ({ po_op = o; po_int = None }, mk_args args)) (ret tys args) ef)

let unit_rule (n:int) : rule =
  Rule_prim (n, fun _ _ -> unit_expr)

(* [Reference.free] is a no-op: the allocation it matches was a [BufCreate
   LStack], which the C backend scopes to the enclosing block. *)
let identity_rule (n:int) : rule =
  Rule_prim (n, fun _ args ->
    match args with
    | a :: _ -> a
    | [] -> unit_expr)

let pulse_rule (ns : list string) (id : string) : ML (option rule) =
  let buf tys (_ : list expr) : ML cty = TBuf (elt_of tys) in
  let rf tys (_ : list expr) : ML cty = TRef (elt_of tys) in
  let unit_ty (_ : list cty) (_ : list expr) : ML cty = TUnit in
  let bool_ty (_ : list cty) (_ : list expr) : ML cty = TApp (bool_name, []) in
  (* The element type of a buffer we are given rather than creating: the
     first argument's own type already says it. *)
  let elt_of_arg (_ : list cty) (args : list expr) : ML cty =
    match args with
    | { ty = TBuf t } :: _ -> t
    | { ty = TRef t } :: _ -> t
    | _ -> TAny in
  (* [to_array_mask] and [array_at] view a reference as a one-element run.
     The two are the same pointer in C, but not the same OCaml value, so the
     node has to say which one it is. *)
  let as_buf (_ : list cty) (args : list expr) : ML cty =
    match args with
    | { ty = TRef t } :: _ -> TBuf t
    | a :: _ -> a.ty
    | _ -> TAny in
  let self (_ : list cty) (args : list expr) : ML cty =
    match args with
    | a :: _ -> a.ty
    | _ -> TAny in
  match ns, id with
  (* Types.  Every one of them is a pointer. *)
  | ["Pulse"; "Lib"; "Vec"], "vec"
  | ["Pulse"; "Lib"; "Array"; "Core"], "array"
  | ["Pulse"; "Lib"; "ArrayPtr"], "ptr" ->
    Some (Rule_type (fun tys -> TBuf (elt_of tys)))

  (* A reference points at one value, not at a run.  C makes no distinction,
     but OCaml does: this is what gets [t ref] rather than a one-element
     array (section 8.4). *)
  | ["Pulse"; "Lib"; "Reference"], "ref"
  | ["Pulse"; "Lib"; "Box"], "box" ->
    Some (Rule_type (fun tys -> TRef (elt_of tys)))

  (* A reference is a one-element stack allocation. *)
  | ["Pulse"; "Lib"; "Reference"], "alloc" ->
    Some (buf_prim 1 (BufCreate LStack) E_Impure rf
            (fun args -> args @ [size_lit "1"]))
  | ["Pulse"; "Lib"; "Reference"], "alloc_uninit" ->
    Some (Rule_prim (1, fun tys _ ->
      let t = elt_of tys in
      mk (EOp ({ po_op = BufCreate LStack; po_int = None },
               [mk EAny t E_Pure; size_lit "1"]))
         (TRef t) E_Impure))
  | ["Pulse"; "Lib"; "Reference"], "free" -> Some (unit_rule 1)
  | ["Pulse"; "Lib"; "Reference"], "read"
  | ["Pulse"; "Lib"; "Reference"], "op_Bang" ->
    Some (buf_prim 1 BufRead E_Impure elt_of_arg
            (fun args -> args @ [size_lit "0"]))
  | ["Pulse"; "Lib"; "Reference"], "write"
  | ["Pulse"; "Lib"; "Reference"], "op_Colon_Equals" ->
    Some (buf_prim 2 BufWrite E_Impure unit_ty
            (fun args -> match args with
                         | [r; v] -> [r; size_lit "0"; v]
                         | args -> args))
  | ["Pulse"; "Lib"; "Reference"], "to_array_mask" ->
    Some (buf_prim 1 BufSub E_Pure as_buf (fun args -> args @ [size_lit "0"]))
  | ["Pulse"; "Lib"; "Reference"], "array_at"
  | ["Pulse"; "Lib"; "Reference"], "array_at_uninit" ->
    Some (buf_prim 2 BufSub E_Pure as_buf (fun args -> args))

  (* A box is a one-element heap allocation. *)
  | ["Pulse"; "Lib"; "Box"], "alloc" ->
    Some (buf_prim 1 (BufCreate LHeap) E_Impure rf
            (fun args -> args @ [size_lit "1"]))
  | ["Pulse"; "Lib"; "Box"], "free" ->
    Some (buf_prim 1 BufFree E_Impure unit_ty (fun args -> args))
  | ["Pulse"; "Lib"; "Box"], "op_Bang" ->
    Some (buf_prim 1 BufRead E_Impure elt_of_arg
            (fun args -> args @ [size_lit "0"]))
  | ["Pulse"; "Lib"; "Box"], "op_Colon_Equals" ->
    Some (buf_prim 2 BufWrite E_Impure unit_ty
            (fun args -> match args with
                         | [r; v] -> [r; size_lit "0"; v]
                         | args -> args))
  | ["Pulse"; "Lib"; "Box"], "box_to_ref" -> Some (identity_rule 1)

  (* A vector is a heap-allocated run. *)
  | ["Pulse"; "Lib"; "Vec"], "alloc" ->
    Some (buf_prim 2 (BufCreate LHeap) E_Impure buf (fun args -> args))
  | ["Pulse"; "Lib"; "Vec"], "free" ->
    Some (buf_prim 1 BufFree E_Impure unit_ty (fun args -> args))
  | ["Pulse"; "Lib"; "Vec"], "op_Dot_Lparen_Rparen" ->
    Some (buf_prim 2 BufRead E_Impure elt_of_arg (fun args -> args))
  | ["Pulse"; "Lib"; "Vec"], "op_Dot_Lparen_Rparen_Less_Minus" ->
    Some (buf_prim 3 BufWrite E_Impure unit_ty (fun args -> args))
  | ["Pulse"; "Lib"; "Vec"], "vec_to_array" -> Some (identity_rule 1)

  (* An array is a stack-allocated run. *)
  | ["Pulse"; "Lib"; "Array"; "PtsTo"], "alloc" ->
    Some (buf_prim 2 (BufCreate LStack) E_Impure buf (fun args -> args))
  | ["Pulse"; "Lib"; "Array"; "Core"], "mask_alloc"
  | ["Pulse"; "Lib"; "Array"; "Core"], "mask_alloc_with_vis" ->
    Some (Rule_prim (1, fun tys args ->
      let t = elt_of tys in
      let n = match args with a :: _ -> a | [] -> size_lit "0" in
      mk (EOp ({ po_op = BufCreate LStack; po_int = None }, [mk EAny t E_Pure; n]))
         (TBuf t) E_Impure))
  | ["Pulse"; "Lib"; "Array"; "Core"], "mask_free" -> Some (unit_rule 1)
  | ["Pulse"; "Lib"; "Array"; "Core"], "mask_read" ->
    Some (buf_prim 2 BufRead E_Impure elt_of_arg (fun args -> args))
  | ["Pulse"; "Lib"; "Array"; "Core"], "mask_write" ->
    Some (buf_prim 3 BufWrite E_Impure unit_ty (fun args -> args))
  | ["Pulse"; "Lib"; "Array"; "Core"], "sub" ->
    Some (buf_prim 2 BufSub E_Pure self (fun args -> args))

  (* An array pointer is a raw pointer. *)
  | ["Pulse"; "Lib"; "ArrayPtr"], "op_Dot_Lparen_Rparen" ->
    Some (buf_prim 2 BufRead E_Impure elt_of_arg (fun args -> args))
  | ["Pulse"; "Lib"; "ArrayPtr"], "op_Dot_Lparen_Rparen_Less_Minus" ->
    Some (buf_prim 3 BufWrite E_Impure unit_ty (fun args -> args))
  | ["Pulse"; "Lib"; "ArrayPtr"], "split" ->
    Some (buf_prim 2 BufSub E_Pure self (fun args -> args))
  | ["Pulse"; "Lib"; "ArrayPtr"], "as_ref"
  | ["Pulse"; "Lib"; "ArrayPtr"], "from_ref"
  | ["Pulse"; "Lib"; "ArrayPtr"], "from_array" ->
    Some (identity_rule 1)
  | ["Pulse"; "Lib"; "ArrayPtr"], "memcpy" ->
    Some (buf_prim 5 BufBlit E_Impure unit_ty (fun args -> args))

  (* Null pointers, shared by all of them. *)
  | ["Pulse"; "Lib"; "Reference"], "null"
  | ["Pulse"; "Lib"; "Box"], "null" ->
    Some (Rule_prim (0, fun tys _ ->
      mk (EOp ({ po_op = BufNull; po_int = None }, [])) (TRef (elt_of tys)) E_Pure))
  | ["Pulse"; "Lib"; "Array"; "Core"], "null"
  | ["Pulse"; "Lib"; "ArrayPtr"], "null" ->
    Some (Rule_prim (0, fun tys _ ->
      mk (EOp ({ po_op = BufNull; po_int = None }, [])) (TBuf (elt_of tys)) E_Pure))
  | ["Pulse"; "Lib"; "Reference"], "is_null"
  | ["Pulse"; "Lib"; "Box"], "is_null"
  | ["Pulse"; "Lib"; "Array"; "Core"], "is_null"
  | ["Pulse"; "Lib"; "ArrayPtr"], "is_null" ->
    Some (buf_prim 1 BufIsNull E_Pure bool_ty (fun args -> args))

  (* [while_] is emitted by Pulse's own elaboration with both halves already
     thunked; a [while] statement is exactly the two thunk bodies. *)
  | ["Pulse"; "Lib"; "Dv"], "while_" ->
    Some (Rule_prim (2, fun _ args ->
      match args with
      | [{ e = EFun (_, cond) }; { e = EFun (_, body) }] ->
        mk (EWhile (cond, body)) TUnit E_Impure
      | _ ->
        (* Pulse's elaboration always thunks both halves, so this cannot
           happen; failing loudly beats emitting a loop that does not loop. *)
        failwith "Custard: Pulse.Lib.Dv.while_ applied to something other than two thunks"))

  (* Pulse proved this branch dead; its argument is the proof. *)
  | ["Pulse"; "Lib"; "Dv"], "unreachable" ->
    Some (Rule_prim (1, fun _ _ ->
      mk (EAbort "Pulse.Lib.Dv.unreachable") TAny E_Impure))

  (* [mk_gvar]/[read_gvar] are the two halves of a global initializer.  A
     [gvar p] *is* the value it guards -- the slprop is ghost -- so the type is
     its own first type argument, making the variable a plain global; [mk_gvar
     init] is the initializer run, and [read_gvar x] is [x].  These mirror the
     three rules Pulse's karamel extension registers (ExtractPulse.fst). *)
  | ["Pulse"; "Lib"; "GlobalVar"], "gvar" ->
    Some (Rule_type (fun tys -> elt_of tys))
  | ["Pulse"; "Lib"; "GlobalVar"], "mk_gvar" ->
    Some (Rule_prim (1, fun tys args ->
      match args with
      | init :: _ ->
        let ret = match init.ty with
                  | TArrow (_, _, r) -> r
                  | _ -> elt_of tys in
        mk (EApp (init, [unit_expr])) ret E_Impure
      | [] -> unit_expr))
  | ["Pulse"; "Lib"; "GlobalVar"], "read_gvar" -> Some (identity_rule 1)

  | _ -> None

(* -------------------------------------------------------------------- *)
(* Garbage-collected references                                         *)
(* -------------------------------------------------------------------- *)

(* [FStar.All] is the ulib reference API and [FStarC.Effect] the compiler's
   own; they are the same API under two names, and neither has a [free],
   because both are realized by OCaml's [ref].  So a reference here is a
   [TRef] holding a *heap* cell: the OCaml backend prints [TRef] as [t ref]
   and [BufCreate] into one as [ref x] (PrintOCaml.fst:359), which is exactly
   right, while the C backend would emit a [malloc] that nothing frees --
   correct, but a leak, and section 8.4 says so.

   [read]/[write] index at 0 for the same reason [Pulse.Lib.Reference] does:
   the IR has one memory-access node, and a reference is the one-element case
   of it. *)
(* Section 8.5.  [raise] is a control-flow node rather than a call, because a
   backend has to know that nothing after it runs.  [try_with] arrives as two
   functions -- F* has no [try] syntax, so the source always spells it
   [try_with (fun () -> e) (fun e -> h)] -- and becomes an [ETry] with a
   single catch-all branch, which is what the two arguments say: an F*
   handler takes the exception value and does its own matching. *)
let exn_var : string = "_cexn"

let exn_rule (id:string) : ML (option rule) =
  (* Pulse's [while_] does the same: a thunk that is syntactically a lambda is
     the body it wraps, and calling it would only make the backend undo that.
     The binder cannot simply be dropped: [fun () -> e] elaborates to a lambda
     whose body matches its binder against [()], so the body may well mention
     it.  Binding it to [()] is what a call would have done, and the
     simplifier deletes the binding when it turns out to be unused. *)
  let force (f:expr) : ML expr =
    match f.e with
    | EFun ([b], body) -> mk (ELet (b.b_name, TUnit, unit_expr, body)) body.ty body.eff
    | _ -> mk (EApp (f, [unit_expr])) TAny E_Impure in
  match id with
  | "raise" ->
    Some (Rule_prim (1, fun _ args ->
      match args with
      | [e] -> mk (ERaise e) TAny E_Impure
      | _ -> failwith "Custard: raise applied to the wrong number of arguments"))
  | "try_with" ->
    Some (Rule_prim (2, fun _ args ->
      match args with
      | [f; h] ->
        let body = force f in
        let x = mk (EVar exn_var) TExn E_Pure in
        mk (ETry (body, [(PVar exn_var, None,
                          mk (EApp (h, [x])) body.ty E_Impure)]))
           body.ty E_Impure
      | _ -> failwith "Custard: try_with applied to the wrong number of arguments"))
  (* [failwith] and [exit] are the support module's own: [exit] in particular
     takes an F* [int], which is a [Z.t], and it is the realization that
     narrows it.  Naming no target lets each of [FStar.All], [FStarC.Effect]
     and [FStar.Exn] resolve to its own file. *)
  | "failwith" -> Some (Rule_extern { x_name = None; x_header = None })
  | "exit" -> Some (Rule_extern { x_name = None; x_header = None })
  | _ -> None

let ref_rule (id:string) : ML (option rule) =
  let rf tys (_ : list expr) : ML cty = TRef (elt_of tys) in
  let unit_ty (_ : list cty) (_ : list expr) : ML cty = TUnit in
  let elt_of_arg (_ : list cty) (args : list expr) : ML cty =
    match args with
    | { ty = TRef t } :: _ -> t
    | { ty = TBuf t } :: _ -> t
    | _ -> TAny in
  match id with
  | "ref" -> Some (Rule_type (fun tys -> TRef (elt_of tys)))
  | "alloc" | "mk_ref" ->
    Some (buf_prim 1 (BufCreate LHeap) E_Impure rf
            (fun args -> args @ [size_lit "1"]))
  | "read" | "op_Bang" ->
    Some (buf_prim 1 BufRead E_Impure elt_of_arg
            (fun args -> args @ [size_lit "0"]))
  | "write" | "op_Colon_Equals" ->
    Some (buf_prim 2 BufWrite E_Impure unit_ty
            (fun args -> match args with
                         | [r; v] -> [r; size_lit "0"; v]
                         | args -> args))
  | _ -> None

(* -------------------------------------------------------------------- *)
(* Attribute-declared rules                                             *)
(* -------------------------------------------------------------------- *)

(* [@@custard_extern "target"], [@@custard_c_header "h.h"] and
   [@@custard_opaque] let a rule be declared in F* source, which covers the
   common cases (an [assume val] realized by hand) without an OCaml plugin. *)
let string_arg (t:S.term) : ML (option string) =
  match (SS.compress t).n with
  | Tm_constant (Const_string (s, _)) -> Some s
  | _ -> None

let attribute_string (attrs : list S.term) (a : Ident.lident) : ML (option string) =
  match U.get_attribute a attrs with
  | Some ((arg, _) :: _) -> string_arg arg
  | _ -> None

let rule_of_attributes (attrs : list S.term) : ML (option rule) =
  if U.has_attribute attrs PC.custard_opaque_attr
  then Some Rule_opaque
  (* [has_attribute] only matches a bare fvar, and these carry an argument. *)
  else if Some? (U.get_attribute PC.custard_extern_attr attrs)
  then
    let name = match attribute_string attrs PC.custard_extern_attr with
               | Some "" -> None
               | r -> r in
    Some (Rule_extern { x_name   = name;
                        x_header = attribute_string attrs PC.custard_c_header_attr })
  else None

(* -------------------------------------------------------------------- *)
(* Lookup                                                               *)
(* -------------------------------------------------------------------- *)

(* The modules whose OCaml realization is written by hand rather than
   extracted: every one of these has a file of the same name under [src/ml] or
   [ulib/ml/plugin], and the build excludes it from extraction.  Custard
   links against the same realizations, so a type declared in one of them
   belongs to that file and must not be compiled again -- see {!Rule_realized}.

   The list is the convention, not an attribute on each module: marking fifty
   interfaces one at a time would be a rule about the build expressed in the
   library, and it would still have to be kept in step with the build.  It is
   the set of module names for which [src/ml] or [ulib/ml/plugin] holds a
   file of the same name, plus [FStar.Pervasives], which is extracted rather
   than hand-written but whose [either] and [dtuple] types the realizations
   use in their own signatures.  Listing a module that declares no type is harmless:
   the rule has no effect on values. *)
(* Section 8.3.  ulib declares the compiler's reflection and tactic API a
   second time, as the [FStar.Stubs.*] modules: abstract types and [assume
   val]s, standing for definitions the compiler already has.  They are not a
   separate implementation of anything, and a metaprogram that used them under
   their own names would not link against the engine that runs it -- so the
   namespace is rewritten to the one it is a stub for, and the two views become
   one set of names.  This is the same rewrite the ML pipeline does in
   [UEnv.no_fstar_stubs_ns], where it is conditional on [--codegen Plugin];
   Custard does it unconditionally, because a whole-program compilation of the
   compiler never mentions these modules at all -- the compiler uses the
   [FStarC.*] originals -- so there is no second case to be in.

   [FStar.NormSteps] is the same arrangement without the [Stubs] segment. *)
let no_fstar_stubs (ns : list string) : list string =
  match ns with
  | "FStar" :: "NormSteps" :: rest -> "FStarC" :: "NormSteps" :: rest
  | "FStar" :: "Stubs" :: rest -> "FStarC" :: rest
  | _ -> ns

(* The rewrite says where a stub's definitions *live*; this recognises that
   they are stubs at all.  A stub is a second declaration of something the
   compiler already defines -- [FStar.Stubs.Syntax.Syntax.subst_elt] is the
   compiler's [FStarC.Syntax.Syntax.subst_elt], written out again so that a
   metaprogram can name it -- and compiling the stub's copy would put a second
   definition of that type in the module that already has the first.

   The consequences are drawn in [Extract.unstub_lid], which is where a
   request for a stub is answered with the compiler's own declaration.  The
   argument is the namespace *before* {!no_fstar_stubs}, since afterwards
   there is nothing left to recognise. *)
let is_stub_module (ns : list string) : bool =
  match ns with
  | "FStar" :: "Stubs" :: _ -> true
  | _ -> false

(* A handful of stubs do not live where {!no_fstar_stubs} says they do.  An
   exception is the clearest case: [FStar.Stubs.Tactics.Common.Stop] is how a
   metaprogram names the exception the tactic engine raises to abort, and the
   engine's own name for it is [FStarC.Errors.Stop] -- a different module, not
   just a different namespace.  Exception identity in OCaml is by declaration,
   so getting this wrong is not a naming inconvenience: the plugin declares a
   second [Stop], raises that one, and the compiler's handler does not catch
   it.  The failure is a Pulse tactic reporting
   [Custard_FStarC_Tactics_Common.FStarC_Tactics_Common_Stop] as an error
   message.  [UEnv.new_mlpath_of_lident] carries the same entry. *)
let stub_aliases : list (string & string) = [
  "FStar.Stubs.Tactics.Common.Stop", "FStarC.Errors.Stop";
]

(* [FStar.Bytes.bytes] is [struct { uint32_t length; const char *data; }] in
   krmllib's [compat.h], which every karamel-generated program includes; the
   direct-to-C backend has to ask for it by name. *)
(* [Lid], [Lid=name], [Lid@header] or [Lid=name@header].  An empty component
   is the same as an absent one, so [Lid=@h] is legal and means "keep the
   mangled name, include [h]". *)
let parse_extern_type (spec:string) : ML (option (string & extern)) =
  let opt (s:string) : option string = if s = "" then None else Some s in
  let lid, rest =
    match String.split ['@'] spec with
    | [a] -> a, None
    | [a; h] -> a, opt h
    | _ -> spec, None in
  let lid, nm =
    match String.split ['='] lid with
    | [a] -> a, None
    | [a; n] -> a, opt n
    | _ -> lid, None in
  if lid = "" then None
  else Some (lid, { x_name = nm; x_header = rest })

(* Deliberately empty.  A type with no F* definition and a representation
   fixed by the target is a fact about the *program being built*, not about
   F*: [FStar.Bytes.bytes] is a struct of a particular shape only because
   some C library says so, and hardcoding one library's answer here would
   make every other program wrong.  Hence [--custard_extern_type], and hence
   nothing built in. *)
let extern_types : list (string & extern) = []

let extern_type_of_lid (l:Ident.lident) : ML (option extern) =
  let s = Ident.string_of_lid l in
  let from_cmdline =
    Options.custard_extern_types () |> List.collect (fun spec ->
      match parse_extern_type spec with
      | Some (k, x) when k = s -> [x]
      | _ -> []) in
  match from_cmdline with
  | x :: _ -> Some x
  | [] -> extern_types |> List.tryPick (fun (k, x) -> if k = s then Some x else None)

let realized_modules : list (list string) = [
  ["FStar"; "All"];
  ["FStar"; "Bytes"];
  ["FStar"; "Char"];
  ["FStar"; "Dyn"];
  ["FStar"; "Exception"];
  ["FStar"; "Exn"];
  ["FStar"; "IO"];
  ["FStar"; "ImmutableArray"];
  ["FStar"; "ImmutableArray"; "Base"];
  ["FStar"; "Issue"];
  ["FStar"; "List"];
  ["FStar"; "List"; "Tot"; "Base"];
  ["FStar"; "Option"];
  ["FStar"; "Parse"];
  ["FStar"; "Pervasives"];
  ["FStar"; "Pervasives"; "Native"];
  ["FStar"; "Pprint"];
  ["FStar"; "Sealed"];
  ["FStar"; "String"];
  ["FStar"; "UInt8"];
  ["FStarC"; "Array"];
  ["FStarC"; "BaseTypes"];
  ["FStarC"; "Effect"];
  ["FStarC"; "Extraction"; "ML"; "PrintML"];
  ["FStarC"; "Filepath"];
  ["FStarC"; "Format"];
  ["FStarC"; "Getopt"];
  ["FStarC"; "Hash"];
  ["FStarC"; "Hints"];
  ["FStarC"; "IMap"];
  ["FStarC"; "Int"; "Extra"];
  ["FStarC"; "Json"];
  ["FStarC"; "List"];
  ["FStarC"; "PIMap"];
  ["FStarC"; "PSMap"];
  ["FStarC"; "Parser"; "ParseIt"];
  ["FStarC"; "Platform"; "Base"];
  ["FStarC"; "Plugins"; "Base"];
  ["FStarC"; "Pprint"];
  ["FStarC"; "Range"];
  (* Reached under their [FStar.Stubs.*] names; see {!no_fstar_stubs}. *)
  ["FStarC"; "Reflection"; "Types"];
  ["FStarC"; "Tactics"; "Unseal"];
  ["FStarC"; "Tactics"; "V2"; "Builtins"];
  ["FStarC"; "SMap"];
  ["FStarC"; "String"];
  ["FStarC"; "StringBuffer"];
  ["FStarC"; "Syntax"; "TermHashTable"];
  ["FStarC"; "Tactics"; "Native"];
  ["FStarC"; "Time"];
  ["FStarC"; "Timing"];
  ["FStarC"; "Unionfind"];
  ["FStarC"; "Util"];
  ["Prims"];
]

(* Section 20.  karamel's Rust backend recognizes [Pulse.Lib.Slice] by name --
   the type as [TApp ((["Pulse"; "Lib"; "Slice"], "slice"), [t])] and each
   operation as an [ETApp] of its own lid -- and turns them into Rust's own
   slices, which are borrowed views rather than owning structs.  Compiling the
   F* definition instead, which is what Custard did and what is right for C,
   gives karamel a struct that owns its buffer, so [split] deep-copies and
   every write lands in a temporary (section 19.15).

   A module karamel models is realized in exactly the sense of section 8.2 --
   the target language defines it, keep the shape and do not emit it -- with
   one difference: the realization is reached under the F* name, so there is
   nothing to rename.  That is why this feeds [is_realized_module] rather than
   being a rule kind of its own.

   Only under [--custard_backend KrmlRust].  On the C path the F* definition
   is the implementation, and modelling it away would leave the program with
   no slice at all.

   Which modules karamel models is a fact about karamel, not about F*, so the
   list is data and [--custard_krml_model] can correct it without a rebuild.
   [Pulse.Lib.Slice] is the one karamel has today. *)
let builtin_krml_models : list (list string) = [
  ["Pulse"; "Lib"; "Slice"];
]

let is_krml_model (ns : list string) : ML bool =
  Options.custard_backend () = "KrmlRust" &&
  (builtin_krml_models |> List.existsb (fun m -> m = ns) ||
   Options.custard_krml_models () |> List.existsb (fun m ->
     m = String.concat "." ns))

(* karamel's Rust backend needs a *tuple*, not a struct that happens to have
   two fields: [Pulse.Lib.Slice.split] becomes [split_at], whose result it
   destructures with [retrieve_pair_type], and which fails outright -- a
   crash, not a diagnostic -- on anything but [MiniRust.Tuple [t; t]].

   So on that path [FStar.Pervasives.Native.tupleN] is modelled too.  Custard's
   IR has had [TTuple], [ETuple] and [PTuple] all along and [PrintKrml] prints
   all three; what it has never had is a reason to produce them, because a
   struct is what C wants and the C backends are all there was.

   Only the tuples, not the whole of [FStar.Pervasives.Native]: [option] is in
   the same module and karamel is happy to compile it. *)
let is_krml_model_name (ns : list string) (id : string) : ML bool =
  is_krml_model ns ||
  (Options.custard_backend () = "KrmlRust" &&
   ns = ["FStar"; "Pervasives"; "Native"] &&
   (FStarC.Util.starts_with id "tuple" ||
    FStarC.Util.starts_with id "Mktuple"))

(* karamel recognizes a handful of F* definitions by name, and it spells those
   names the way F* spelled them before operator mangling was made uniform.
   Custard rewrites them on the way out for the same reason
   [FStarC.Extraction.Krml.krml_compat_name] does, and the two tables must
   agree: karamel lives in another repository and cannot be updated in the
   same commit.  Delete both once it has been taught the current names.

   The Prims operators are never extracted -- karamel supplies them as
   builtins ([Krml.Builtin.prepare]) -- so only references to them are ever
   emitted, but the name a reference carries still has to be the one karamel
   declares.  The [Pulse.Lib.Slice] operators are the ones its Rust backend
   matches on to emit native indexing (section 20). *)
let krml_compat_name (ns : list string) (id : string) : list string & string =
  match ns, id with
  | ["Prims"], "op_Plus"           -> ns, "op_Addition"
  | ["Prims"], "op_Minus"          -> ns, "op_Subtraction"
  | ["Prims"], "op_Tilde_Minus"    -> ns, "op_Minus"
  | ["Prims"], "op_Star"           -> ns, "op_Multiply"
  | ["Prims"], "op_Slash"          -> ns, "op_Division"
  | ["Prims"], "op_Percent"        -> ns, "op_Modulus"
  | ["Prims"], "op_Less"           -> ns, "op_LessThan"
  | ["Prims"], "op_Less_Equals"    -> ns, "op_LessThanOrEqual"
  | ["Prims"], "op_Greater"        -> ns, "op_GreaterThan"
  | ["Prims"], "op_Greater_Equals" -> ns, "op_GreaterThanOrEqual"
  | ["Pulse"; "Lib"; "Slice"], "op_Dot_Lparen_Rparen" ->
    ns, "op_Array_Access"
  | ["Pulse"; "Lib"; "Slice"], "op_Dot_Lparen_Rparen_Less_Minus" ->
    ns, "op_Array_Assignment"
  | _ -> ns, id

(* The operations of [Pulse.Lib.Slice] that karamel's Rust backend rewrites,
   from [AstToMiniRust.translate_expr]'s match on
   [EApp (ETApp (EQualified (["Pulse";"Lib";"Slice"], op), _, _, _), _)].
   Anything else in the module is modelled away with nothing to model it. *)
let builtin_krml_model_ops : list (list string & list string) = [
  ["Pulse"; "Lib"; "Slice"],
  ["from_array"; "op_Array_Access"; "op_Array_Assignment";
   "split"; "subslice"; "copy"; "len"];
]

(* Against the *karamel* spelling, since that is what the table lists and what
   the emitted reference will carry. *)
let is_known_krml_model_op (ns : list string) (id : string) : ML bool =
  match builtin_krml_model_ops |> List.tryFind (fun (m, _) -> m = ns) with
  | None -> true
  | Some (_, ops) ->
    let _, id = krml_compat_name ns id in
    ops |> List.existsb (fun o -> o = id)
let is_realized_module (ns : list string) : ML bool =
  realized_modules |> List.existsb (fun m -> m = ns)
  || is_krml_model ns


(* A realization *replaces* the F* module, values included: where there is a
   hand-written [.ml] the F* definitions are a model, and a model that
   disagrees with the realization is exactly the sort of thing extraction
   must not silently pick between.  [FStar.Dyn] is the case that makes it
   concrete -- [dyn] is [unit -> Dv value_type_bundle] in F* and [Obj.t] in
   [FStar_Dyn.ml], so [undyn]'s body forces a thunk that is not one -- but the
   rule is not about that one module: if a realization does not implement the
   whole interface, that is a bug in the realization, and the OCaml linker
   says so.

   The exceptions are the modules whose realization defines no representation
   of its own, so that there is nothing for it to replace.  [FStar.Pervasives]
   has no hand-written file at all and is listed above only so that the
   [either] and [dtuple] types the realizations name in their signatures are
   pinned.  [FStar.Pervasives.Native] does have one, but it is transparent --
   [type ('a,'b) tuple2 = 'a * 'b], and every value a projection out of it --
   and these are types Custard represents natively, so its [fst] and [snd] are
   ordinary F* code over a representation both sides already agree on.
   Compiling them is also what keeps [tuple2] monomorphizable: an external's
   signature freezes the types in it (section 5.0), and a frozen [tuple2] has
   no C representation at all. *)
let type_only_realized_modules : list (list string) = [
  ["FStar"; "Pervasives"];
  ["FStar"; "Pervasives"; "Native"];
]

let is_type_only_realized_module (ns : list string) : ML bool =
  type_only_realized_modules |> List.existsb (fun m -> m = ns)

(* The hardcoded rules: the registry populated by {!register_rule}, then the
   families matched by the shape of the name. *)
(* Section 3.2c: [FStar.Custard.dyn] is a call-site marker, not a
   computation.  It exists to survive the normalization that computes a
   specialization key -- which is why it is [irreducible] -- and carries no
   run-time meaning of its own, so it compiles to its argument. *)
let custard_rule (id:string) : ML (option rule) =
  match id with
  | "dyn" -> Some (Rule_prim (1, fun _ args ->
                     match args with
                     | [e] -> e
                     | _ -> failwith "FStar.Custard.dyn applied to the wrong number of arguments"))
  | _ -> None

let builtin_rule (l:Ident.lident) : ML rule =
  let r =
    match SMap.try_find table (Ident.string_of_lid l) with
    | Some r -> Some r
    | None ->
      let path = Ident.path_of_lid l in
      match List.rev path with
      | id :: rev_ns ->
        let ns = no_fstar_stubs (List.rev rev_ns) in
        (match machine_int_of_module ns with
         | Some sw -> machine_int_rule sw id
         | None ->
           if ns = ["Prims"] then prims_rule id
           (* [FStar.Pervasives] is also a *realized* module, so this has to
              fall through rather than shadow: [pervasives_rule] claims one
              name, and everything else in the module -- [Mkdtuple3] and
              friends -- still has to reach [is_realized_module] below. *)
           else if ns = ["FStar"; "Pervasives"] && Some? (pervasives_rule id)
           then pervasives_rule id
           else if ns = ["FStar"; "Int"; "Cast"] then int_cast_rule id
           else if ns = ["FStar"; "All"] || ns = ["FStarC"; "Effect"]
           then (match ref_rule id with
                 | Some r -> Some r
                 | None ->
                   (match exn_rule id with
                    | Some r -> Some r
                    | None -> pulse_rule ns id))
           else if ns = ["FStar"; "Custard"] then custard_rule id
           else if ns = ["FStar"; "Exn"] then exn_rule id
           else if is_realized_module ns then Some Rule_realized
           else pulse_rule ns id)
      | [] -> None
  in
  match r with
  | Some r -> r
  | None -> raise No_custard_rule

(* Extensions are chained in the same style as the karamel extension points of
   [FStarC.Extraction.Krml] (see [register_pre_translate_type] there): each
   registered function may decline by raising [No_custard_rule], in which case
   the rest of the chain is tried. *)
let ref_lookup_rule : ref rule_lookup_t = mk_ref builtin_rule

let register_pre_rule (f : rule_lookup_t) : ML unit =
  let before : rule_lookup_t = !ref_lookup_rule in
  ref_lookup_rule := (fun l -> try f l with No_custard_rule -> before l)

let register_post_rule (f : rule_lookup_t) : ML unit =
  let before : rule_lookup_t = !ref_lookup_rule in
  ref_lookup_rule := (fun l -> try before l with No_custard_rule -> f l)

let lookup_rule (l:Ident.lident) : ML (option rule) =
  try Some (!ref_lookup_rule l) with No_custard_rule -> None
