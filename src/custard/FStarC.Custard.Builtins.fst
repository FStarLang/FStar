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
open FStarC.Custard.Syntax

module Ident = FStarC.Ident
module SMap  = FStarC.SMap

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
     | _ -> None)
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
let bool_name : name = { ns = ["Prims"]; id = "bool"; uniq = 0; hint = None }

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

    | _ -> None

(* -------------------------------------------------------------------- *)
(* Prims                                                                *)
(* -------------------------------------------------------------------- *)

(* The boolean connectives.  Without these they would be emitted as calls to
   [Prims_op_AmpAmp], which has no realization in C.  The comparison and
   arithmetic operators of [Prims] are deliberately *not* here: they act on
   unbounded integers, which no C backend can represent, so leaving them as
   ordinary calls keeps the failure at link time and legible. *)
let prims_rule (id:string) : ML (option rule) =
  let bool_op (o:op) (arity:int) : ML (option rule) =
    let po = { po_op = o; po_int = None } in
    Some (Rule_prim (arity, fun _ args ->
            mk (EOp (po, args)) (TApp (bool_name, [])) E_Pure)) in
  match id with
  | "op_AmpAmp"   -> bool_op And 2
  | "op_BarBar"   -> bool_op Or 2
  | "op_Negation" -> bool_op Not 1
  | _ -> None

(* -------------------------------------------------------------------- *)
(* Lookup                                                               *)
(* -------------------------------------------------------------------- *)

let lookup_rule (l:Ident.lident) : ML (option rule) =
  match SMap.try_find table (Ident.string_of_lid l) with
  | Some r -> Some r
  | None ->
    let path = Ident.path_of_lid l in
    match List.rev path with
    | id :: rev_ns ->
      (match machine_int_of_module (List.rev rev_ns) with
       | Some sw -> machine_int_rule sw id
       | None ->
         if List.rev rev_ns = ["Prims"] then prims_rule id else None)
    | [] -> None
