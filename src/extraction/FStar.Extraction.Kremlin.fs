(*
   Copyright 2008-2015 Abhishek Anand, Nikhil Swamy and Microsoft Research

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
(* -------------------------------------------------------------------- *)
#light "off"

module FStar.Extraction.Kremlin
open FStar.All

open FStar
open FStar.Util
open FStar.Extraction
open FStar.Extraction.ML
open FStar.Extraction.ML.Syntax
open FStar.Format
open FStar.Const
open FStar.BaseTypes

module BU = FStar.Util

(* COPY-PASTED ****************************************************************)

type program =
  list<decl>

and decl =
  | DGlobal of list<flag> * lident * typ * expr
  | DFunction of option<cc> * list<flag> * int * typ * lident * list<binder> * expr
  | DTypeAlias of lident * int * typ
  | DTypeFlat of lident * int * fields_t
  | DExternal of option<cc> * lident * typ
  | DTypeVariant of lident * int * branches_t

and cc =
  | StdCall
  | CDecl
  | FastCall

and fields_t =
  list<(ident * (typ * bool))>

and branches_t =
  list<(ident * fields_t)>

and flag =
  | Private
  | NoExtract
  | CInline
  | Substitute

and lifetime =
  | Eternal
  | Stack

and expr =
  | EBound of var
  | EQualified of lident
  | EConstant of constant
  | EUnit
  | EApp of expr * list<expr>
  | ELet of binder * expr * expr
  | EIfThenElse of expr * expr * expr
  | ESequence of list<expr>
  | EAssign of expr * expr
  | (** left expression can only be a EBound of EOpen *)
    EBufCreate of lifetime * expr * expr
  | EBufRead of expr * expr
  | EBufWrite of expr * expr * expr
  | EBufSub of expr * expr
  | EBufBlit of expr * expr * expr * expr * expr
  | EMatch of expr * branches
  | EOp of op * width
  | ECast of expr * typ
  | EPushFrame
  | EPopFrame
  | EBool of bool
  | EAny
  | EAbort
  | EReturn of expr
  | EFlat of typ * list<(ident * expr)>
  | EField of typ * expr * ident
  | EWhile of expr * expr
  | EBufCreateL of lifetime * list<expr>
  | ETuple of list<expr>
  | ECons of typ * ident * list<expr>
  | EBufFill of expr * expr * expr
  | EString of string
  | EFun of list<binder> * expr

and op =
  | Add | AddW | Sub | SubW | Div | DivW | Mult | MultW | Mod
  | BOr | BAnd | BXor | BShiftL | BShiftR | BNot
  | Eq | Neq | Lt | Lte | Gt | Gte
  | And | Or | Xor | Not

and branches =
  list<branch>

and branch =
  pattern * expr

and pattern =
  | PUnit
  | PBool of bool
  | PVar of binder
  | PCons of (ident * list<pattern>)
  | PTuple of list<pattern>
  | PRecord of list<(ident * pattern)>

and width =
  | UInt8 | UInt16 | UInt32 | UInt64
  | Int8 | Int16 | Int32 | Int64
  | Bool
  | Int | UInt

and constant = width * string

(* a De Bruijn index *)
and var = int

and binder = {
  name: ident;
  typ: typ;
  mut: bool;
}

(* for pretty-printing *)
and ident = string

and lident =
  list<ident> * ident

and typ =
  | TInt of width
  | TBuf of typ
  | TUnit
  | TQualified of lident
  | TBool
  | TAny
  | TArrow of typ * typ
  | TZ
  | TBound of int
  | TApp of lident * list<typ>
  | TTuple of list<typ>

(** Versioned binary writing/reading of ASTs *)

type version = int
let current_version: version = 20

type file = string * program
type binary_format = version * list<file>


(* Utilities *****************************************************************)

let fst3 (x, _, _) = x
let snd3 (_, x, _) = x
let thd3 (_, _, x) = x

let mk_width = function
  | "UInt8" -> Some UInt8
  | "UInt16" -> Some UInt16
  | "UInt32" -> Some UInt32
  | "UInt64" -> Some UInt64
  | "Int8" -> Some Int8
  | "Int16" -> Some Int16
  | "Int32" -> Some Int32
  | "Int64" -> Some Int64
  | _ -> None

let mk_bool_op = function
  | "op_Negation" ->
      Some Not
  | "op_AmpAmp" ->
      Some And
  | "op_BarBar" ->
      Some Or
  | "op_Equality" ->
      Some Eq
  | "op_disEquality" ->
      Some Neq
  | _ ->
      None

let is_bool_op op =
  mk_bool_op op <> None

let mk_op = function
  | "add" | "op_Plus_Hat" ->
      Some Add
  | "add_mod" | "op_Plus_Percent_Hat" ->
      Some AddW
  | "sub" | "op_Subtraction_Hat" ->
      Some Sub
  | "sub_mod" | "op_Subtraction_Percent_Hat" ->
      Some SubW
  | "mul" | "op_Star_Hat" ->
      Some Mult
  | "mul_mod" | "op_Star_Percent_Hat" ->
      Some MultW
  | "div" | "op_Slash_Hat" ->
      Some Div
  | "div_mod" | "op_Slash_Percent_Hat" ->
      Some DivW
  | "rem" | "op_Percent_Hat" ->
      Some Mod
  | "logor" | "op_Bar_Hat" ->
      Some BOr
  | "logxor" | "op_Hat_Hat" ->
      Some BXor
  | "logand" | "op_Amp_Hat" ->
      Some BAnd
  | "lognot" ->
      Some BNot
  | "shift_right" | "op_Greater_Greater_Hat" ->
      Some BShiftR
  | "shift_left" | "op_Less_Less_Hat" ->
      Some BShiftL
  | "eq" | "op_Equals_Hat" ->
      Some Eq
  | "op_Greater_Hat" | "gt" ->
      Some Gt
  | "op_Greater_Equals_Hat" | "gte" ->
      Some Gte
  | "op_Less_Hat" | "lt" ->
      Some Lt
  | "op_Less_Equals_Hat" | "lte" ->
      Some Lte
  | _ ->
      None

let is_op op =
  mk_op op <> None

let is_machine_int m =
  mk_width m <> None

(* Environments **************************************************************)

type env = {
  names: list<name>;
  names_t: list<string>;
  module_name: list<string>;
}

and name = {
  pretty: string;
  mut: bool;
}

let empty module_name = {
  names = [];
  names_t = [];
  module_name = module_name
}

let extend env x is_mut =
  { env with names = { pretty = x; mut = is_mut } :: env.names }

let extend_t env x =
  { env with names_t = x :: env.names_t }

let find_name env x =
  match List.tryFind (fun name -> name.pretty = x) env.names with
  | Some name ->
      name
  | None ->
      failwith "internal error: name not found"

let is_mutable env x =
  (find_name env x).mut

let find env x =
  try
    List.index (fun name -> name.pretty = x) env.names
  with _ ->
    failwith (BU.format1 "Internal error: name not found %s\n" x)

let find_t env x =
  try
    List.index (fun name -> name = x) env.names_t
  with _ ->
    failwith (BU.format1 "Internal error: name not found %s\n" x)

let add_binders env binders =
  List.fold_left (fun env ((name, _), _) -> extend env name false) env binders

(* Actual translation ********************************************************)

let rec translate (MLLib modules): list<file> =
  List.filter_map (fun m ->
    let m_name =
      let (prefix, final), _, _ = m in
      String.concat "." (prefix @ [ final ])
    in
    try
      BU.print1 "Attempting to translate module %s\n" m_name;
      Some (translate_module m)
    with
    | e ->
        BU.print2 "Unable to translate module: %s because:\n  %s\n"
          m_name (BU.print_exn e);
        None
  ) modules

and translate_module (module_name, modul, _): file =
  let module_name = fst module_name @ [ snd module_name ] in
  let program = match modul with
    | Some (_signature, decls) ->
        List.filter_map (translate_decl (empty module_name)) decls
    | _ ->
        failwith "Unexpected standalone interface or nested modules"
  in
  (String.concat "_" module_name), program

and translate_flags flags =
  List.choose (function
    | Syntax.Private -> Some Private
    | Syntax.NoExtract -> Some NoExtract
    | Syntax.Attribute "c_inline" -> Some CInline
    | Syntax.Attribute "substitute" -> Some Substitute
    | Syntax.Attribute a ->
        print1_warning "Warning: unrecognized attribute %s" a;
        None
    | _ -> None
  ) flags

and translate_decl env d: option<decl> =
  match d with
  | MLM_Let (flavor, flags, [ {
      mllb_name = name, _;
      mllb_tysc = Some (tvars, t0);
      mllb_def = { expr = MLE_Fun (args, body) }
    } ])
  | MLM_Let (flavor, flags, [ {
      mllb_name = name, _;
      mllb_tysc = Some (tvars, t0);
      mllb_def = { expr = MLE_Coerce ({ expr = MLE_Fun (args, body) }, _, _) }
    } ]) ->
      let assumed = BU.for_some (function Syntax.Assumed -> true | _ -> false) flags in
      let env = if flavor = Rec then extend env name false else env in
      let env = List.fold_left (fun env (name, _) -> extend_t env name) env tvars in
      let rec find_return_type = function
        | MLTY_Fun (_, _, t) ->
            find_return_type t
        | t ->
            t
      in
      let t = translate_type env (find_return_type t0) in
      let binders = translate_binders env args in
      let env = add_binders env args in
      let name = env.module_name, name in
      let flags = translate_flags flags in
      if assumed then
        if List.length tvars = 0 then
          Some (DExternal (None, name, translate_type env t0))
        else
          None
      else begin
        try
          let body = translate_expr env body in
          Some (DFunction (None, flags, List.length tvars, t, name, binders, body))
        with e ->
          BU.print2 "Warning: writing a stub for %s (%s)\n" (snd name) (BU.print_exn e);
          Some (DFunction (None, flags, List.length tvars, t, name, binders, EAbort))
      end

  | MLM_Let (flavor, flags, [ {
      mllb_name = name, _;
      mllb_tysc = Some ([], t);
      mllb_def = expr
    } ]) ->
      let flags = translate_flags flags in
      let t = translate_type env t in
      let name = env.module_name, name in
      begin try
        let expr = translate_expr env expr in
        Some (DGlobal (flags, name, t, expr))
      with e ->
        BU.print2 "Warning: not translating definition for %s (%s)\n" (snd name) (BU.print_exn e);
        Some (DGlobal (flags, name, t, EAny))
      end

  | MLM_Let (_, _, { mllb_name = name, _; mllb_tysc = ts } :: _) ->
      (* Things we currently do not translate:
       * - polymorphic functions (lemmas do count, sadly)
       *)
      BU.print1 "Warning: not translating definition for %s (and possibly others)\n" name;
      begin match ts with
      | Some (idents, t) ->
          BU.print2 "Type scheme is: forall %s. %s\n"
            (String.concat ", " (List.map fst idents))
            (ML.Code.string_of_mlty ([], "") t)
      | None ->
          ()
      end;
      None

  | MLM_Let _ ->
      failwith "impossible"

  | MLM_Loc _ ->
      None

  | MLM_Ty [ (assumed, name, _mangled_name, args, Some (MLTD_Abbrev t)) ] ->
      let name = env.module_name, name in
      let env = List.fold_left (fun env (name, _) -> extend_t env name) env args in
      if assumed then
        None
      else
        Some (DTypeAlias (name, List.length args, translate_type env t))

  | MLM_Ty [ (_, name, _mangled_name, args, Some (MLTD_Record fields)) ] ->
      let name = env.module_name, name in
      let env = List.fold_left (fun env (name, _) -> extend_t env name) env args in
      Some (DTypeFlat (name, List.length args, List.map (fun (f, t) ->
        f, (translate_type env t, false)) fields))

  | MLM_Ty [ (_, name, _mangled_name, args, Some (MLTD_DType branches)) ] ->
      let name = env.module_name, name in
      let env = List.fold_left (fun env (name, _) -> extend_t env name) env args in
      Some (DTypeVariant (name, List.length args, List.mapi (fun i (cons, ts) ->
        cons, List.mapi (fun j t ->
          // TODO: carry the right names
          BU.format2 "x%s%s" (string_of_int i) (string_of_int j), (translate_type env t, false)
        ) ts
      ) branches))

  | MLM_Ty ((_, name, _mangled_name, _, _) :: _) ->
      BU.print1 "Warning: not translating definition for %s (and possibly others)\n" name;
      None

  | MLM_Ty [] ->
      BU.print_string "Impossible!! Empty block of mutually recursive type declarations";
      None

  | MLM_Top _ ->
      failwith "todo: translate_decl [MLM_Top]"

  | MLM_Exn _ ->
      failwith "todo: translate_decl [MLM_Exn]"

and translate_type env t: typ =
  match t with
  | MLTY_Tuple []
  | MLTY_Top ->
      TAny
  | MLTY_Var (name, _) ->
      TBound (find_t env name)
  | MLTY_Fun (t1, _, t2) ->
      TArrow (translate_type env t1, translate_type env t2)
  | MLTY_Named ([], p) when (Syntax.string_of_mlpath p = "Prims.unit") ->
      TUnit
  | MLTY_Named ([], p) when (Syntax.string_of_mlpath p = "Prims.bool") ->
      TBool
  | MLTY_Named ([], ([ "FStar"; m ], "t")) when is_machine_int m ->
      TInt (must (mk_width m))
  | MLTY_Named ([], ([ "FStar"; m ], "t'")) when is_machine_int m ->
      TInt (must (mk_width m))
  | MLTY_Named ([arg], p) when (Syntax.string_of_mlpath p = "FStar.Buffer.buffer") ->
      TBuf (translate_type env arg)
  | MLTY_Named ([_], p) when (Syntax.string_of_mlpath p = "FStar.Ghost.erased") ->
      TAny
  | MLTY_Named ([], (path, type_name)) ->
      // Generate an unbound reference... to be filled in later by glue code.
      TQualified (path, type_name)
  | MLTY_Named (args, (ns, t)) when (ns = ["Prims"] || ns = ["FStar"; "Pervasives"]) && BU.starts_with t "tuple" ->
      TTuple (List.map (translate_type env) args)
  | MLTY_Named (args, lid) ->
      if List.length args > 0 then
        TApp (lid, List.map (translate_type env) args)
      else
        TQualified lid
  | MLTY_Tuple ts ->
      TTuple (List.map (translate_type env) ts)

and translate_binders env args =
  List.map (translate_binder env) args

and translate_binder env ((name, _), typ) =
  { name = name; typ = translate_type env typ; mut = false }

and translate_expr env e: expr =
  match e.expr with
  | MLE_Tuple [] ->
      EUnit

  | MLE_Const c ->
      translate_constant c

  | MLE_Var (name, _) ->
      EBound (find env name)

  // Some of these may not appear beneath an [EApp] node because of partial applications
  | MLE_Name ([ "FStar"; m ], op) when (is_machine_int m && is_op op) ->
      EOp (must (mk_op op), must (mk_width m))

  | MLE_Name ([ "Prims" ], op) when (is_bool_op op) ->
      EOp (must (mk_bool_op op), Bool)

  | MLE_Name n ->
      EQualified n

  | MLE_Let ((flavor, flags, [{
      mllb_name = name, _;
      mllb_tysc = Some ([], typ); // assuming unquantified type
      mllb_add_unit = add_unit; // ?
      mllb_def = body;
      print_typ = print // ?
    }]), continuation) ->
      let is_mut = BU.for_some (function Mutable -> true | _ -> false) flags in
      let typ, body =
        if is_mut then
          (match typ with
          | MLTY_Named ([ t ], p) when string_of_mlpath p = "FStar.ST.stackref" -> t
          | _ -> failwith (BU.format1
            "unexpected: bad desugaring of Mutable (typ is %s)"
            (ML.Code.string_of_mlty ([], "") typ))),
          (match body with
          | { expr = MLE_App (_, [ body ]) } -> body
          | _ -> failwith "unexpected: bad desugaring of Mutable")
        else
          typ, body
      in
      let binder = { name = name; typ = translate_type env typ; mut = is_mut } in
      let body = translate_expr env body in
      let env = extend env name is_mut in
      let continuation = translate_expr env continuation in
      ELet (binder, body, continuation)

  | MLE_Match (expr, branches) ->
      EMatch (translate_expr env expr, translate_branches env branches)

  // We recognize certain distinguished names from [FStar.HST] and other
  // modules, and translate them into built-in Kremlin constructs
  | MLE_App ({ expr = MLE_Name p }, [ { expr = MLE_Var (v, _) } ]) when (string_of_mlpath p = "FStar.ST.op_Bang" && is_mutable env v) ->
      EBound (find env v)
  | MLE_App ({ expr = MLE_Name p }, [ { expr = MLE_Var (v, _) }; e ]) when (string_of_mlpath p = "FStar.ST.op_Colon_Equals" && is_mutable env v) ->
      EAssign (EBound (find env v), translate_expr env e)
  | MLE_App ({ expr = MLE_Name p }, [ e1; e2 ])
    when string_of_mlpath p = "FStar.Buffer.index" || string_of_mlpath p = "FStar.Buffer.op_Array_Access" ->
      EBufRead (translate_expr env e1, translate_expr env e2)
  | MLE_App ({ expr = MLE_Name p }, [ e1; e2 ]) when (string_of_mlpath p = "FStar.Buffer.create") ->
      EBufCreate (Stack, translate_expr env e1, translate_expr env e2)
  | MLE_App ({ expr = MLE_Name p }, [ _e0; e1; e2 ]) when (string_of_mlpath p = "FStar.Buffer.rcreate") ->
      EBufCreate (Eternal, translate_expr env e1, translate_expr env e2)
  | MLE_App ({ expr = MLE_Name p }, [ e2 ]) when (string_of_mlpath p = "FStar.Buffer.createL") ->
      let rec list_elements acc e2 =
        match e2.expr with
        | MLE_CTor (([ "Prims" ], "Cons" ), [ hd; tl ]) ->
            list_elements (hd :: acc) tl
        | MLE_CTor (([ "Prims" ], "Nil" ), []) ->
            List.rev acc
        | _ ->
            failwith "Argument of FStar.Buffer.createL is not a string literal!"
      in
      let list_elements = list_elements [] in
      EBufCreateL (Stack, List.map (translate_expr env) (list_elements e2))
  | MLE_App ({ expr = MLE_Name p }, [ e1; e2; _e3 ]) when (string_of_mlpath p = "FStar.Buffer.sub") ->
      EBufSub (translate_expr env e1, translate_expr env e2)
  | MLE_App ({ expr = MLE_Name p }, [ e1; e2 ]) when (string_of_mlpath p = "FStar.Buffer.join") ->
      (translate_expr env e1)
  | MLE_App ({ expr = MLE_Name p }, [ e1; e2 ]) when (string_of_mlpath p = "FStar.Buffer.offset") ->
      EBufSub (translate_expr env e1, translate_expr env e2)
  | MLE_App ({ expr = MLE_Name p }, [ e1; e2; e3 ])
    when string_of_mlpath p = "FStar.Buffer.upd" || string_of_mlpath p = "FStar.Buffer.op_Array_Assignment" ->
      EBufWrite (translate_expr env e1, translate_expr env e2, translate_expr env e3)
  | MLE_App ({ expr = MLE_Name p }, [ _ ]) when (string_of_mlpath p = "FStar.ST.push_frame") ->
      EPushFrame
  | MLE_App ({ expr = MLE_Name p }, [ _ ]) when (string_of_mlpath p = "FStar.ST.pop_frame") ->
      EPopFrame
  | MLE_App ({ expr = MLE_Name p }, [ e1; e2; e3; e4; e5 ]) when (string_of_mlpath p = "FStar.Buffer.blit") ->
      EBufBlit (translate_expr env e1, translate_expr env e2, translate_expr env e3, translate_expr env e4, translate_expr env e5)
  | MLE_App ({ expr = MLE_Name p }, [ e1; e2; e3 ]) when (string_of_mlpath p = "FStar.Buffer.fill") ->
      EBufFill (translate_expr env e1, translate_expr env e2, translate_expr env e3)
  | MLE_App ({ expr = MLE_Name p }, [ _ ]) when string_of_mlpath p = "FStar.ST.get" ->
      // We need to reveal to Kremlin that FStar.HST.get is equivalent to
      // (void*)0 so that it can get rid of ghost calls to HST.get at the
      // beginning of functions, which is needed to enforce the push/pop
      // structure.
      EUnit

  | MLE_App ({ expr = MLE_Name p }, [ e ]) when string_of_mlpath p = "Obj.repr" ->
      ECast (translate_expr env e, TAny)

  // Operators from fixed-width integer modules, e.g. [FStar.Int32.addw].
  | MLE_App ({ expr = MLE_Name ([ "FStar"; m ], op) }, args) when (is_machine_int m && is_op op) ->
      mk_op_app env (must (mk_width m)) (must (mk_op op)) args

  | MLE_App ({ expr = MLE_Name ([ "Prims" ], op) }, args) when (is_bool_op op) ->
      mk_op_app env Bool (must (mk_bool_op op)) args

  // Fixed-width literals are represented as calls to [FStar.Int32.uint_to_t]
  | MLE_App ({ expr = MLE_Name ([ "FStar"; m ], "int_to_t") }, [ { expr = MLE_Const (MLC_Int (c, None)) }])
  | MLE_App ({ expr = MLE_Name ([ "FStar"; m ], "uint_to_t") }, [ { expr = MLE_Const (MLC_Int (c, None)) }]) when is_machine_int m ->
      EConstant (must (mk_width m), c)

  | MLE_App ({ expr = MLE_Name ([ "C" ], "string_of_literal") }, [ { expr = e } ]) ->
      begin match e with
      | MLE_Const (MLC_String s) ->
          EString s
      | _ ->
          failwith "Cannot extract string_of_literal applied to a non-literal"
      end

  | MLE_App ({ expr = MLE_Name ([ "FStar"; "Int"; "Cast" ], c) }, [ arg ]) ->
      let is_known_type =
        starts_with c "uint8" || starts_with c "uint16" ||
        starts_with c "uint32" || starts_with c "uint64" ||
        starts_with c "int8" || starts_with c "int16" ||
        starts_with c "int32" || starts_with c "int64"
      in
      if ends_with c "uint64" && is_known_type then
        ECast (translate_expr env arg, TInt UInt64)
      else if ends_with c "uint32" && is_known_type then
        ECast (translate_expr env arg, TInt UInt32)
      else if ends_with c "uint16" && is_known_type then
        ECast (translate_expr env arg, TInt UInt16)
      else if ends_with c "uint8" && is_known_type then
        ECast (translate_expr env arg, TInt UInt8)
      else if ends_with c "int64" && is_known_type then
        ECast (translate_expr env arg, TInt Int64)
      else if ends_with c "int32" && is_known_type then
        ECast (translate_expr env arg, TInt Int32)
      else if ends_with c "int16" && is_known_type then
        ECast (translate_expr env arg, TInt Int16)
      else if ends_with c "int8" && is_known_type then
        ECast (translate_expr env arg, TInt Int8)
      else
        EApp (EQualified ([ "FStar"; "Int"; "Cast" ], c), [ translate_expr env arg ])

  | MLE_App ({ expr = MLE_Name (path, function_name) }, args) ->
      EApp (EQualified (path, function_name), List.map (translate_expr env) args)

  | MLE_App ({ expr = MLE_Var (name, _) }, args) ->
      EApp (EBound (find env name), List.map (translate_expr env) args)

  | MLE_Coerce (e, t_from, t_to) ->
      ECast (translate_expr env e, translate_type env t_to)

  | MLE_Record (_, fields) ->
      EFlat (assert_lid env e.mlty, List.map (fun (field, expr) ->
        field, translate_expr env expr) fields)

  | MLE_Proj (e, path) ->
      EField (assert_lid env e.mlty, translate_expr env e, snd path)

  | MLE_Let _ ->
      (* Things not supported (yet): let-bindings for functions; meaning, rec flags are not
       * supported, and quantified type schemes are not supported either *)
      failwith "todo: translate_expr [MLE_Let]"
  | MLE_App (head, _) ->
      failwith (BU.format1 "todo: translate_expr [MLE_App] (head is: %s)"
        (ML.Code.string_of_mlexpr ([], "") head))
  | MLE_Seq seqs ->
      ESequence (List.map (translate_expr env) seqs)
  | MLE_Tuple es ->
      ETuple (List.map (translate_expr env) es)

  | MLE_CTor ((_, cons), es) ->
      ECons (assert_lid env e.mlty, cons, List.map (translate_expr env) es)

  | MLE_Fun (args, body) ->
      let binders = translate_binders env args in
      let env = add_binders env args in
      EFun (binders, translate_expr env body)

  | MLE_If (e1, e2, e3) ->
      EIfThenElse (translate_expr env e1, translate_expr env e2, (match e3 with
        | None -> EUnit
        | Some e3 -> translate_expr env e3))
  | MLE_Raise _ ->
      failwith "todo: translate_expr [MLE_Raise]"
  | MLE_Try _ ->
      failwith "todo: translate_expr [MLE_Try]"
  | MLE_Coerce _ ->
      failwith "todo: translate_expr [MLE_Coerce]"

and assert_lid env t =
  match t with
  | MLTY_Named (ts, lid) ->
      if List.length ts > 0 then
        TApp (lid, List.map (translate_type env) ts)
      else
        TQualified lid
  | _ -> failwith "invalid argument: assert_lid"

and translate_branches env branches =
  List.map (translate_branch env) branches

and translate_branch env (pat, guard, expr) =
  if guard = None then
    let env, pat = translate_pat env pat in
    pat, translate_expr env expr
  else
    failwith "todo: translate_branch"

and translate_pat env p =
  match p with
  | MLP_Const MLC_Unit ->
      env, PUnit
  | MLP_Const (MLC_Bool b) ->
      env, PBool b
  | MLP_Var (name, _) ->
      let env = extend env name false in
      env, PVar ({ name = name; typ = TAny; mut = false })
  | MLP_Wild ->
      let env = extend env "_" false in
      env, PVar ({ name = "_"; typ = TAny; mut = false })
  | MLP_CTor ((_, cons), ps) ->
      let env, ps = List.fold_left (fun (env, acc) p ->
        let env, p = translate_pat env p in
        env, p :: acc
      ) (env, []) ps in
      env, PCons (cons, List.rev ps)
  | MLP_Record (_, ps) ->
      let env, ps = List.fold_left (fun (env, acc) (field, p) ->
        let env, p = translate_pat env p in
        env, (field, p) :: acc
      ) (env, []) ps in
      env, PRecord (List.rev ps)

  | MLP_Tuple ps ->
      let env, ps = List.fold_left (fun (env, acc) p ->
        let env, p = translate_pat env p in
        env, p :: acc
      ) (env, []) ps in
      env, PTuple (List.rev ps)

  | MLP_Const _ ->
      failwith "todo: translate_pat [MLP_Const]"
  | MLP_Branch _ ->
      failwith "todo: translate_pat [MLP_Branch]"

and translate_constant c: expr =
  match c with
  | MLC_Unit ->
      EUnit
  | MLC_Bool b ->
      EBool b
  | MLC_Int (s, Some _) ->
      failwith "impossible: machine integer not desugared to a function call"
  | MLC_Float _ ->
      failwith "todo: translate_expr [MLC_Float]"
  | MLC_Char _ ->
      failwith "todo: translate_expr [MLC_Char]"
  | MLC_String _ ->
      failwith "todo: translate_expr [MLC_String]"
  | MLC_Bytes _ ->
      failwith "todo: translate_expr [MLC_Bytes]"
  | MLC_Int (_, None) ->
      failwith "todo: translate_expr [MLC_Int]"

(* Helper functions **********************************************************)

and mk_op_app env w op args =
  EApp (EOp (op, w), List.map (translate_expr env) args)
