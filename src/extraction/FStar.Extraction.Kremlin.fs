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
open FStar.ST
open FStar.All

open FStar
open FStar.Util
open FStar.Extraction
open FStar.Extraction.ML
open FStar.Extraction.ML.Syntax
open FStar.Const
open FStar.BaseTypes

module BU = FStar.Util
module FC = FStar.Const

(** CHANGELOG
- v24: Added a single constructor to the expression type to reflect the addition
  of type applications to the ML extraction language.
- v25: Added a number of type parameters for globals.
- v26: Flags for DExternal and all the DType's
- v27: Added PConstant
*)

(* COPY-PASTED ****************************************************************)

type program =
  list<decl>

and decl =
  | DGlobal of list<flag> * lident * int * typ * expr
  | DFunction of option<cc> * list<flag> * int * typ * lident * list<binder> * expr
  | DTypeAlias of lident * list<flag> * int * typ
  | DTypeFlat of lident * list<flag> * int * fields_t
  | DUnusedRetainedForBackwardsCompat of option<cc> * list<flag> * lident * typ
  | DTypeVariant of lident * list<flag> * int * branches_t
  | DTypeAbstractStruct of lident
  | DExternal of option<cc> * list<flag> * lident * typ * list<ident>

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
  | WipeBody
  | CInline
  | Substitute
  | GCType
  | Comment of string
  | MustDisappear
  | Const of string
  | Prologue of string
  | Epilogue of string
  | Abstract
  | IfDef
  | Macro

and fsdoc = string

and lifetime =
  | Eternal
  | Stack
  | ManuallyManaged

and expr =
  | EBound of var
  | EQualified of lident
  | EConstant of constant
  | EUnit
  | EApp of expr * list<expr>
  | ETypApp of expr * list<typ>
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
  | EFun of list<binder> * expr * typ
  | EAbortS of string
  | EBufFree of expr
  | EBufCreateNoInit of lifetime * expr


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
  | PConstant of constant

and width =
  | UInt8 | UInt16 | UInt32 | UInt64
  | Int8 | Int16 | Int32 | Int64
  | Bool
  | CInt

and constant = width * string

(* a De Bruijn index *)
and var = int

and binder = {
  name: ident;
  typ: typ;
  mut: bool
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
  | TBound of int
  | TApp of lident * list<typ>
  | TTuple of list<typ>

(** Versioned binary writing/reading of ASTs *)

type version = int
let current_version: version = 27

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
  | "add" | "op_Plus_Hat" | "add_underspec" ->
      Some Add
  | "add_mod" | "op_Plus_Percent_Hat" ->
      Some AddW
  | "sub" | "op_Subtraction_Hat" | "sub_underspec" ->
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
}

let empty module_name = {
  names = [];
  names_t = [];
  module_name = module_name
}

let extend env x =
  { env with names = { pretty = x } :: env.names }

let extend_t env x =
  { env with names_t = x :: env.names_t }

let find_name env x =
  match List.tryFind (fun name -> name.pretty = x) env.names with
  | Some name ->
      name
  | None ->
      failwith "internal error: name not found"

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
  List.fold_left (fun env (name, _) -> extend env name) env binders

(* Actual translation ********************************************************)

let list_elements e2 =
  let rec list_elements acc e2 =
    match e2.expr with
    | MLE_CTor (([ "Prims" ], "Cons" ), [ hd; tl ]) ->
        list_elements (hd :: acc) tl
    | MLE_CTor (([ "Prims" ], "Nil" ), []) ->
        List.rev acc
    | _ ->
        failwith "Argument of FStar.Buffer.createL is not a list literal!"
  in
  list_elements [] e2

let rec translate (MLLib modules): list<file> =
  List.filter_map (fun m ->
    let m_name =
      let path, _, _ = m in
      Syntax.string_of_mlpath path
    in
    try
      if not (Options.silent()) then (BU.print1 "Attempting to translate module %s\n" m_name);
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
        List.collect (translate_decl (empty module_name)) decls
    | _ ->
        failwith "Unexpected standalone interface or nested modules"
  in
  (String.concat "_" module_name), program

and translate_flags flags =
  List.choose (function
    | Syntax.Private -> Some Private
    | Syntax.NoExtract -> Some WipeBody
    | Syntax.CInline -> Some CInline
    | Syntax.Substitute -> Some Substitute
    | Syntax.GCType -> Some GCType
    | Syntax.Comment s -> Some (Comment s)
    | Syntax.StackInline -> Some MustDisappear
    | Syntax.CConst s -> Some (Const s)
    | Syntax.CPrologue s -> Some (Prologue s)
    | Syntax.CEpilogue s -> Some (Epilogue s)
    | Syntax.CAbstract -> Some Abstract
    | Syntax.CIfDef -> Some IfDef
    | Syntax.CMacro -> Some Macro
    | _ -> None // is this all of them?
  ) flags

and translate_cc flags =
  match List.choose (function | Syntax.CCConv s -> Some s | _ -> None) flags with
  | [ "stdcall" ] -> Some StdCall
  | [ "fastcall" ] -> Some FastCall
  | [ "cdecl" ] -> Some CDecl
  | _ -> None

and translate_decl env d: list<decl> =
  match d with
  | MLM_Let (flavor, lbs) ->
      // We don't care about mutual recursion, since every C file will include
      // its own header with the forward declarations.
      List.choose (translate_let env flavor) lbs

  | MLM_Loc _ ->
      // JP: TODO: use this to reconstruct location information
      []

  | MLM_Ty tys ->
      // We don't care about mutual recursion, since KreMLin will insert forward
      // declarations exactly as needed, as part of its monomorphization phase
      List.choose (translate_type_decl env) tys

  | MLM_Top _ ->
      failwith "todo: translate_decl [MLM_Top]"

  | MLM_Exn (m, _) ->
      BU.print1_warning "Not extracting exception %s to KreMLin (exceptions unsupported)\n" m;
      []

and translate_let env flavor lb: option<decl> =
  match lb with
  | {
      mllb_name = name;
      mllb_tysc = Some (tvars, t0);
      mllb_def = e;
      mllb_meta = meta
    } when BU.for_some (function Syntax.Assumed -> true | _ -> false) meta ->
      let name = env.module_name, name in
      let arg_names = match e.expr with
        | MLE_Fun (args, _) -> List.map fst args
        | _ -> []
      in
      if List.length tvars = 0 then
        Some (DExternal (translate_cc meta, translate_flags meta, name, translate_type env t0, arg_names))
      else begin
        BU.print1_warning "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n" (Syntax.string_of_mlpath name);
        None
      end

  | {
      mllb_name = name;
      mllb_tysc = Some (tvars, t0);
      mllb_def = { expr = MLE_Fun (args, body) };
      mllb_meta = meta
    } ->
      if List.mem Syntax.NoExtract meta then
        None
      else
        // Case 1: a possibly-polymorphic function.
        let env = if flavor = Rec then extend env name else env in
        let env = List.fold_left (fun env name -> extend_t env name) env tvars in
        let rec find_return_type eff i = function
          | MLTY_Fun (_, eff, t) when i > 0 ->
              find_return_type eff (i - 1) t
          | t ->
              i, eff, t
        in
        let name = env.module_name, name in
        let i, eff, t = find_return_type E_PURE (List.length args) t0 in
        if i > 0 then begin
          let msg = "function type annotation has less arrows than the \
            number of arguments; please mark the return type abbreviation as \
            inline_for_extraction" in
          BU.print2_warning "Not extracting %s to KreMLin (%s)\n" (Syntax.string_of_mlpath name) msg
        end;
        let t = translate_type env t in
        let binders = translate_binders env args in
        let env = add_binders env args in
        let cc = translate_cc meta in
        let meta = match eff, t with
          | E_GHOST, _
          | E_PURE, TUnit -> MustDisappear :: translate_flags meta
          | _ -> translate_flags meta
        in
        begin try
          let body = translate_expr env body in
          Some (DFunction (cc, meta, List.length tvars, t, name, binders, body))
        with e ->
          // JP: TODO: figure out what are the remaining things we don't extract
          let msg = BU.print_exn e in
          Errors. log_issue Range.dummyRange
          (Errors.Warning_FunctionNotExtacted, (BU.format2 "Error while extracting %s to KreMLin (%s)\n" (Syntax.string_of_mlpath name) msg));
          let msg = "This function was not extracted:\n" ^ msg in
          Some (DFunction (cc, meta, List.length tvars, t, name, binders, EAbortS msg))
        end

  | {
      mllb_name = name;
      mllb_tysc = Some (tvars, t);
      mllb_def = expr;
      mllb_meta = meta
    } ->
      if List.mem Syntax.NoExtract meta then
        None
      else
        // Case 2: this is a global
        let meta = translate_flags meta in
        let env = List.fold_left (fun env name -> extend_t env name) env tvars in
        let t = translate_type env t in
        let name = env.module_name, name in
        begin try
          let expr = translate_expr env expr in
          Some (DGlobal (meta, name, List.length tvars, t, expr))
        with e ->
          Errors. log_issue Range.dummyRange (Errors.Warning_DefinitionNotTranslated, (BU.format2 "Error extracting %s to KreMLin (%s)\n" (Syntax.string_of_mlpath name) (BU.print_exn e)));
          Some (DGlobal (meta, name, List.length tvars, t, EAny))
        end

  | { mllb_name = name; mllb_tysc = ts } ->
      // TODO JP: figure out what exactly we're hitting here...?
      Errors. log_issue Range.dummyRange (Errors.Warning_DefinitionNotTranslated, (BU.format1 "Not extracting %s to KreMLin\n" name));
      begin match ts with
      | Some (idents, t) ->
          BU.print2 "Type scheme is: forall %s. %s\n"
            (String.concat ", " idents)
            (ML.Code.string_of_mlty ([], "") t)
      | None ->
          ()
      end;
      None


and translate_type_decl env ty: option<decl> =
  let _, _, _, _, flags, _ = ty in
  if List.mem Syntax.NoExtract flags then
    None
  else
    match ty with
    | (assumed, name, _mangled_name, args, flags, Some (MLTD_Abbrev t)) ->
        let name = env.module_name, name in
        let env = List.fold_left (fun env name -> extend_t env name) env args in
        if assumed && List.mem Syntax.CAbstract flags then
          Some (DTypeAbstractStruct name)
        else if assumed then
          let name = string_of_mlpath name in
          BU.print1_warning "Not extracting type definition %s to KreMLin (assumed type)\n" name;
          // JP: TODO: shall we be smarter here?
          None
        else
          Some (DTypeAlias (name, translate_flags flags, List.length args, translate_type env t))

    | (_, name, _mangled_name, args, flags, Some (MLTD_Record fields)) ->
        let name = env.module_name, name in
        let env = List.fold_left (fun env name -> extend_t env name) env args in
        Some (DTypeFlat (name, translate_flags flags, List.length args, List.map (fun (f, t) ->
          f, (translate_type env t, false)) fields))

    | (_, name, _mangled_name, args, flags, Some (MLTD_DType branches)) ->
        let name = env.module_name, name in
        let flags = translate_flags flags in
        let env = List.fold_left extend_t env args in
        Some (DTypeVariant (name, flags, List.length args, List.map (fun (cons, ts) ->
          cons, List.map (fun (name, t) ->
            name, (translate_type env t, false)
          ) ts
        ) branches))

    | (_, name, _mangled_name, _, _, _) ->
        // JP: TODO: figure out why and how this happens
        Errors. log_issue Range.dummyRange (Errors.Warning_DefinitionNotTranslated, (BU.format1 "Error extracting type definition %s to KreMLin\n" name));
        None

and translate_type env t: typ =
  match t with
  | MLTY_Tuple []
  | MLTY_Top ->
      TAny
  | MLTY_Var name ->
      TBound (find_t env name)
  | MLTY_Fun (t1, _, t2) ->
      TArrow (translate_type env t1, translate_type env t2)
  | MLTY_Erased ->
      TUnit
  | MLTY_Named ([], p) when (Syntax.string_of_mlpath p = "Prims.unit") ->
      TUnit
  | MLTY_Named ([], p) when (Syntax.string_of_mlpath p = "Prims.bool") ->
      TBool
  | MLTY_Named ([], ([ "FStar"; m ], "t")) when is_machine_int m ->
      TInt (must (mk_width m))
  | MLTY_Named ([], ([ "FStar"; m ], "t'")) when is_machine_int m ->
      TInt (must (mk_width m))
  | MLTY_Named ([arg], p) when (Syntax.string_of_mlpath p = "FStar.Monotonic.HyperStack.mem") ->
      TUnit

  | MLTY_Named ([_; arg; _], p) when
    Syntax.string_of_mlpath p = "FStar.Monotonic.HyperStack.s_mref" ||
    Syntax.string_of_mlpath p = "FStar.Monotonic.HyperHeap.mrref"  ||
    Syntax.string_of_mlpath p = "FStar.HyperStack.ST.m_rref" ||
    Syntax.string_of_mlpath p = "FStar.HyperStack.ST.s_mref"
    ->
      TBuf (translate_type env arg)
  | MLTY_Named ([arg; _], p) when
    Syntax.string_of_mlpath p = "FStar.Monotonic.HyperStack.mreference" ||
    Syntax.string_of_mlpath p = "FStar.Monotonic.HyperStack.mstackref" ||
    Syntax.string_of_mlpath p = "FStar.Monotonic.HyperStack.mref" ||
    Syntax.string_of_mlpath p = "FStar.Monotonic.HyperStack.mmmstackref" ||
    Syntax.string_of_mlpath p = "FStar.Monotonic.HyperStack.mmmref" ||
    Syntax.string_of_mlpath p = "FStar.Monotonic.Heap.mref" ||
    Syntax.string_of_mlpath p = "FStar.HyperStack.ST.mreference" ||
    Syntax.string_of_mlpath p = "FStar.HyperStack.ST.mstackref" ||
    Syntax.string_of_mlpath p = "FStar.HyperStack.ST.mref" ||
    Syntax.string_of_mlpath p = "FStar.HyperStack.ST.mmmstackref" ||
    Syntax.string_of_mlpath p = "FStar.HyperStack.ST.mmmref"
    ->
      TBuf (translate_type env arg)
  | MLTY_Named ([arg; _; _], p) when
    Syntax.string_of_mlpath p = "LowStar.Monotonic.Buffer.mbuffer" -> TBuf (translate_type env arg)
  | MLTY_Named ([arg], p) when
    Syntax.string_of_mlpath p = "FStar.Buffer.buffer" ||
    Syntax.string_of_mlpath p = "LowStar.Buffer.buffer" ||
    Syntax.string_of_mlpath p = "LowStar.ImmutableBuffer.ibuffer" ||
    Syntax.string_of_mlpath p = "LowStar.UninitializedBuffer.ubuffer" ||
    Syntax.string_of_mlpath p = "FStar.HyperStack.reference" ||
    Syntax.string_of_mlpath p = "FStar.HyperStack.stackref" ||
    Syntax.string_of_mlpath p = "FStar.HyperStack.ref" ||
    Syntax.string_of_mlpath p = "FStar.HyperStack.mmstackref" ||
    Syntax.string_of_mlpath p = "FStar.HyperStack.mmref" ||
    Syntax.string_of_mlpath p = "FStar.HyperStack.ST.reference" ||
    Syntax.string_of_mlpath p = "FStar.HyperStack.ST.stackref" ||
    Syntax.string_of_mlpath p = "FStar.HyperStack.ST.ref" ||
    Syntax.string_of_mlpath p = "FStar.HyperStack.ST.mmstackref" ||
    Syntax.string_of_mlpath p = "FStar.HyperStack.ST.mmref"
    ->
      TBuf (translate_type env arg)
  | MLTY_Named ([_;arg], p) when
    Syntax.string_of_mlpath p = "FStar.HyperStack.s_ref" ||
    Syntax.string_of_mlpath p = "FStar.HyperStack.ST.s_ref"
    ->
      TBuf (translate_type env arg)

  | MLTY_Named ([_], p) when (Syntax.string_of_mlpath p = "FStar.Ghost.erased") ->
      TAny
  | MLTY_Named ([], (path, type_name)) ->
      // Generate an unbound reference... to be filled in later by glue code.
      TQualified (path, type_name)
  | MLTY_Named (args, (ns, t)) when (ns = ["Prims"] || ns = ["FStar"; "Pervasives"; "Native"]) && BU.starts_with t "tuple" ->
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

and translate_binder env (name, typ) =
  { name = name; typ = translate_type env typ; mut = false }

and translate_expr env e: expr =
  match e.expr with
  | MLE_Tuple [] ->
      EUnit

  | MLE_Const c ->
      translate_constant c

  | MLE_Var name ->
      EBound (find env name)

  // Some of these may not appear beneath an [EApp] node because of partial applications
  | MLE_Name ([ "FStar"; m ], op) when (is_machine_int m && is_op op) ->
      EOp (must (mk_op op), must (mk_width m))

  | MLE_Name ([ "Prims" ], op) when (is_bool_op op) ->
      EOp (must (mk_bool_op op), Bool)

  | MLE_Name n ->
      EQualified n

  | MLE_Let ((flavor, [{
      mllb_name = name;
      mllb_tysc = Some ([], typ); // assuming unquantified type
      mllb_add_unit = add_unit; // ?
      mllb_def = body;
      mllb_meta = flags;
      print_typ = print // ?
    }]), continuation) ->
      let binder = { name = name; typ = translate_type env typ; mut = false } in
      let body = translate_expr env body in
      let env = extend env name in
      let continuation = translate_expr env continuation in
      ELet (binder, body, continuation)

  | MLE_Match (expr, branches) ->
      EMatch (translate_expr env expr, translate_branches env branches)

  // We recognize certain distinguished names from [FStar.HST] and other
  // modules, and translate them into built-in Kremlin constructs
  | MLE_App({expr=MLE_TApp ({ expr = MLE_Name p }, [t])}, [arg])
    when string_of_mlpath p = "FStar.Dyn.undyn" ->
      ECast (translate_expr env arg, translate_type env t)
  | MLE_App({expr=MLE_TApp ({ expr = MLE_Name p }, _)}, _)
    when string_of_mlpath p = "Prims.admit" ->
      EAbort
  | MLE_App({expr=MLE_TApp ({ expr = MLE_Name p }, _)}, [arg])
    when string_of_mlpath p = "FStar.HyperStack.All.failwith"
      ||  string_of_mlpath p = "FStar.Error.unexpected"
      ||  string_of_mlpath p = "FStar.Error.unreachable" ->
      (match arg with
       | {expr=MLE_Const (MLC_String msg)} -> EAbortS msg
       | _ ->
         let print = with_ty MLTY_Top (MLE_Name (mlpath_of_lident (Ident.lid_of_str "FStar.HyperStack.IO.print_string"))) in
         let print = with_ty MLTY_Top (MLE_App (print, [arg])) in
         let t = translate_expr env print in
         ESequence [t; EAbort])

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e ] )
    when string_of_mlpath p = "LowStar.ToFStarBuffer.new_to_old_st" ||
         string_of_mlpath p = "LowStar.ToFStarBuffer.old_to_new_st"
    ->
    translate_expr env e

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e1; e2 ])
    when string_of_mlpath p = "FStar.Buffer.index" || string_of_mlpath p = "FStar.Buffer.op_Array_Access"
      || string_of_mlpath p = "LowStar.Monotonic.Buffer.index"
      || string_of_mlpath p = "LowStar.UninitializedBuffer.uindex" ->
      EBufRead (translate_expr env e1, translate_expr env e2)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e ])
    when string_of_mlpath p = "FStar.HyperStack.ST.op_Bang" ->
      EBufRead (translate_expr env e, EConstant (UInt32, "0"))

  (* All the distinguished combinators that correspond to allocation, either on
   * the stack, on the heap (GC'd or manually-managed). *)
  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) } , [ e1; e2 ])
    when (string_of_mlpath p = "FStar.Buffer.create" ||
          string_of_mlpath p = "LowStar.Monotonic.Buffer.malloca" ||
          string_of_mlpath p = "LowStar.ImmutableBuffer.ialloca") ->
      EBufCreate (Stack, translate_expr env e1, translate_expr env e2)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) } , [ elen ])
    when string_of_mlpath p = "LowStar.UninitializedBuffer.ualloca" ->
      EBufCreateNoInit (Stack, translate_expr env elen)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) } , [ init ])
    when (string_of_mlpath p = "FStar.HyperStack.ST.salloc") ->
      EBufCreate (Stack, translate_expr env init, EConstant (UInt32, "1"))

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e2 ])
    when (string_of_mlpath p = "FStar.Buffer.createL" ||
          string_of_mlpath p = "LowStar.Monotonic.Buffer.malloca_of_list" ||
          string_of_mlpath p = "LowStar.ImmutableBuffer.ialloca_of_list") ->
      EBufCreateL (Stack, List.map (translate_expr env) (list_elements e2))

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ _erid; e2 ])
    when string_of_mlpath p = "LowStar.Monotonic.Buffer.mgcmalloc_of_list" ||
         string_of_mlpath p = "LowStar.ImmutableBuffer.igcmalloc_of_list" ->
      EBufCreateL (Eternal, List.map (translate_expr env) (list_elements e2))

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) } , [ _rid; init ])
    when (string_of_mlpath p = "FStar.HyperStack.ST.ralloc") ->
      EBufCreate (Eternal, translate_expr env init, EConstant (UInt32, "1"))

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ _e0; e1; e2 ])
    when (string_of_mlpath p = "FStar.Buffer.rcreate" || string_of_mlpath p = "LowStar.Monotonic.Buffer.mgcmalloc" ||
          string_of_mlpath p = "LowStar.ImmutableBuffer.igcmalloc") ->
      EBufCreate (Eternal, translate_expr env e1, translate_expr env e2)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ _erid; elen ])
    when string_of_mlpath p = "LowStar.UninitializedBuffer.ugcmalloc" ->
      EBufCreateNoInit (Eternal, translate_expr env elen)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) } , [ _rid; init ])
    when (string_of_mlpath p = "FStar.HyperStack.ST.ralloc_mm") ->
      EBufCreate (ManuallyManaged, translate_expr env init, EConstant (UInt32, "1"))

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ _e0; e1; e2 ])
    when (string_of_mlpath p = "FStar.Buffer.rcreate_mm" ||
          string_of_mlpath p = "LowStar.Monotonic.Buffer.mmalloc" ||
          string_of_mlpath p = "LowStar.Monotonic.Buffer.mmalloc" ||
          string_of_mlpath p = "LowStar.ImmutableBuffer.imalloc") ->
      EBufCreate (ManuallyManaged, translate_expr env e1, translate_expr env e2)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ _erid; elen ])
    when string_of_mlpath p = "LowStar.UninitializedBuffer.umalloc" ->
      EBufCreateNoInit (ManuallyManaged, translate_expr env elen)

  (* Only manually-managed references and buffers can be freed. *)
  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e2 ]) when (string_of_mlpath p = "FStar.HyperStack.ST.rfree") ->
      EBufFree (translate_expr env e2)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e2 ]) when (string_of_mlpath p = "FStar.Buffer.rfree" || string_of_mlpath p = "LowStar.Monotonic.Buffer.free") ->
      EBufFree (translate_expr env e2)

  (* Generic buffer operations. *)
  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e1; e2; _e3 ]) when (string_of_mlpath p = "FStar.Buffer.sub") ->
      EBufSub (translate_expr env e1, translate_expr env e2)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e1; e2; _e3 ]) when string_of_mlpath p = "LowStar.Monotonic.Buffer.msub" ->
      EBufSub (translate_expr env e1, translate_expr env e2)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e1; e2 ]) when (string_of_mlpath p = "FStar.Buffer.join") ->
      (translate_expr env e1)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e1; e2 ]) when (string_of_mlpath p = "FStar.Buffer.offset") ->
      EBufSub (translate_expr env e1, translate_expr env e2)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e1; e2 ]) when string_of_mlpath p = "LowStar.Monotonic.Buffer.moffset" ->
      EBufSub (translate_expr env e1, translate_expr env e2)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e1; e2; e3 ])
    when string_of_mlpath p = "FStar.Buffer.upd" || string_of_mlpath p = "FStar.Buffer.op_Array_Assignment"
    || string_of_mlpath p = "LowStar.Monotonic.Buffer.upd'"
    || string_of_mlpath p = "LowStar.UninitializedBuffer.uupd" ->
      EBufWrite (translate_expr env e1, translate_expr env e2, translate_expr env e3)
  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e1; e2 ])
    when string_of_mlpath p = "FStar.HyperStack.ST.op_Colon_Equals" ->
      EBufWrite (translate_expr env e1, EConstant (UInt32, "0"), translate_expr env e2)
  | MLE_App ({ expr = MLE_Name p }, [ _ ]) when (string_of_mlpath p = "FStar.HyperStack.ST.push_frame") ->
      EPushFrame
  | MLE_App ({ expr = MLE_Name p }, [ _ ]) when (string_of_mlpath p = "FStar.HyperStack.ST.pop_frame") ->
      EPopFrame
  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e1; e2; e3; e4; e5 ]) when (
      string_of_mlpath p = "FStar.Buffer.blit" ||
      string_of_mlpath p = "LowStar.Monotonic.Buffer.blit" ||
      string_of_mlpath p = "LowStar.UninitializedBuffer.ublit"
    ) ->
      EBufBlit (translate_expr env e1, translate_expr env e2, translate_expr env e3, translate_expr env e4, translate_expr env e5)
  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e1; e2; e3 ])
    when (let s = string_of_mlpath p in (s = "FStar.Buffer.fill" || s = "LowStar.Monotonic.Buffer.fill" )) ->
      EBufFill (translate_expr env e1, translate_expr env e2, translate_expr env e3)
  | MLE_App ({ expr = MLE_Name p }, [ _ ]) when string_of_mlpath p = "FStar.HyperStack.ST.get" ->
      // We need to reveal to Kremlin that FStar.HST.get is equivalent to
      // (void*)0 so that it can get rid of ghost calls to HST.get at the
      // beginning of functions, which is needed to enforce the push/pop
      // structure.
      EUnit

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ _ebuf; _eseq ])
    when (string_of_mlpath p = "LowStar.Monotonic.Buffer.witness_p" ||
          string_of_mlpath p = "LowStar.Monotonic.Buffer.recall_p" ||
          string_of_mlpath p = "LowStar.ImmutableBuffer.witness_contents" ||
          string_of_mlpath p = "LowStar.ImmutableBuffer.recall_contents") ->
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

  | MLE_App ({ expr = MLE_Name ([ "C" ], "string_of_literal") }, [ { expr = e } ])
  | MLE_App ({ expr = MLE_Name ([ "C"; "Compat"; "String" ], "of_literal") }, [ { expr = e } ])
  | MLE_App ({ expr = MLE_Name ([ "C"; "String" ], "of_literal") }, [ { expr = e } ]) ->
      begin match e with
      | MLE_Const (MLC_String s) ->
          EString s
      | _ ->
          failwith "Cannot extract string_of_literal applied to a non-literal"
      end

  | MLE_App ({ expr = MLE_Name ([ "LowStar"; "Literal" ], "buffer_of_literal") }, [ { expr = e } ]) ->
      begin match e with
      | MLE_Const (MLC_String s) ->
          ECast (EString s, TBuf (TInt UInt8))
      | _ ->
          failwith "Cannot extract buffer_of_literal applied to a non-literal"
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

  | MLE_App (head, args) ->
      EApp (translate_expr env head, List.map (translate_expr env) args)

  | MLE_TApp (head, ty_args) ->
      ETypApp (translate_expr env head, List.map (translate_type env) ty_args)

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
      EFun (binders, translate_expr env body, translate_type env body.mlty)

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
  | _ -> failwith (BU.format1 "invalid argument: expected MLTY_Named, got %s"
                             (ML.Code.string_of_mlty ([], "") t))

and translate_branches env branches =
  List.map (translate_branch env) branches

and translate_branch env (pat, guard, expr) =
  if guard = None then
    let env, pat = translate_pat env pat in
    pat, translate_expr env expr
  else
    failwith "todo: translate_branch"

and translate_width = function
  | None -> CInt
  | Some (FC.Signed, FC.Int8) -> Int8
  | Some (FC.Signed, FC.Int16) -> Int16
  | Some (FC.Signed, FC.Int32) -> Int32
  | Some (FC.Signed, FC.Int64) -> Int64
  | Some (FC.Unsigned, FC.Int8) -> UInt8
  | Some (FC.Unsigned, FC.Int16) -> UInt16
  | Some (FC.Unsigned, FC.Int32) -> UInt32
  | Some (FC.Unsigned, FC.Int64) -> UInt64

and translate_pat env p =
  match p with
  | MLP_Const MLC_Unit ->
      env, PUnit
  | MLP_Const (MLC_Bool b) ->
      env, PBool b
  | MLP_Const (MLC_Int (s, sw)) ->
      env, PConstant (translate_width sw, s)
  | MLP_Var name ->
      let env = extend env name in
      env, PVar ({ name = name; typ = TAny; mut = false })
  | MLP_Wild ->
      let env = extend env "_" in
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
  | MLC_String s ->
      if FStar.String.list_of_string s
      |> BU.for_some (fun (c:Char.char) -> c = Char.char_of_int 0)
      then failwith (BU.format1 "Refusing to translate a string literal that contains a null character: %s" s);
      EString s
  | MLC_Char c ->
      let i = BU.int_of_char c in
      let s = BU.string_of_int i in
      let c = EConstant (UInt32, s) in
      let char_of_int = EQualified (["FStar"; "Char"], "char_of_int") in
      EApp(char_of_int, [c])
  | MLC_Int (s, Some _) ->
      failwith "impossible: machine integer not desugared to a function call"
  | MLC_Float _ ->
      failwith "todo: translate_expr [MLC_Float]"
  | MLC_Bytes _ ->
      failwith "todo: translate_expr [MLC_Bytes]"
  | MLC_Int (s, None) ->
      EConstant (CInt, s)

(* Helper functions **********************************************************)

and mk_op_app env w op args =
  EApp (EOp (op, w), List.map (translate_expr env) args)
