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

open FStar
open FStar.Util
open FStar.Extraction.ML
open FStar.Extraction.ML.Syntax
open FStar.Format
open FStar.Const
open FStar.BaseTypes

(* COPY-PASTED ****************************************************************)

type program =
  list<decl>

and decl =
  | DFunction of typ * ident * list<binder> * expr

and expr =
  | EBound of var
  | EOpen of binder
  | EQualified of lident
  | EConstant of constant
  | EUnit
  | EApp of expr * list<expr>
  | ELet of binder * expr * expr
  | EIfThenElse of expr * expr * expr
  | ESequence of list<expr>
  | EAssign of expr * expr
    (** left expression can only be a EBound of EOpen *)
  | EBufCreate of expr * expr
  | EBufRead of expr * expr
  | EBufWrite of expr * expr * expr
  | EBufSub of expr * expr * expr
  | EMatch of expr * branches
  | EOp of op

and op = | Add | Sub | Div | Mult | Mod

and branches =
  list<branch>

and branch =
  pattern * expr

and pattern =
  | PUnit

and constant =
  | CInt of string

and var =
  int (** a De Bruijn index *)

and binder = {
  name: ident;
  typ: typ;
  mut: bool;
}

and ident =
  string (** for pretty-printing *)

and lident =
  list<ident> * ident

and typ =
  | TInt32
  | TBuf of typ
  | TUnit

(** Versioned binary writing/reading of ASTs *)

type version = int
let current_version: version = 1

type file = string * program
type binary_format = version * list<file>


(* Utilities *****************************************************************)

let fst3 (x, _, _) = x
let snd3 (_, x, _) = x
let thd3 (_, _, x) = x

(* Environments **************************************************************)

type env = {
  names: list<name>;
}

and name = {
  pretty: string;
  mut: bool;
}

let empty = {
  names = []
}

let extend env x is_mut =
  { env with names = { pretty = x; mut = is_mut } :: env.names }

let find_name env x =
  match List.tryFind (fun name -> name.pretty = x) env.names with
  | Some name ->
      name
  | None ->
      failwith "internal error: name not found"

let is_mutable env x =
  (find_name env x).mut

let find env x =
  List.index (fun name -> name.pretty = x) env.names

(* Actual translation ********************************************************)

let rec translate (MLLib modules): list<file> =
  List.filter_map (fun m ->
    try
      Some (translate_module m)
    with
    | e ->
        Util.print2 "Unable to translate module: %s\n%s\n"
          (fst3 m) (Util.print_exn e);
        None
  ) modules

and translate_module (name, modul, _): file =
  let program = match modul with
    | Some (_signature, decls) ->
        List.filter_map (translate_decl empty) decls
    | _ ->
        failwith "Unexpected standalone interface or nested modules"
  in
  name, program

and translate_decl env d: option<decl> =
  match d with
  | MLM_Let (flavor, [ {
      mllb_name = name, _;
      mllb_tysc = Some ([], MLTY_Fun (_, _, t));
      mllb_def = { expr = MLE_Fun (args, body) }
    } ]) ->
      assert (flavor <> Mutable);
      let env = if flavor = Rec then extend env name false else env in
      let t = translate_type env t in
      let binders = translate_binders env args in
      let body = translate_expr env body in
      Some (DFunction (t, name, binders, body))

  | MLM_Let _ ->
      failwith "todo: translate_decl [MLM_Let]"

  | MLM_Loc _ ->
      None

  | MLM_Ty _ ->
      failwith "todo: translate_decl [MLM_Ty]"

  | MLM_Top _ ->
      failwith "todo: translate_decl [MLM_Top]"

  | MLM_Exn _ ->
      failwith "todo: translate_decl [MLM_Exn]"

and translate_type env t: typ =
  match t with
  | MLTY_Tuple []
  | MLTY_Top ->
      TUnit
  | MLTY_Var _ ->
      failwith "todo: translate_type [MLTY_Var]"
  | MLTY_Fun _ ->
      failwith "todo: translate_type [MLTY_Fun]"
  | MLTY_Named (_, p) ->
      begin match Syntax.string_of_mlpath p with
      | "Prims.unit" ->
          TUnit
      | "FStar.Int32.int32" ->
          TInt32
      | _ ->
          failwith (Util.format1 "todo: translate_type [MLTY_Named] %s" (Syntax.string_of_mlpath p))
      end
  | MLTY_Tuple _ ->
      failwith "todo: translate_type [MLTY_Tuple]"

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

  | MLE_Name _ ->
      failwith "todo: translate_expr [MLE_Name]"

  | MLE_Let ((flavor, [{
      mllb_name = name, _;
      mllb_tysc = Some ([], typ); // assuming unquantified type
      mllb_add_unit = add_unit; // ?
      mllb_def = body;
      print_typ = print // ?
    }]), continuation) ->
      let typ, body =
        if flavor = Mutable then
          (match typ with
          | MLTY_Named ([ t ], p) when (string_of_mlpath p = "FStar.ST.ref") -> t
          | _ -> failwith "unexpected: bad desugaring of Mutable"),
          (match body with
          | { expr = MLE_App (_, [ body ]) } -> body
          | _ -> failwith "unexpected: bad desugaring of Mutable")
        else
          typ, body
      in
      let is_mut = flavor = Mutable in
      let binder = { name = name; typ = translate_type env typ; mut = is_mut } in
      let body = translate_expr env body in
      let env = extend env name is_mut in
      let continuation = translate_expr env continuation in
      ELet (binder, body, continuation)

  | MLE_Match (expr, branches) ->
      EMatch (translate_expr env expr, translate_branches env branches)

  | MLE_App ({ expr = MLE_Name p }, [ { expr = MLE_Var (v, _) } ])
    when (string_of_mlpath p = "FStar.ST.read" && is_mutable env v) ->
      EBound (find env v)

  | MLE_App ({ expr = MLE_Name p }, [ { expr = MLE_Var (v, _) }; e ])
    when (string_of_mlpath p = "FStar.ST.write" && is_mutable env v) ->
      EAssign (EBound (find env v), translate_expr env e)

  | MLE_App ({ expr = MLE_Name p }, args)
    when (string_of_mlpath p = "FStar.Int32.op_Plus") ->
      EApp (EOp Add, List.map (translate_expr env) args)

  | MLE_App ({ expr = MLE_Name p }, _) ->
      failwith (Util.format1 "todo: translate_expr [MLE_App=%s]" (string_of_mlpath p))

  | MLE_Let _ ->
      (* Things not supported (yet): let-bindings for functions; meaning, rec flags are not
       * supported, and quantified type schemes are not supported either *)
      failwith "todo: translate_expr [MLE_Let]"
  | MLE_App _ ->
      failwith "todo: translate_expr [MLE_App]"
  | MLE_Fun _ ->
      failwith "todo: translate_expr [MLE_Fun]"
  | MLE_Coerce _ ->
      failwith "todo: translate_expr [MLE_Coerce]"
  | MLE_CTor _ ->
      failwith "todo: translate_expr [MLE_CTor]"
  | MLE_Seq seqs ->
      ESequence (List.map (translate_expr env) seqs)
  | MLE_Tuple _ ->
      failwith "todo: translate_expr [MLE_Tuple]"
  | MLE_Record _ ->
      failwith "todo: translate_expr [MLE_Record]"
  | MLE_Proj _ ->
      failwith "todo: translate_expr [MLE_Proj]"
  | MLE_If _ ->
      failwith "todo: translate_expr [MLE_If]"
  | MLE_Raise _ ->
      failwith "todo: translate_expr [MLE_Raise]"
  | MLE_Try _ ->
      failwith "todo: translate_expr [MLE_Try]"

and translate_branches env branches =
  List.map (translate_branch env) branches

and translate_branch env (pat, guard, expr) =
  if guard = None then
    translate_pat env pat, translate_expr env expr
  else
    failwith "todo: translate_branch"

and translate_pat env p: pattern =
  match p with
  | MLP_Const MLC_Unit ->
      PUnit
  | MLP_Wild ->
      failwith "todo: translate_pat [MLP_Wild]"
  | MLP_Const _ ->
      failwith "todo: translate_pat [MLP_Const]"
  | MLP_Var _ ->
      failwith "todo: translate_pat [MLP_Var]"
  | MLP_CTor _ ->
      failwith "todo: translate_pat [MLP_CTor]"
  | MLP_Branch _ ->
      failwith "todo: translate_pat [MLP_Branch]"
  | MLP_Record _ ->
      failwith "todo: translate_pat [MLP_Record]"
  | MLP_Tuple _ ->
      failwith "todo: translate_pat [MLP_Tuple]"

and translate_constant c: expr =
  match c with
  | MLC_Unit ->
      EUnit
  | MLC_Bool _ ->
      failwith "todo: translate_expr [MLC_Bool]"
  | MLC_Int (s, _) ->
      EConstant (CInt s)
  | MLC_Float _ ->
      failwith "todo: translate_expr [MLC_Float]"
  | MLC_Char _ ->
      failwith "todo: translate_expr [MLC_Char]"
  | MLC_String _ ->
      failwith "todo: translate_expr [MLC_String]"
  | MLC_Bytes _ ->
      failwith "todo: translate_expr [MLC_Bytes]"
