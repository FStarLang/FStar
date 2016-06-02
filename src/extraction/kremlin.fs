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

(** COPY-PASTED... *)

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
  | ESequence of expr * expr
  | EAssign of expr * expr
    (** left expression can only be a EBound of EOpen *)
  | EBufCreate of expr * expr
  | EBufRead of expr * expr
  | EBufWrite of expr * expr * expr
  | EBufSub of expr * expr * expr

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

(** END COPY-PASTED... *)

let fst3 (x, _, _) = x
let snd3 (_, x, _) = x
let thd3 (_, _, x) = x

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
        List.filter_map translate_decl decls
    | _ ->
        failwith "Unexpected standalone interface or nested modules"
  in
  name, program

and translate_decl d: option<decl> =
  match d with
  | MLM_Let (is_rec, [ {
      mllb_name = name, _;
      mllb_tysc = Some ([], MLTY_Fun (_, _, t));
      mllb_def = { expr = MLE_Fun (args, body) }
    } ]) ->
      let t = translate_type t in
      let binders = translate_binders args in
      let body = translate_expr body in
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

and translate_type t: typ =
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
      | _ ->
          failwith (Util.format1 "todo: translate_type [MLTY_Named] %s" (Syntax.string_of_mlpath p))
      end
  | MLTY_Tuple _ ->
      failwith "todo: translate_type [MLTY_Tuple]"

and translate_binders args =
  List.map translate_binder args

and translate_binder ((name, _), typ) =
  { name = name; typ = translate_type typ; mut = false }

and translate_expr e: expr =
  match e.expr with
  | MLE_Tuple [] ->
      EUnit
  | MLE_Const c ->
      translate_constant c
  | MLE_Var _ ->
      failwith "todo: translate_expr [MLE_Var]"
  | MLE_Name _ ->
      failwith "todo: translate_expr [MLE_Name]"
  | MLE_Let _ ->
      failwith "todo: translate_expr [MLE_Let]"
  | MLE_App _ ->
      failwith "todo: translate_expr [MLE_App]"
  | MLE_Fun _ ->
      failwith "todo: translate_expr [MLE_Fun]"
  | MLE_Match _ ->
      failwith "todo: translate_expr [MLE_Match]"
  | MLE_Coerce _ ->
      failwith "todo: translate_expr [MLE_Coerce]"
  | MLE_CTor _ ->
      failwith "todo: translate_expr [MLE_CTor]"
  | MLE_Seq _ ->
      failwith "todo: translate_expr [MLE_Seq]"
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

and translate_constant c: expr =
  match c with
  | MLC_Unit ->
      EUnit
  | MLC_Bool _ ->
      failwith "todo: translate_expr [MLC_Bool]"
  | MLC_Int _ ->
      failwith "todo: translate_expr [MLC_Int]"
  | MLC_Float _ ->
      failwith "todo: translate_expr [MLC_Float]"
  | MLC_Char _ ->
      failwith "todo: translate_expr [MLC_Char]"
  | MLC_String _ ->
      failwith "todo: translate_expr [MLC_String]"
  | MLC_Bytes _ ->
      failwith "todo: translate_expr [MLC_Bytes]"
