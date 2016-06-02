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

let rec translate (MLLib modules): list<file> =
  List.map translate_module modules

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

  | _ ->
      None

and translate_type t: typ =
  match t with
  | MLTY_Tuple []
  | MLTY_Top ->
      TUnit
  | _ ->
      failwith "todo: translate_type"

and translate_binders args =
  List.map translate_binder args

and translate_binder ((name, _), typ) =
  { name = name; typ = translate_type typ; mut = false }

and translate_expr e: expr =
  match e.expr with
  | MLE_Tuple [] ->
      EUnit
  | _ ->
      failwith "todo: translate_expr"
