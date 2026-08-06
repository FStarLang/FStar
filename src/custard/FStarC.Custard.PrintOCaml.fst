(*
   Copyright 2008-2026 Microsoft Research

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
module FStarC.Custard.PrintOCaml

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Class.Show
open FStarC.BaseTypes
open FStarC.Const
open FStarC.Custard.Syntax

module BU = FStarC.Util

(* -------------------------------------------------------------------- *)
(* Names                                                                *)
(* -------------------------------------------------------------------- *)

let ocaml_keywords = [
  "and"; "as"; "assert"; "begin"; "class"; "constraint"; "do"; "done";
  "downto"; "else"; "end"; "exception"; "external"; "false"; "for"; "fun";
  "function"; "functor"; "if"; "in"; "include"; "inherit"; "initializer";
  "lazy"; "let"; "match"; "method"; "module"; "mutable"; "new"; "nonrec";
  "object"; "of"; "open"; "or"; "private"; "rec"; "sig"; "struct"; "then";
  "to"; "true"; "try"; "type"; "val"; "virtual"; "when"; "while"; "with";
]

let is_alpha (i:int) : bool = (i >= 97 && i <= 122) || (i >= 65 && i <= 90)

let sanitize (s:string) : ML string =
  let ok (c:char) : ML bool =
    let i = BU.int_of_char c in
    is_alpha i || (i >= 48 && i <= 57) || i = 95 || i = 39
  in
  String.concat "" (List.map (fun c -> if ok c then BU.string_of_char c else "_")
                             (String.list_of_string s))

let lowercase_first (s:string) : ML string =
  if s = "" then "x"
  else
    let i = BU.int_of_char (List.hd (String.list_of_string s)) in
    let tl = String.substring s 1 (String.length s - 1) in
    if i >= 65 && i <= 90 then String.lowercase (String.substring s 0 1) ^ tl
    else if i >= 97 && i <= 122 then s
    (* An OCaml value name has to start with a lowercase letter. *)
    else "u_" ^ s

let uppercase_first (s:string) : ML string =
  if s = "" then "X"
  else
    let i = BU.int_of_char (List.hd (String.list_of_string s)) in
    let hd = String.uppercase (String.substring s 0 1) in
    let tl = String.substring s 1 (String.length s - 1) in
    if is_alpha i then hd ^ tl else "U" ^ s

let ocaml_value_name (n:name) : ML string =
  let s = sanitize (mangled_name n) in
  let s = lowercase_first s in
  if List.existsb (fun k -> k = s) ocaml_keywords then s ^ "_" else s

let ocaml_type_name (n:name) : ML string =
  let s = sanitize (mangled_name n) in
  let s = lowercase_first s in
  if List.existsb (fun k -> k = s) ocaml_keywords then s ^ "_" else s

let ocaml_ctor_name (n:name) (c:string) : ML string =
  uppercase_first (sanitize (mangled_name n ^ "_" ^ c))

let ocaml_var (x:string) : ML string =
  let s = lowercase_first (sanitize x) in
  if List.existsb (fun k -> k = s) ocaml_keywords then s ^ "_" else s

(* The path of the existing F* OCaml support module realizing a symbol that has
   no F* definition: FStar.IO.print_string is FStar_IO.print_string. *)
let realization_of (n:name) : ML string =
  match n.ns with
  | [] -> lowercase_first (sanitize n.id)
  | ns -> String.concat "_" ns ^ "." ^ lowercase_first (sanitize n.id)

(* Types with a built-in OCaml realization; emitting a declaration for these
   would shadow the real one. *)
let builtin_type (n:name) : ML (option string) =
  match String.concat "." (n.ns @ [n.id]) with
  | "Prims.unit" -> Some "unit"
  | "Prims.bool" -> Some "bool"
  | "Prims.string" -> Some "string"
  | "Prims.int" -> Some "Prims.int"
  | "Prims.exn" -> Some "exn"
  | "Prims.list" -> Some "list"
  | "FStar.Char.char" -> Some "FStar_Char.char"
  | _ -> None

let is_builtin_type (n:name) : ML bool = Some? (builtin_type n)

(* -------------------------------------------------------------------- *)
(* Types                                                                *)
(* -------------------------------------------------------------------- *)

let int_module_stem (s:signedness) : string =
  match s with Unsigned -> "UInt" | Signed -> "Int"

(* The OCaml realizations of machine integers live in the [FStar.UIntN]
   support modules, and every operator we emit has a same-named function
   there, so a machine type and a machine operation are both just a qualified
   name. *)
let int_module (sw : signedness & width) : string =
  let s, w = sw in
  "FStar_" ^ int_module_stem s ^
  (match w with
   | Int8 -> "8" | Int16 -> "16" | Int32 -> "32" | Int64 -> "64"
   | Sizet -> "SizeT")

let rec ty (t:cty) : ML string =
  match t with
  | TUnit -> "unit"
  | TAny -> "Obj.t"
  | TVar x -> "'" ^ ocaml_var x
  | TInt sw -> int_module sw ^ ".t"
  | TArrow (t1, _, t2) -> "(" ^ ty t1 ^ " -> " ^ ty t2 ^ ")"
  | TTuple ts -> "(" ^ String.concat " * " (List.map ty ts) ^ ")"
  | TApp (n, []) ->
    (match builtin_type n with
     | Some s -> s
     | None -> ocaml_type_name n)
  | TApp (n, args) ->
    let hd = match builtin_type n with Some s -> s | None -> ocaml_type_name n in
    "(" ^ String.concat ", " (List.map ty args) ^ ") " ^ hd

(* -------------------------------------------------------------------- *)
(* Constants                                                            *)
(* -------------------------------------------------------------------- *)

let escape (s:string) : ML string =
  let esc (c:char) : ML string =
    match c with
    | '\n' -> "\\n"
    | '\t' -> "\\t"
    | '\r' -> "\\r"
    | '"' -> "\\\""
    | '\\' -> "\\\\"
    | c ->
      let i = BU.int_of_char c in
      if i < 32 || i > 126 then "\\" ^ (if i < 10 then "00" else if i < 100 then "0" else "") ^ show i
      else BU.string_of_char c
  in
  String.concat "" (List.map esc (String.list_of_string s))

let constant (c:constant) : ML string =
  match c with
  | CUnit -> "()"
  | CBool b -> if b then "true" else "false"
  (* Prims.int is arbitrary precision in the OCaml runtime, exactly as in the
     ML extraction. *)
  | CInt (s, None) -> "(Prims.parse_int \"" ^ s ^ "\")"
  (* The realization's injection is [uint_to_t] for unsigned widths and
     [int_to_t] for signed ones. *)
  | CInt (s, Some sw) ->
    let sgn, _ = sw in
    let inj = match sgn with Unsigned -> "uint_to_t" | Signed -> "int_to_t" in
    "(" ^ int_module sw ^ "." ^ inj ^ " (Prims.parse_int \"" ^ s ^ "\"))"
  | CChar c -> "(FStar_Char.char_of_int (" ^ show (BU.int_of_char c) ^ "))"
  | CString s -> "\"" ^ escape s ^ "\""

(* -------------------------------------------------------------------- *)
(* Patterns and expressions                                             *)
(* -------------------------------------------------------------------- *)

(* Machine operators are the functions of the [FStar.UIntN] support module;
   the non-width-directed ones are OCaml's own. *)
let op_name (o:prim_op) : ML string =
  match o.po_int with
  | Some sw ->
    int_module sw ^ "." ^
    (match o.po_op with
     | Add -> "add" | AddW -> "add_mod" | Sub -> "sub" | SubW -> "sub_mod"
     | Mult -> "mul" | MultW -> "mul_mod" | Div -> "div" | DivW -> "div"
     | Mod -> "rem"
     | BOr -> "logor" | BAnd -> "logand" | BXor -> "logxor" | BNot -> "lognot"
     | BShiftL -> "shift_left" | BShiftR -> "shift_right"
     | Eq -> "eq" | Neq -> "ne" | Lt -> "lt" | Lte -> "lte"
     | Gt -> "gt" | Gte -> "gte"
     | And -> "logand" | Or -> "logor" | Not -> "lognot")
  | None ->
    (match o.po_op with
     | Add -> "Prims.op_Addition" | AddW -> "Prims.op_Addition"
     | Sub -> "Prims.op_Subtraction" | SubW -> "Prims.op_Subtraction"
     | Mult -> "Prims.op_Multiply" | MultW -> "Prims.op_Multiply"
     | Div -> "Prims.op_Division" | DivW -> "Prims.op_Division"
     | Mod -> "Prims.op_Modulus"
     | Eq -> "(=)" | Neq -> "(<>)" | Lt -> "(<)" | Lte -> "(<=)"
     | Gt -> "(>)" | Gte -> "(>=)"
     | And -> "(&&)" | Or -> "(||)" | Not -> "not"
     | BOr -> "(lor)" | BAnd -> "(land)" | BXor -> "(lxor)" | BNot -> "lnot"
     | BShiftL -> "(lsl)" | BShiftR -> "(lsr)")

let rec pattern (p:pat) : ML string =
  match p with
  | PWild -> "_"
  | PVar x -> ocaml_var x
  | PConst c -> constant c
  | PCtor (n, []) -> ctor_ref n
  | PCtor (n, ps) -> "(" ^ ctor_ref n ^ " (" ^ String.concat ", " (List.map pattern ps) ^ "))"
  | PTuple ps -> "(" ^ String.concat ", " (List.map pattern ps) ^ ")"
  | POr ps -> "(" ^ String.concat " | " (List.map pattern ps) ^ ")"

(* A constructor name in the IR is the *constructor's* lid, so the OCaml name
   is derived from it directly. *)
and ctor_ref (n:name) : ML string = uppercase_first (sanitize (mangled_name n))

let rec term (ind:string) (e:expr) : ML string =
  match e.e with
  | EConst c -> constant c
  | EVar x -> ocaml_var x
  | EQual (n, _) -> ocaml_value_name n
  | ECtor (n, []) -> ctor_ref n
  | ECtor (n, args) ->
    "(" ^ ctor_ref n ^ " (" ^ String.concat ", " (List.map (term ind) args) ^ "))"
  | ETuple es -> "(" ^ String.concat ", " (List.map (term ind) es) ^ ")"
  | EApp (hd, args) ->
    "(" ^ term ind hd ^ " " ^ String.concat " " (List.map (term ind) args) ^ ")"
  | EFun (bs, body) ->
    "(fun " ^ String.concat " " (List.map (fun b -> ocaml_var b.b_name) bs) ^
    " -> " ^ term ind body ^ ")"
  | ELet (x, _, e1, e2) ->
    let ind' = ind ^ "  " in
    "(let " ^ ocaml_var x ^ " = " ^ term ind' e1 ^ " in\n" ^ ind' ^ term ind' e2 ^ ")"
  | ESeq (e1, e2) ->
    (* [let _ = ...] rather than [;]: the discarded expression need not have
       type unit, and OCaml warns about that. *)
    "(let _ = " ^ term ind e1 ^ " in\n" ^ ind ^ term ind e2 ^ ")"
  | EIf (c, t, f) ->
    "(if " ^ term ind c ^ " then " ^ term ind t ^ " else " ^ term ind f ^ ")"
  | EMatch (scrut, brs) ->
    let ind' = ind ^ "  " in
    "(match " ^ term ind scrut ^ " with\n" ^
    String.concat "" (List.map (case ind') brs) ^ ind ^ ")"
  | ERecord (_, fs) ->
    "{ " ^ String.concat "; " (List.map (fun (f, e) ->
              ocaml_var f ^ " = " ^ term ind e) fs) ^ " }"
  | EProj (e1, _, f) -> "(" ^ term ind e1 ^ ")." ^ ocaml_var f
  | EDiscrim (e1, n) ->
    "(match " ^ term ind e1 ^ " with " ^ ctor_ref n ^ " _ -> true | _ -> false)"
  | ECast (e1, _) -> "(Obj.magic (" ^ term ind e1 ^ "))"
  | EOp (op, args) ->
    "(" ^ op_name op ^ " " ^ String.concat " " (List.map (term ind) args) ^ ")"
  | EWhile (c, body) ->
    "(while " ^ term ind c ^ " do " ^ term ind body ^ " done)"
  | ERaise (n, []) -> "(raise " ^ ctor_ref n ^ ")"
  | ERaise (n, args) ->
    "(raise (" ^ ctor_ref n ^ " (" ^ String.concat ", " (List.map (term ind) args) ^ ")))"
  | ETry (e1, brs) ->
    let ind' = ind ^ "  " in
    "(try " ^ term ind e1 ^ " with\n" ^
    String.concat "" (List.map (case ind') brs) ^ ind ^ ")"

and case (ind:string) (br:branch) : ML string =
  let p, g, b = br in
  let guard = match g with None -> "" | Some g -> " when " ^ term ind g in
  ind ^ "| " ^ pattern p ^ guard ^ " -> " ^ term (ind ^ "  ") b ^ "\n"

(* -------------------------------------------------------------------- *)
(* Declarations                                                         *)
(* -------------------------------------------------------------------- *)

let params (ps : list string) : ML string =
  match ps with
  | [] -> ""
  | [p] -> "'" ^ ocaml_var p ^ " "
  | _ -> "(" ^ String.concat ", " (List.map (fun p -> "'" ^ ocaml_var p) ps) ^ ") "

let decl (d:decl) : ML (option string) =
  match d with
  | DType t ->
    if is_builtin_type t.dt_name then None
    else
      let hd = "type " ^ params t.dt_params ^ ocaml_type_name t.dt_name in
      (match t.dt_body with
       | TAbstract -> Some (hd)
       | TAbbrev c -> Some (hd ^ " = " ^ ty c)
       | TRecord fs ->
         Some (hd ^ " = { " ^
               String.concat "; " (List.map (fun (f, c) ->
                 ocaml_var f ^ " : " ^ ty c) fs) ^ " }")
       | TVariant cs ->
         Some (hd ^ " =\n" ^
               String.concat "" (List.map (fun (c, fs) ->
                 "  | " ^ ctor_ref c ^
                 (match fs with
                  | [] -> ""
                  | _ -> " of " ^ String.concat " * " (List.map (fun (_, t) -> ty t) fs))
                 ^ "\n") cs)))

  | DExternal e ->
    (* No F* definition: bind to the hand-written OCaml realization. *)
    let target = match e.dx_target with
                 | Some t -> t
                 | None -> realization_of e.dx_name in
    Some ("let " ^ ocaml_value_name e.dx_name ^ " = " ^ target)

  | DExn e ->
    Some ("exception " ^ uppercase_first (sanitize (mangled_name e.de_name)) ^
          (match e.de_args with
           | [] -> ""
           | args -> " of " ^ String.concat " * " (List.map ty args)))

  | DLet l ->
    let bs = match l.dl_binders with
             | [] -> ""
             | _ -> " " ^ String.concat " " (List.map (fun b -> ocaml_var b.b_name) l.dl_binders) in
    let rc = if l.dl_flags |> List.existsb Rec? then "rec " else "" in
    Some ("let " ^ rc ^ ocaml_value_name l.dl_name ^ bs ^ " =\n  " ^ term "  " l.dl_body)

(* Constructor names have to be declared with the same OCaml name we refer to
   them by, so the variant's constructor labels are the constructors' own
   mangled names. *)
let print_program (p:program) : ML string =
  let header =
    "(* Generated by F* Custard extraction. Do not edit. *)\n\
     [@@@ocaml.warning \"-3-5-8-11-20-26-27-28-32-33-34-35-37-39-50-57-60-69-70\"]\n" in
  let ds = p |> List.collect (fun d ->
             match decl d with
             | Some s -> [s]
             | None -> []) in
  (* Custard compiles standalone programs (section 4.4), so the entry points
     are called from the generated module itself. *)
  let calls = p |> List.collect (fun d ->
    match d with
    | DLet l when l.dl_flags |> List.existsb Entrypoint?
               && l.dl_binders |> List.for_all (fun b -> TUnit? b.b_ty) ->
      let args = String.concat " " (List.map (fun _ -> "()") l.dl_binders) in
      ["let _ = " ^ ocaml_value_name l.dl_name ^ " " ^ args]
    | _ -> []) in
  header ^ "\n" ^ String.concat "\n\n" (ds @ calls) ^ "\n"
