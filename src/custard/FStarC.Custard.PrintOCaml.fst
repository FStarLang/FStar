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

module BU   = FStarC.Util
module SMap = FStarC.SMap

(* Symbols with no F* definition are references to a hand-written OCaml
   realization, so they are printed as that realization wherever they occur
   rather than bound to a local alias first.  The table is filled in by
   {!print_program}; threading it through every printing function instead
   would be noise, since it is constant for a whole program. *)
let externals : ref (SMap.t string) = mk_ref (SMap.create 0)

let external_target (n:name) : ML (option string) =
  SMap.try_find !externals (string_of_name n)

(* Names belonging to a linked unit (section 12), by the OCaml module that
   unit compiled to.  Every reference to one is qualified explicitly rather
   than brought into scope with [open]: two sibling units may each have
   re-specialized the same upstream definition -- which section 12.6 expects
   -- and an [open] would make the clash silent and the choice positional.
   Explicit qualification cannot be ambiguous. *)
let qualifiers : ref (SMap.t string) = mk_ref (SMap.create 0)

(* The types of a realized module, and their constructors (section 8.2).  A
   reference to one of these prints as the *realization's* own name -- [sys],
   not [fStarC_Platform_Base_sys] -- qualified by the support module, which
   {!qualifiers} already carries.  Nothing else about them is special: a field
   of a realized record is qualified by exactly the same mechanism as a field
   of an imported one. *)
let realized : ref (SMap.t unit) = mk_ref (SMap.create 0)

let is_realized (n:name) : ML bool =
  None? n.spec && Some? (SMap.try_find !realized (string_of_name n))

(* [FStar.Pervasives.Native.tupleN] is realized as OCaml's own N-tuple, which
   has no constructor to name and no field to project.  The *type* needs no
   help -- [('a, 'b) FStar_Pervasives_Native.tuple2] is an alias for ['a * 'b],
   so the realized spelling above is already right -- but building one,
   matching one and reading a component out of one each have to be written in
   OCaml's tuple syntax.  This table gives the arity, under both the type's
   name and its constructor's. *)
let tuples : ref (SMap.t int) = mk_ref (SMap.create 0)

let is_tuple_type (n:name) : ML bool =
  None? n.spec &&
  n.ns = ["FStar"; "Pervasives"; "Native"] &&
  FStarC.Util.starts_with n.id "tuple"

let tuple_arity (n:name) : ML (option int) =
  if Some? n.spec then None
  else SMap.try_find !tuples (string_of_name n)

(* A tuple component's field name is [_1], [_2], ...; its position is the
   number.  The name is the declaration's, before [ocaml_var] mangles it. *)
let tuple_index (f:string) : ML int =
  let s = if String.strlen f > 0 && String.substring f 0 1 = "_"
          then String.substring f 1 (String.strlen f - 1) else f in
  match FStarC.Util.safe_int_of_string s with Some i -> i | None -> 0

(* Place [fs] at the positions their field names give, filling the gaps with
   [dflt].  A pattern need not mention every component; a construction does,
   but writing it positionally rather than trusting the order costs nothing. *)
let by_position (k:int) (dflt:string) (fs : list (string & string)) : ML (list string) =
  let at (i:int) : ML string =
    match fs |> List.tryPick (fun (f, s) ->
                  if tuple_index f = i then Some s else None) with
    | Some s -> s
    | None -> dflt in
  let rec go (i:int) : ML (list string) =
    if i > k then [] else at i :: go (i + 1) in
  go 1

let qualifier (n:name) : ML (option string) =
  SMap.try_find !qualifiers (string_of_name n)

let qualify (n:name) (s:string) : ML string =
  match qualifier n with
  | Some m -> m ^ "." ^ s
  | None -> s

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
  (* Infix operators spelled as words.  They are reserved just as firmly as
     the rest -- `let mod = ...` does not parse -- and F\* code does use
     `mod` as a name. *)
  "asr"; "land"; "lor"; "lsl"; "lsr"; "lxor"; "mod";
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
  if is_realized n then sanitize n.id else
  let s = sanitize (mangled_name n) in
  let s = lowercase_first s in
  if List.existsb (fun k -> k = s) ocaml_keywords then s ^ "_" else s

let ocaml_ctor_name (n:name) (c:string) : ML string =
  uppercase_first (sanitize (mangled_name n ^ "_" ^ c))

let module_name_of_unit (u:string) : ML string = uppercase_first (sanitize u)

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
   would shadow the real one.  A monomorphized clone carries a [spec] suffix
   and is a genuinely new type, so it is declared and referred to like any
   other. *)
let builtin_type (n:name) : ML (option string) =
  match (if Some? n.spec then "" else String.concat "." (n.ns @ [n.id])) with
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
  match w with
  | Sizet -> "FStar_SizeT"
  | _ ->
    "FStar_" ^ int_module_stem s ^
    (match w with
     | Int8 -> "8" | Int16 -> "16" | Int32 -> "32" | Int64 -> "64"
     | Sizet -> "SizeT")

(* A width as [FStar.Int.Cast] spells it: [uint32], [int8]. *)
let int_cast_stem (sw : signedness & width) : ML string =
  let s, w = sw in
  (match s with Unsigned -> "uint" | Signed -> "int") ^
  (match w with
   | Int8 -> "8" | Int16 -> "16" | Int32 -> "32" | Int64 -> "64"
   | Sizet -> failwith "Custard: FStar.SizeT has no FStar.Int.Cast conversion")

(* The realization's injection from [Prims.int]: [uint_to_t] at an unsigned
   width, [int_to_t] at a signed one. *)
let int_inj (sw : signedness & width) : string =
  let sgn, _ = sw in
  int_module sw ^ (match sgn with Unsigned -> ".uint_to_t" | Signed -> ".int_to_t")

let rec ty (t:cty) : ML string =
  match t with
  | TUnit -> "unit"
  | TExn -> "exn"
  | TAny -> "Obj.t"
  | TVar x -> "'" ^ ocaml_var x
  | TInt sw -> int_module sw ^ ".t"
  | TArrow (t1, _, t2) -> "(" ^ ty t1 ^ " -> " ^ ty t2 ^ ")"
  | TTuple ts -> "(" ^ String.concat " * " (List.map ty ts) ^ ")"
  (* Section 8.4: a buffer is an OCaml array.  This is faithful for everything
     but [BufSub], which needs an interior pointer that OCaml has no way to
     express; that one is refused at run time rather than mistranslated. *)
  | TBuf t -> "(" ^ ty t ^ " array)"
  (* A reference points at one value, so it is an OCaml [ref] rather than a
     one-element array.  The buffer operations are shared with [TBuf], so the
     spelling of each one is chosen from the type of its pointer argument. *)
  | TRef t -> "(" ^ ty t ^ " ref)"
  | TApp (n, []) ->
    (match builtin_type n with
     | Some s -> s
     | None -> qualify n (ocaml_type_name n))
  | TApp (n, args) ->
    let hd = match builtin_type n with
             | Some s -> s
             | None -> qualify n (ocaml_type_name n) in
    "(" ^ String.concat ", " (List.map ty args) ^ ") " ^ hd

(* -------------------------------------------------------------------- *)
(* Constants                                                            *)
(* -------------------------------------------------------------------- *)

(* F\* strings are sequences of Unicode code points, and OCaml string literals
   are sequences of bytes, so a code point above 127 cannot be escaped
   numerically: `\821` is not a byte.  The ML extraction's answer, which this
   follows, is to escape only what has to be escaped and let everything else
   through verbatim -- [string_of_char] renders a code point as its UTF-8
   bytes, which is what the reader wanted in the first place. *)
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
      if i < 32 || i = 127 then "\\" ^ (if i < 10 then "00" else "0") ^ show i
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
    "(" ^ int_inj sw ^ " (Prims.parse_int \"" ^ s ^ "\"))"
  (* [FStar.Char.char] is realized as a plain OCaml [int] -- a code point, not
     OCaml's byte-sized [char] -- so the literal is the code point itself.
     That is what the ML extraction emits too, and it is what makes a char
     usable as a *pattern*: `FStar_Char.char_of_int 39` is neither a pattern
     nor even well-typed, since the realization takes a [Z.t]. *)
  | CChar c -> show (BU.int_of_char c)
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

(* OCaml has no integer pattern that means what the IR's [PConst (CInt _)]
   means: [Prims.int] is a [Z.t], whose literals are calls to
   [Prims.parse_int], and a machine integer literal is a call to
   [uint_to_t].  Neither is a pattern.  So an integer constant pattern is
   replaced by a fresh variable and an equality in the [when] clause, which
   is what the ML extraction does too (`Term.fst`, [Pat_constant] of a
   machine integer).  The C backend has real integer patterns and keeps the
   [PConst]. *)
let rec defer_ints (n:int) (p:pat) : (int & pat & list (string & FStarC.Custard.Syntax.constant)) =
  match p with
  | PConst c when (match c with CInt _ -> true | _ -> false) ->
    let x = "_iconst" ^ string_of_int n in
    (n + 1, PVar x, [(x, c)])
  | PCtor (nm, ps) -> let n, ps, eqs = defer_ints_list n ps in (n, PCtor (nm, ps), eqs)
  | PRecord (nm, fs) -> let n, fs, eqs = defer_ints_fields n fs in (n, PRecord (nm, fs), eqs)
  | PTuple ps -> let n, ps, eqs = defer_ints_list n ps in (n, PTuple ps, eqs)
  (* A disjunction has to bind the same variables in every alternative, so
     there is nothing sensible to lift out of one. *)
  | _ -> (n, p, [])

and defer_ints_fields (n:int) (fs:list (string & pat))
  : (int & list (string & pat) & list (string & FStarC.Custard.Syntax.constant)) =
  match fs with
  | [] -> (n, [], [])
  | (f, p) :: fs ->
    let n, p, eqs = defer_ints n p in
    let n, fs, eqs' = defer_ints_fields n fs in
    (n, (f, p) :: fs, eqs @ eqs')

and defer_ints_list (n:int) (ps:list pat) : (int & list pat & list (string & FStarC.Custard.Syntax.constant)) =
  match ps with
  | [] -> (n, [], [])
  | p :: ps ->
    let n, p, eqs = defer_ints n p in
    let n, ps, eqs' = defer_ints_list n ps in
    (n, p :: ps, eqs @ eqs')

let rec pattern (p:pat) : ML string =
  match p with
  | PWild -> "_"
  | PVar x -> ocaml_var x
  | PConst c -> constant c
  | PCtor (n, []) -> ctor_ref n
  (* [::] is infix in OCaml, and it is the only builtin constructor that takes
     arguments, so this one case covers them all. *)
  | PCtor (n, [p1; p2]) when builtin_ctor n = Some "::" ->
    "(" ^ pattern p1 ^ " :: " ^ pattern p2 ^ ")"
  | PCtor (n, ps) when Some? (tuple_arity n) ->
    "(" ^ String.concat ", " (List.map pattern ps) ^ ")"
  | PCtor (n, ps) -> "(" ^ ctor_ref n ^ " (" ^ String.concat ", " (List.map pattern ps) ^ "))"
  | PRecord (n, fs) when Some? (tuple_arity n) ->
    let k = Some?.v (tuple_arity n) in
    "(" ^ String.concat ", "
            (by_position k "_" (fs |> List.map (fun (f, p) -> (f, pattern p)))) ^ ")"
  (* As with [ERecord], qualifying the first field is enough to resolve the
     type.  A record pattern need not be exhaustive, and OCaml would warn about
     the fields it leaves out, so it always ends in a [_]. *)
  | PRecord (n, fs) ->
    "{ " ^ String.concat "; " (List.mapi (fun i (f, p) ->
             (if i = 0 then qualify n (ocaml_var f) else ocaml_var f)
             ^ " = " ^ pattern p) fs) ^ (if Cons? fs then "; _ }" else "_ }")
  | PTuple ps -> "(" ^ String.concat ", " (List.map pattern ps) ^ ")"
  | POr ps -> "(" ^ String.concat " | " (List.map pattern ps) ^ ")"

(* A constructor name in the IR is the *constructor's* lid, so the OCaml name
   is derived from it directly -- except for the constructors of the types
   [builtin_type] maps to an OCaml type, which have to be OCaml's own. *)
and ctor_ref (n:name) : ML string =
  match builtin_ctor n with
  | Some c -> c
  | None ->
    if is_realized n then qualify n (uppercase_first (sanitize n.id))
    else qualify n (uppercase_first (sanitize (mangled_name n)))

and builtin_ctor (n:name) : ML (option string) =
  match (if Some? n.spec then "" else String.concat "." (n.ns @ [n.id])) with
  | "Prims.Nil" -> Some "[]"
  | "Prims.Cons" -> Some "::"
  | _ -> None

let rec term (ind:string) (e:expr) : ML string =
  match e.e with
  | EConst c -> constant c
  | EVar x -> ocaml_var x
  | EQual (n, _) ->
    (match external_target n with
     | Some t -> t
     | None -> ocaml_value_name n)
  | ECtor (n, []) -> ctor_ref n
  | ECtor (n, [a; b]) when builtin_ctor n = Some "::" ->
    "(" ^ term ind a ^ " :: " ^ term ind b ^ ")"
  | ECtor (n, args) when Some? (tuple_arity n) ->
    "(" ^ String.concat ", " (List.map (term ind) args) ^ ")"
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
  | ERecord (n, fs) when Some? (tuple_arity n) ->
    let k = Some?.v (tuple_arity n) in
    "(" ^ String.concat ", "
            (by_position k "(Obj.magic ())"
               (fs |> List.map (fun (f, e) -> (f, term ind e)))) ^ ")"
  | ERecord (n, fs) ->
    (* Qualifying the first field is enough for OCaml to resolve the record
       type; qualifying every one would be noise. *)
    "{ " ^ String.concat "; " (List.mapi (fun i (f, e) ->
              (if i = 0 then qualify n (ocaml_var f) else ocaml_var f)
              ^ " = " ^ term ind e) fs) ^ " }"
  (* A tuple has no projection in OCaml beyond [fst] and [snd], so every
     component is read by a match that names it and ignores the rest. *)
  | EProj (e1, n, f) when Some? (tuple_arity n) ->
    let k = Some?.v (tuple_arity n) in
    "(match " ^ term ind e1 ^ " with (" ^
    String.concat ", " (by_position k "_" [(f, "custard_tup")]) ^ ") -> custard_tup)"
  | EProj (e1, n, f) -> "(" ^ term ind e1 ^ ")." ^ qualify n (ocaml_var f)
  (* A tuple type has one constructor, so the test is vacuous. *)
  | EDiscrim (_, n) when Some? (tuple_arity n) -> "true"
  | EDiscrim (e1, n) ->
    "(match " ^ term ind e1 ^ " with " ^ ctor_ref n ^ " _ -> true | _ -> false)"
  (* Every machine width is a *distinct* OCaml type -- [Stdint.UintN.t], plain
     [int] for [FStar.UInt8], a boxed [Sz of UInt64.t] for [FStar.SizeT] -- so
     an [Obj.magic] between two of them is a miscompilation, not a no-op.  C
     gets a coercion between integer types for free; OCaml needs a conversion,
     and a narrowing one needs the masking that the C cast does implicitly.
     Both are exactly what [FStar.Int.Cast] specifies, so between two machine
     widths that is what we call.  [FStar.SizeT] is not in that module, but its
     conversions are exact by their own preconditions, so they can go through
     [Prims.int] the way the realization itself does. *)
  | ECast (e1, t) ->
    (match e1.ty, t with
     | TInt sw1, TInt sw2 when sw1 = sw2 -> term ind e1
     | TInt sw1, TInt sw2 when snd sw1 <> Sizet && snd sw2 <> Sizet ->
       "(FStar_Int_Cast." ^ int_cast_stem sw1 ^ "_to_" ^ int_cast_stem sw2 ^
       " " ^ term ind e1 ^ ")"
     | TInt sw1, TInt sw2 ->
       "(" ^ int_inj sw2 ^ " (" ^ int_module sw1 ^ ".v " ^ term ind e1 ^ "))"
     | TInt sw1, _ -> "(Obj.magic (" ^ int_module sw1 ^ ".v " ^ term ind e1 ^ "))"
     | _, TInt sw2 -> "(" ^ int_inj sw2 ^ " (Obj.magic (" ^ term ind e1 ^ ")))"
     | _ -> "(Obj.magic (" ^ term ind e1 ^ "))")
  (* An OCaml array is indexed by [int], the IR by a machine integer. *)
  | EOp ({ po_op = BufCreate _ }, [init; len]) ->
    if TRef? e.ty then "(ref " ^ term ind init ^ ")"
    else "(Array.make " ^ index ind len ^ " " ^ term ind init ^ ")"
  | EOp ({ po_op = BufRead }, [b; i]) ->
    if TRef? b.ty then "(!(" ^ term ind b ^ "))"
    else "(" ^ term ind b ^ ").(" ^ index ind i ^ ")"
  | EOp ({ po_op = BufWrite }, [b; i; v]) ->
    if TRef? b.ty then "((" ^ term ind b ^ ") := " ^ term ind v ^ ")"
    else "((" ^ term ind b ^ ").(" ^ index ind i ^ ") <- " ^ term ind v ^ ")"
  | EOp ({ po_op = BufFree }, [_]) -> "()"
  (* A [ref] has no null, and no room to invent one: the empty array that
     stands in for a null buffer has no [ref] counterpart.  Refused at run
     time, like [BufSub]. *)
  | EOp ({ po_op = BufNull }, []) ->
    if TRef? e.ty then "(failwith \"Custard: a null reference has no OCaml representation\")"
    else "[||]"
  | EOp ({ po_op = BufIsNull }, [b]) ->
    if TRef? b.ty then "(failwith \"Custard: a null reference has no OCaml representation\")"
    else "(Array.length (" ^ term ind b ^ ") = 0)"
  | EOp ({ po_op = BufBlit }, [src; si; dst; di; len]) ->
    "(Array.blit " ^ term ind src ^ " " ^ index ind si ^ " " ^
    term ind dst ^ " " ^ index ind di ^ " " ^ index ind len ^ ")"
  | EOp ({ po_op = BufSub }, _) ->
    "(failwith \"Custard: pointer arithmetic has no OCaml representation\")"
  (* Infix, not [((&&) a b)].  OCaml's [&&] and [||] are the [%sequand] and
     [%sequor] primitives, which the compiler does short-circuit even when
     they are written prefix and fully applied -- but nothing in the emitted
     file says so, and §6 pass 1 has already arranged the operands on the
     assumption that they are delayed.  Printing them infix makes the
     generated code mean what it is meant to mean on inspection.  The guard on
     [po_int] matters: at a width, [And]/[Or] are *bitwise*. *)
  | EOp ({ po_op = And; po_int = None }, [a; b]) ->
    "(" ^ term ind a ^ " && " ^ term ind b ^ ")"
  | EOp ({ po_op = Or; po_int = None }, [a; b]) ->
    "(" ^ term ind a ^ " || " ^ term ind b ^ ")"
  | EOp (op, args) ->
    "(" ^ op_name op ^ " " ^ String.concat " " (List.map (term ind) args) ^ ")"
  | EAny -> "(Obj.magic 0)"
  | EAbort s -> "(failwith \"" ^ escape s ^ "\")"
  | EWhile (c, body) ->
    "(while " ^ term ind c ^ " do " ^ term ind body ^ " done)"
  | ERaise e1 -> "(raise " ^ term ind e1 ^ ")"
  | ETry (e1, brs) ->
    let ind' = ind ^ "  " in
    "(try " ^ term ind e1 ^ " with\n" ^
    String.concat "" (List.map (case ind') brs) ^ ind ^ ")"

(* An array index: the IR value is a machine integer, whose OCaml realization
   is a [Stdint] value with a [v] projection into a [Z.t]. *)
and index (ind:string) (e:expr) : ML string =
  match e.e with
  (* A literal index is the common case, and going through [Z.t] to say [0]
     would drown the output. *)
  | EConst (CInt (s, _)) -> s
  | ECast (e1, _) -> index ind e1
  | _ ->
    (match e.ty with
     | TInt sw -> "(Z.to_int (" ^ int_module sw ^ ".v " ^ term ind e ^ "))"
     | _ -> "(Obj.magic (" ^ term ind e ^ "))")

and case (ind:string) (br:branch) : ML string =
  let p, g, b = br in
  let _, p, eqs = defer_ints 0 p in
  let conds = eqs |> List.map (fun (x, c) -> ocaml_var x ^ " = " ^ constant c) in
  let conds = match g with None -> conds | Some g -> conds @ [term ind g] in
  let guard = if conds = [] then "" else " when " ^ String.concat " && " conds in
  ind ^ "| " ^ pattern p ^ guard ^ " -> " ^ term (ind ^ "  ") b ^ "\n"

(* -------------------------------------------------------------------- *)
(* Declarations                                                         *)
(* -------------------------------------------------------------------- *)

let params (ps : list string) : ML string =
  match ps with
  | [] -> ""
  | [p] -> "'" ^ ocaml_var p ^ " "
  | _ -> "(" ^ String.concat ", " (List.map (fun p -> "'" ^ ocaml_var p) ps) ^ ") "

let print_decl (first:bool) (d:decl) : ML (option string) =
  match d with
  | DType t ->
    if is_builtin_type t.dt_name || has_flag t.dt_flags Realized then None
    else
      let hd = (if first then "type " else "and ") ^
               params t.dt_params ^ ocaml_type_name t.dt_name in
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

  (* An external is printed at each of its uses; see {!externals}. *)
  | DExternal _ -> None

  | DExn e ->
    Some ("exception " ^ uppercase_first (sanitize (mangled_name e.de_name)) ^
          (match e.de_args with
           | [] -> ""
           | args -> " of " ^ String.concat " * " (List.map ty args)))

  | DLet l ->
    (* Every binder and the result carry their type.  Custard knows all of
       them exactly, and writing them down turns a mistake in the extraction
       into an OCaml type error here rather than a puzzle at the use site. *)
    let bs = String.concat "" (List.map (fun b ->
               " (" ^ ocaml_var b.b_name ^ " : " ^ ty b.b_ty ^ ")") l.dl_binders) in
    let rc = if l.dl_flags |> List.existsb Rec? then "rec " else "" in
    let kw = if first then "let " ^ rc else "and " in
    Some (kw ^ ocaml_value_name l.dl_name ^ bs ^ " : " ^ ty l.dl_ret ^
          " =\n  " ^ term "  " l.dl_body)

(* Constructor names have to be declared with the same OCaml name we refer to
   them by, so the variant's constructor labels are the constructors' own
   mangled names. *)
let print_program (p:program) : ML string =
  let tbl = SMap.create 50 in
  let quals = SMap.create 50 in
  let real = SMap.create 20 in
  let tups = SMap.create 20 in
  p |> List.iter (fun d ->
    (* An imported value is exactly an external whose target happens to be
       another generated module: nothing else about it is special, and reusing
       the mechanism means no printing path has to learn about linking. *)
    match imported_unit d with
    | Some u ->
      let m = module_name_of_unit u in
      (match d with
       | DLet l -> SMap.add tbl (string_of_name l.dl_name)
                     (m ^ "." ^ ocaml_value_name l.dl_name)
       | DExternal e ->
         (* An external the upstream unit did not compile either: it resolves
            to the same hand-written realization here, not to a symbol in the
            upstream module. *)
         SMap.add tbl (string_of_name e.dx_name)
           (match e.dx_target with Some t -> t | None -> realization_of e.dx_name)
       | DType t ->
         SMap.add quals (string_of_name t.dt_name) m;
         (match t.dt_body with
          | TVariant cs -> cs |> List.iter (fun (cn, _) ->
                             SMap.add quals (string_of_name cn) m)
          | _ -> ())
       | DExn _ -> ())
    | None ->
    match d with
    | DExternal e ->
      SMap.add tbl (string_of_name e.dx_name)
        (match e.dx_target with
         | Some t -> t
         | None -> realization_of e.dx_name)
    | _ -> ());
  (* A realized type resolves to its support module, which is the module its
     own namespace names.  This runs after the pass above so that a realized
     type reaching us through an imported unit still resolves to the
     realization: the upstream unit did not compile it either. *)
  p |> List.iter (fun d ->
    match d with
    | DType t when has_flag t.dt_flags Realized ->
      let m = String.concat "_" t.dt_name.ns in
      let mark (n:name) : ML unit =
        SMap.add real (string_of_name n) ();
        SMap.add quals (string_of_name n) m in
      mark t.dt_name;
      (match t.dt_body with
       | TVariant cs -> cs |> List.iter (fun (cn, _) -> mark cn)
       | _ -> ());
      (* [tupleN] is the one realized type whose OCaml form is syntax rather
         than a name; record its arity under every name it is reached by. *)
      if is_tuple_type t.dt_name then begin
        let arity (fs : list (string & cty)) : ML unit =
          SMap.add tups (string_of_name t.dt_name) (List.length fs) in
        match t.dt_body with
        | TRecord fs -> arity fs
        | TVariant [(cn, fs)] ->
          arity fs; SMap.add tups (string_of_name cn) (List.length fs)
        | _ -> ()
      end
    | _ -> ());
  externals := tbl;
  qualifiers := quals;
  realized := real;
  tuples := tups;
  let header =
    "(* Generated by F* Custard extraction. Do not edit. *)\n\
     [@@@ocaml.warning \"-3-5-8-11-20-26-27-28-32-33-34-35-37-39-50-57-60-69-70\"]\n" in
  (* [scc] has already made the members of a recursive group adjacent and
     tagged each of them with the group's members; all that is left is to join
     them with [and].  The flag is what identifies the group, not adjacency
     alone: two unrelated self-recursive definitions are also adjacent. *)
  let group_of (d:decl) : ML (option (list string)) =
    match decl_flags d |> List.tryFind Rec? with
    | Some (Rec ns) -> Some (List.map string_of_name ns)
    | _ -> None in
  let prev : ref (option (list string)) = mk_ref None in
  let ds = p |> List.collect (fun d ->
             (* An imported declaration is in the program only so that the two
                tables above could be built from it. *)
             if Some? (imported_unit d) then [] else
             let g = group_of d in
             let first = None? g || g <> !prev in
             match print_decl first d with
             | Some s -> prev := g; [s]
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
