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
module Prof = FStarC.Custard.Prof

(* Section 12.9: the file currently being printed, when the output is split.
   A reference to a name of *this* file must not be qualified, and everything
   in {!qualifiers} is qualified by construction, so the two are reconciled
   here rather than by keeping a second table per file. *)
let current_module : ref (option string) = mk_ref None

(* Symbols with no F* definition are references to a hand-written OCaml
   realization, so they are printed as that realization wherever they occur
   rather than bound to a local alias first.  The table is filled in by
   {!print_program}; threading it through every printing function instead
   would be noise, since it is constant for a whole program. *)
let externals : ref (SMap.t string) = mk_ref (SMap.create 0)

(* A realization's path is absolute -- [FStarC_Syntax_Syntax.subst_elt] -- and
   that is what a reference to it has to print everywhere except in the file
   that *is* [FStarC_Syntax_Syntax], where OCaml has no way to name the module
   being defined.  The case arises for ulib's [FStar.Stubs.*] restatements of
   the compiler's API (section 8.3): a stub value is realized by the
   compiler's own definition, and Custard compiles that definition into the
   very file the stub's qualified name points at. *)
let unqualify_self (t:string) : ML string =
  match !current_module with
  | None -> t
  | Some m ->
    let p = m ^ "." in
    let lp = String.strlen p in
    if String.strlen t > lp && String.substring t 0 lp = p
    then String.substring t lp (String.strlen t - lp)
    else t

let external_target (n:name) : ML (option string) =
  match SMap.try_find !externals (string_of_name n) with
  | Some t -> Some (unqualify_self t)
  | None -> None

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

(* Section 12.9: the names emitted under their plain F* identifier rather than
   their mangled one.  Mangling exists only to keep one flat file
   collision-free (section 12.7); once a declaration is in the file its own
   module names, and is the only declaration from its source lid, the module
   already separates it and the plain name is both shorter and -- this is the
   point -- the name the hand-written realizations refer to it by. *)
let at_home : ref (SMap.t unit) = mk_ref (SMap.create 0)

let is_at_home (n:name) : ML bool =
  None? n.spec && Some? (SMap.try_find !at_home (string_of_name n))

(* [FStar.Pervasives.Native.tupleN] is realized as OCaml's own N-tuple, which
   has no constructor to name and no field to project.  The *type* needs no
   help -- [('a, 'b) FStar_Pervasives_Native.tuple2] is an alias for ['a * 'b],
   so the realized spelling above is already right -- but building one,
   matching one and reading a component out of one each have to be written in
   OCaml's tuple syntax.  This table gives the arity, under both the type's
   name and its constructor's. *)
let tuples : ref (SMap.t int) = mk_ref (SMap.create 0)

(* How many type parameters each record type takes.  OCaml resolves a record
   expression's type from its labels, and when two record types in the same
   module share their label names -- [namedv_view] and [binding] in
   [FStarC.Reflection.V2.Data] both have [uniq], [sort], [ppname] -- it picks
   the one declared last, silently, unless the expression's type is already
   known.  Qualifying a label names the module, not the type, so it does not
   help.  An ascription does, and it needs the parameter count to write
   [(_, _) t]. *)
let record_params : ref (SMap.t int) = mk_ref (SMap.create 0)

(* Which labels are actually contested: keyed by the label qualified with its
   module, the number of record types in that module that declare it.  Only
   those need the ascription, and leaving it off everywhere else keeps the
   generated code readable.  Specializations count as separate types, so
   [both__int] and [both__bool] do make [fst] ambiguous. *)
let record_labels : ref (SMap.t int) = mk_ref (SMap.create 0)

let label_key (n:name) (f:string) : string =
  String.concat "." n.ns ^ "|" ^ f

let ambiguous_label (n:name) (f:string) : ML bool =
  match SMap.try_find !record_labels (label_key n f) with
  | Some k -> k > 1
  | None -> false

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
  match SMap.try_find !qualifiers (string_of_name n) with
  | Some m -> if Some m = !current_module then None else Some m
  | None -> None

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

let escape_keyword (s:string) : ML string =
  if List.existsb (fun k -> k = s) ocaml_keywords then s ^ "_" else s

let ocaml_value_name (n:name) : ML string =
  if is_at_home n then escape_keyword (lowercase_first (sanitize n.id)) else
  escape_keyword (lowercase_first (sanitize (mangled_name n)))

let ocaml_type_name (n:name) : ML string =
  if is_realized n then sanitize n.id else
  if is_at_home n then escape_keyword (lowercase_first (sanitize n.id)) else
  escape_keyword (lowercase_first (sanitize (mangled_name n)))

(* The OCaml constructor a variant label or an exception is declared and
   referred to under.  Both spellings have to agree, so both go through here. *)
let ocaml_ctor_ident (n:name) : ML string =
  if is_realized n || is_at_home n then uppercase_first (sanitize n.id)
  else uppercase_first (sanitize (mangled_name n))

let ocaml_ctor_name (n:name) (c:string) : ML string =
  uppercase_first (sanitize (mangled_name n ^ "_" ^ c))

let module_name_of_unit (u:string) : ML string = uppercase_first (sanitize u)

let ocaml_var (x:string) : ML string =
  let s = lowercase_first (sanitize x) in
  if List.existsb (fun k -> k = s) ocaml_keywords then s ^ "_" else s

(* Section 30.13.  The names of the top-level values this run will emit, filled
   in by [build_tables] before anything is printed.

   A reference to a top-level value in the same file is printed unqualified,
   because inside [Foo] there is no way to say [Foo.bar].  So a *local* of the
   same name captures it, silently, and the generated OCaml either does not
   compile or -- worse -- compiles against the wrong binding.  F* has no such
   problem, which is why the collision arrives from a source that reads
   perfectly: [FStarC.Real.try_mk (mantissa exponent : int)] shadows the
   projections [mantissa] and [exponent] it then calls.

   Locals are renamed rather than references qualified, because the local is
   the one whose name carries no meaning outside the definition. *)
let reserved_top : ref (list string) = mk_ref []

(* Only value locals go through here, not record fields or type variables: a
   field's spelling has to match the type's declaration, which may be a
   hand-written realization this run does not get to rename. *)
let ocaml_local (x:string) : ML string =
  let s = ocaml_var x in
  if List.existsb (fun k -> k = s) !reserved_top then s ^ "_" else s

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
  (* An option is OCaml's own, for the same reason a list is: the
     realization defines it as an alias of the stdlib type, so naming the
     stdlib type is not a translation but the same thing said directly.  What
     it buys is that the generated code no longer needs the realization to
     say what an option *is* -- see {!ty}'s tuple case. *)
  | "FStar.Pervasives.Native.option" -> Some "option"
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
  (* [FStar.Pervasives.Native.tupleN] is OCaml's own N-tuple.  The realization
     says so -- [type ('a,'b) tuple2 = 'a * 'b] is an alias, not a definition
     -- so writing the tuple type directly is not a translation of it but the
     same type named without the detour.  It is also the only way to say it
     that does not require the realization to be linked, which is the point:
     the F* side of this module is ordinary code that both backends compile,
     and the hand-written file exists for the ML extraction's sake, not
     Custard's. *)
  | TApp (n, args) when is_tuple_type n && Cons? args ->
    "(" ^ String.concat " * " (List.map ty args) ^ ")"
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
     | Add -> "Prims.op_Plus" | AddW -> "Prims.op_Plus"
     | Sub -> "Prims.op_Minus" | SubW -> "Prims.op_Minus"
     | Mult -> "Prims.op_Star" | MultW -> "Prims.op_Star"
     | Div -> "Prims.op_Slash" | DivW -> "Prims.op_Slash"
     | Mod -> "Prims.op_Percent"
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
  | PVar x -> ocaml_local x
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
    qualify n (ocaml_ctor_ident n)

and builtin_ctor (n:name) : ML (option string) =
  match (if Some? n.spec then "" else String.concat "." (n.ns @ [n.id])) with
  | "Prims.Nil" -> Some "[]"
  | "Prims.Cons" -> Some "::"
  | "FStar.Pervasives.Native.None" -> Some "None"
  | "FStar.Pervasives.Native.Some" -> Some "Some"
  | _ -> None

(* Say which record type is meant.  OCaml resolves a label to the *last*
   record type declared with it, silently, so an expression built out of
   labels alone -- or a projection out of a value whose type is not otherwise
   known -- can be given the wrong type, and only fail somewhere else.  The
   ascription has to spell the type constructor's parameters, hence
   {!record_params}; they are all wildcards, since it is the type's identity
   that is in question and never its arguments. *)
let ascribe_record (n:name) (fs:list string) (s:string) : ML string =
  match SMap.try_find !record_params (string_of_name n) with
  | _ when not (fs |> List.existsb (ambiguous_label n)) -> s
  | None -> s
  | Some k ->
    let rec wilds (i:int) : ML (list string) =
      if i <= 0 then [] else "_" :: wilds (i - 1) in
    let args = if k = 0 then ""
               else if k = 1 then "_ "
               else "(" ^ String.concat ", " (wilds k) ^ ") " in
    "(" ^ s ^ " : " ^ args ^ qualify n (ocaml_type_name n) ^ ")"

(* Past this many columns a line stops being one a reader takes in at a
   glance, which is the only thing the layout here is for. *)
let line_width : int = 80

(* Whether a width conversion can change the mathematical value.  Signed to
   unsigned always can, because of the negatives; otherwise it is a question
   of range.  [FStar.SizeT] is 64 bits at every target F* supports. *)
let width_bits (w:width) : int =
  match w with
  | Int8 -> 8 | Int16 -> 16 | Int32 -> 32 | Int64 -> 64 | Sizet -> 64

let value_preserving (a b : signedness & width) : bool =
  let sa, wa = a in
  let sb, wb = b in
  match sa, sb with
  | Unsigned, Unsigned
  | Signed, Signed -> width_bits wa <= width_bits wb
  | Unsigned, Signed -> width_bits wa < width_bits wb
  | Signed, Unsigned -> false

let rec term (ind:string) (e:expr) : ML string =
  match e.e with
  | EConst c -> constant c
  | EVar x -> ocaml_local x
  | EQual (n, _) ->
    (match external_target n with
     | Some t -> t
     | None -> qualify n (ocaml_value_name n))
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
    "(fun " ^ String.concat " " (List.map (fun b -> ocaml_local b.b_name) bs) ^
    " -> " ^ term ind body ^ ")"
  (* A binding and a statement both open a *sequence*, which {!stmts} prints
     as one: at one column and inside one pair of parentheses, rather than
     nesting a pair and an indentation step per element. *)
  | ELet _ | ESeq _ -> "(" ^ stmts ind e ^ ")"
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
    (* Qualifying the first field names the *module*, which is enough to find
       the record type only when no other record in it shares these labels.
       When one does, OCaml takes the last declared, so say which is meant
       ({!record_params}). *)
    (* One field per line, unless the whole literal fits on the one it is
       already on: a record is where a reader looks up what a value is made
       of, and the fields of the ones this compiler builds are whole
       expressions rather than names -- but a two-field record of variables is
       not clearer for being spread over two lines. *)
    let ind' = ind ^ "  " in
    let parts = List.mapi (fun i (f, e) ->
                  (if i = 0 then qualify n (ocaml_var f) else ocaml_var f)
                  ^ " = " ^ term ind' e) fs in
    let one = "{ " ^ String.concat "; " parts ^ " }" in
    let body =
      if String.length ind + String.length one <= line_width
         && not (List.existsb (fun c -> c = '\n') (String.list_of_string one))
      then one
      else "{ " ^ String.concat (";\n" ^ ind') parts ^ " }" in
    ascribe_record n (List.map fst fs) body
  (* A tuple has no projection in OCaml beyond [fst] and [snd], so every
     component is read by a match that names it and ignores the rest. *)
  | EProj (e1, n, f) when Some? (tuple_arity n) ->
    let k = Some?.v (tuple_arity n) in
    "(match " ^ term ind e1 ^ " with (" ^
    String.concat ", " (by_position k "_" [(f, "custard_tup")]) ^ ") -> custard_tup)"
  (* Reading a field is ambiguous for exactly the reason writing one is, and
     the fix is the same.  It is *more* often ambiguous, in fact: a record
     expression at least names all of its labels, whereas [x.uniq] is one
     label, and the only other thing that could decide the type is what [x] is
     already known to be -- which, in a lambda Custard emits without binder
     annotations, is nothing at all.  It surfaced when
     [FStarC.Reflection.V2.Embeddings.e_namedv_view] stopped being specialized:
     its [embed] closure projects [uniq], [sort] and [ppname], which [binding]
     also has and declares later, so the closure was inferred at [binding] and
     the embedding no longer agreed with its own [unembed]. *)
  | EProj (e1, n, f) -> "(" ^ ascribe_record n [f] (term ind e1) ^ ")." ^ qualify n (ocaml_var f)
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
     [Prims.int] the way the realization itself does.

     A *coercion* is the opposite case: it must not change the representation
     at all, or the two directions would have to agree about which one is
     canonical -- and they cannot, because the same value also crosses the
     boundary inside a structure ([uint32 list] to [TAny]), where no
     per-element conversion is possible.  So it is a bare [Obj.magic], at
     every width and at every depth. *)
  | ECast (e1, t) ->
    (match e1.ty, t with
     | TInt sw1, TInt sw2 when sw1 = sw2 -> term ind e1
     | TInt sw1, TInt sw2 when snd sw1 <> Sizet && snd sw2 <> Sizet ->
       "(FStar_Int_Cast." ^ int_cast_stem sw1 ^ "_to_" ^ int_cast_stem sw2 ^
       " " ^ term ind e1 ^ ")"
     | TInt sw1, TInt sw2 ->
       "(" ^ int_inj sw2 ^ " (" ^ int_module sw1 ^ ".v " ^ term ind e1 ^ "))"
     (* The operand's representation was lost upstream, so there is nothing to
        convert *from*; all that can be done is to assert the target. *)
     | _ -> coerce ind e1 t)
  | ECoerce (e1, t) -> coerce ind e1 t
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
  (* An empty array stands in for a null buffer, but a [ref] has no empty.
     What it does have is a representation: an OCaml [ref] is a one-field
     record, so it is always a *block*, and no block is the immediate 0.  That
     makes 0 a null every [ref] type has room for and none can collide with,
     and the test for it needs no state -- which matters, because under
     [--custard_split] a sentinel defined per file would not be one value.

     Pulse's own realization ([Pulse_Lib_Reference.null]) allocates a dummy
     cell instead and compares against it; that is the same idea with the
     drawback that dereferencing its null quietly reads the dummy.  Here it
     is a null dereference, which is what the program wrote. *)
  | EOp ({ po_op = BufNull }, []) ->
    if TRef? e.ty then "(Obj.magic 0)"
    else "[||]"
  | EOp ({ po_op = BufIsNull }, [b]) ->
    if TRef? b.ty then "(not (Obj.is_block (Obj.repr " ^ term ind b ^ ")))"
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
(* A coercion changes no representation, so between two types that have one it
   is [Obj.magic] and nothing else.  The two exceptions are the widths whose
   OCaml representation is *boxed*: [FStar.SizeT] is an [Sz] and [FStar.UInt8]
   a plain [int], so a coercion that puts one of those where an unrepresented
   value is expected -- or takes one out -- has to open and close the box, or
   the [Obj.magic] would hand the other side a pointer where it wanted a
   scalar.  [TAny] on the other side is not such a case: it is opaque, so
   whatever the box is, it survives. *)
and coerce (ind:string) (e1:expr) (t:cty) : ML string =
  match e1.ty, t with
  | TInt _, TAny | TAny, TInt _ -> "(Obj.magic (" ^ term ind e1 ^ "))"
  | TInt sw1, _ -> "(Obj.magic (" ^ int_module sw1 ^ ".v " ^ term ind e1 ^ "))"
  | _, TInt sw2 -> "(" ^ int_inj sw2 ^ " (Obj.magic (" ^ term ind e1 ^ ")))"
  | _ -> "(Obj.magic (" ^ term ind e1 ^ "))"

and index (ind:string) (e:expr) : ML string =
  match e.e with
  (* A literal index is the common case, and going through [Z.t] to say [0]
     would drown the output. *)
  | EConst (CInt (s, _)) -> s
  (* A coercion does not change the value, and neither does a conversion to a
     width that can hold every value of the one it came from -- which is what
     [uint32_to_sizet] on a length is.  A *narrowing* one does, so it has to be
     evaluated rather than looked through. *)
  | ECoerce (e1, _) -> index ind e1
  | ECast (e1, t) when (match e1.ty, t with
                        | TInt a, TInt b -> value_preserving a b
                        | _ -> false) -> index ind e1
  | _ ->
    (match e.ty with
     | TInt sw -> "(Z.to_int (" ^ int_module sw ^ ".v " ^ term ind e ^ "))"
     | _ -> "(Obj.magic (" ^ term ind e ^ "))")

(* The elements of a sequence, at [ind], without the enclosing parentheses.
   [let ... in] and [;] both extend as far right as they can in OCaml, so one
   pair around the whole run is exactly as many as are needed. *)
and stmts (ind:string) (e:expr) : ML string =
  match e.e with
  | ELet (x, _, e1, e2) ->
    "let " ^ ocaml_local x ^ " = " ^ term (ind ^ "  ") e1 ^ " in\n" ^ ind ^ stmts ind e2
  | ESeq (e1, e2) ->
    (* The discarded expression need not have type unit, and OCaml warns about
       that, so one that is not goes through [ignore]. *)
    let s = term ind e1 in
    let s = if TUnit? e1.ty then s else "(ignore " ^ s ^ ")" in
    s ^ ";\n" ^ ind ^ stmts ind e2
  | _ -> term ind e

and case (ind:string) (br:branch) : ML string =
  let p, g, b = br in
  let _, p, eqs = defer_ints 0 p in
  let conds = eqs |> List.map (fun (x, c) -> ocaml_local x ^ " = " ^ constant c) in
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
         Some (hd ^ " = {\n" ^
               String.concat "" (List.map (fun (f, c) ->
                 "  " ^ ocaml_var f ^ " : " ^ ty c ^ ";\n") fs) ^ "}")
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
    Some ("exception " ^ ocaml_ctor_ident e.de_name ^
          (match e.de_args with
           | [] -> ""
           | args -> " of " ^ String.concat " * " (List.map ty args)))

  | DLet l ->
    (* Every binder and the result carry their type.  Custard knows all of
       them exactly, and writing them down turns a mistake in the extraction
       into an OCaml type error here rather than a puzzle at the use site. *)
    let bs = String.concat "" (List.map (fun b ->
               " (" ^ ocaml_local b.b_name ^ " : " ^ ty b.b_ty ^ ")") l.dl_binders) in
    let rc = if l.dl_flags |> List.existsb Rec? then "rec " else "" in
    let kw = if first then "let " ^ rc else "and " in
    Some (kw ^ ocaml_value_name l.dl_name ^ bs ^ " : " ^ ty l.dl_ret ^
          " =\n  " ^ term "  " l.dl_body)

(* Constructor names have to be declared with the same OCaml name we refer to
   them by, so the variant's constructor labels are the constructors' own
   mangled names. *)
(* Constructor names have to be declared with the same OCaml name we refer to
   them by, so the variant's constructor labels are the constructors' own
   mangled names.

   [homes] is empty for the ordinary whole-program-in-one-file output.  When
   the output is split (section 12.9) it maps each declaration to the OCaml
   module its file compiles to, which is what every cross-file reference is
   qualified by and what decides whether a declaration is *at home* and so
   emitted under its plain identifier. *)
let build_tables (homes : SMap.t string) (p:program) : ML unit =
  let tbl = SMap.create 50 in
  let quals = SMap.create 50 in
  let real = SMap.create 20 in
  let tups = SMap.create 20 in
  let home = SMap.create 50 in
  (* Section 12.9 and 12.3: a declaration imported from a unit that *split* its
     output lives in a file of its own, not in a module named after the unit,
     and it may have been emitted there under its plain identifier.  That is
     precisely what the [homes] treatment below expresses, so such an import
     joins [homes] and is handled by exactly the same code -- which is what
     makes a reference across a link and a reference across a split file print
     the same way, because they are the same thing. *)
  let homes =
    match p |> List.collect (fun d ->
            match imported_home d with
            | Some m -> [(string_of_name (name_of_decl d), m)]
            | None -> []) with
    | [] -> homes
    | hs ->
      let homes' = SMap.copy homes in
      hs |> List.iter (fun (n, m) -> SMap.add homes' n (module_name_of_unit m));
      homes' in
  p |> List.iter (fun d ->
    (* An imported value is exactly an external whose target happens to be
       another generated module: nothing else about it is special, and reusing
       the mechanism means no printing path has to learn about linking. *)
    match imported_unit d with
    | Some _ when Some? (imported_home d) ->
      (* Handled by [homes]; an imported external still resolves to the
         hand-written realization, exactly as below. *)
      (match d with
       | DExternal e ->
         SMap.add tbl (string_of_name e.dx_name)
           (match e.dx_target with Some t -> t | None -> realization_of e.dx_name)
       | _ -> ())
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
  (* Section 12.9.  Every compiled declaration is qualified by its own file --
     {!qualifier} drops the qualification again while that file is the one
     being printed -- so a reference needs to know nothing about where it is.

     A declaration is at home when it sits in the file its own F* module names
     and carries no specialization suffix.  No suffix means it is the only
     declaration from its source lid, so the plain identifier is unambiguous
     within the file, and it is the identifier the hand-written realizations
     spell. *)
  p |> List.iter (fun d ->
    let n = name_of_decl d in
    match SMap.try_find homes (string_of_name n) with
    | None -> ()
    | Some m ->
      let mark (x:name) : ML unit =
        SMap.add quals (string_of_name x) m;
        if None? x.spec && module_name_of_unit (String.concat "." x.ns) = m
        then SMap.add home (string_of_name x) () in
      (* A value is reached through {!externals} when it belongs to a linked
         unit, and through {!qualifiers} otherwise; only the latter is us. *)
      mark n;
      (match d with
       | DType t ->
         (match t.dt_body with
          | TVariant cs -> cs |> List.iter (fun (cn, _) -> mark cn)
          | _ -> ())
       | _ -> ()));
  (* A realized type resolves to its support module, which is the module its
     own namespace names.  This runs after the passes above so that a realized
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
  (* Every record type in the program, realized or not: the ascription is
     just as necessary for a realization's record, and just as harmless when
     the labels happen to be unambiguous. *)
  let recs : SMap.t int = SMap.create 100 in
  let labels : SMap.t int = SMap.create 100 in
  p |> List.iter (fun d ->
    match d with
    | DType t ->
      (match t.dt_body with
       | TRecord fs ->
         SMap.add recs (string_of_name t.dt_name) (List.length t.dt_params);
         fs |> List.iter (fun (f, _) ->
           let k = label_key t.dt_name f in
           SMap.add labels k (1 + (match SMap.try_find labels k with
                                   | Some i -> i
                                   | None -> 0)))
       | _ -> ())
    | _ -> ());
  externals := tbl;
  qualifiers := quals;
  realized := real;
  tuples := tups;
  record_params := recs;
  record_labels := labels;
  at_home := home

let header : string =
  "(* Generated by F* Custard extraction. Do not edit. *)\n\
   [@@@ocaml.warning \"-3-5-8-11-20-26-27-28-32-33-34-35-37-39-50-57-60-69-70\"]\n"

(* [scc] has already made the members of a recursive group adjacent and
   tagged each of them with the group's members; all that is left is to join
   them with [and].  The flag is what identifies the group, not adjacency
   alone: two unrelated self-recursive definitions are also adjacent. *)
let group_of (d:decl) : ML (option (list string)) =
  match decl_flags d |> List.tryFind Rec? with
  | Some (Rec ns) -> Some (List.map string_of_name ns)
  | _ -> None

(* The declarations of one file, already rendered; the tables have to have
   been built.  Not every declaration prints -- a realized type and an
   external are references, not definitions -- so this can be empty, and an
   empty file is one that should not exist. *)
let print_decls (p:program) : ML (list string) =
  let prev : ref (option (list string)) = mk_ref None in
  p |> List.collect (fun d ->
    (* An imported declaration is in the program only so that the tables could
       be built from it. *)
    if Some? (imported_unit d) then [] else
    let g = group_of d in
    let first = None? g || g <> !prev in
    match print_decl first d with
    | Some s -> prev := g; [s]
    | None -> [])

(* Custard compiles standalone programs (section 4.4), so the entry points are
   called from the generated code itself.  An entry point returning a machine
   integer is the process exit status, exactly as it is on the C backend --
   the two must agree, or the same program tested on both reports success on
   one and failure on the other. *)
let entry_calls (p:program) : ML (list string) =
  p |> List.collect (fun d ->
    match d with
    | DLet l when l.dl_flags |> List.existsb Entrypoint?
               && l.dl_binders |> List.for_all (fun b -> TUnit? b.b_ty) ->
      let args = String.concat " " (List.map (fun _ -> "()") l.dl_binders) in
      let call = qualify l.dl_name (ocaml_value_name l.dl_name) ^ " " ^ args in
      (match l.dl_ret with
       (* [v] lands in [Prims.int], which is zarith's, and is the one
          conversion every width's realization has. *)
       | TInt sw ->
         ["let _ = Stdlib.exit (Z.to_int (" ^ int_module sw ^ ".v (" ^ call ^ ")))"]
       | _ -> ["let _ = " ^ call])
    | _ -> [])

let assemble (ds : list string) : ML string =
  header ^ "\n" ^ String.concat "\n\n" ds ^ "\n"

(* Fills {!reserved_top} for the file about to be printed.  It has to run with
   [current_module] already set: [ocaml_value_name] spells a declaration by its
   plain identifier only when it is at home, and the whole question here is
   which names are spelled without a qualifier in *this* file. *)
let reserve_top (p:program) : ML unit =
  reserved_top := p |> List.collect (fun d ->
    match d with
    | DLet l -> [ocaml_value_name l.dl_name]
    | DExternal e -> [ocaml_value_name e.dx_name]
    | _ -> [])

let print_program (p:program) : ML string =
  build_tables (SMap.create 0) p;
  current_module := None;
  reserve_top p;
  assemble (print_decls p @ entry_calls p)

let print_split (files : list (string & program)) : ML (list (string & string)) =
  let homes = SMap.create 100 in
  files |> List.iter (fun (m, ds) ->
    let m = module_name_of_unit m in
    ds |> List.iter (fun d ->
      SMap.add homes (string_of_name (name_of_decl d)) m));
  Prof.timed "p.tables" (fun () -> build_tables homes (List.collect snd files));
  let rendered = files |> List.map (fun (m, ds) ->
    let m = module_name_of_unit m in
    current_module := Some m;
    reserve_top ds;
    let r = (m, Prof.timed "p.decls" (fun () -> print_decls ds)) in
    current_module := None;
    r) in
  (* A module all of whose declarations are references -- a realized one, or
     one that contributed only externals -- gets no file.  Which is also what
     keeps a generated file from colliding with a hand-written realization of
     the same name. *)
  let rendered = rendered |> List.filter (fun (_, ds) -> Cons? ds) in
  (* The entry points are called from the last file that exists, which by
     construction comes after everything they reach.  They are collected from
     the whole program, not from that file, and qualified from where the call
     is written. *)
  let n = List.length rendered in
  let last = if n = 0 then None else Some (fst (List.last rendered)) in
  current_module := last;
  let calls = entry_calls (List.collect snd files) in
  current_module := None;
  rendered |> List.mapi (fun i (m, ds) ->
    (m, Prof.timed "p.render"
          (fun () -> assemble (if i = n - 1 then ds @ calls else ds))))
