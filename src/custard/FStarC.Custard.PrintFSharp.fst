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
module FStarC.Custard.PrintFSharp

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Class.Show
open FStarC.BaseTypes
open FStarC.Const
open FStarC.Custard.Syntax

module BU   = FStarC.Util
module SMap = FStarC.SMap
module E    = FStarC.Errors
module Msg  = FStarC.Errors.Msg

let text = Msg.text

(* -------------------------------------------------------------------- *)
(* Layout                                                               *)
(* -------------------------------------------------------------------- *)

(* Section 122.2.  F# is an offside-rule language, so where a continuation
   line starts is not cosmetic: it is the difference between a program and a
   syntax error.  Every printing function here therefore takes [ind], the
   indentation string standing for the column its output *begins* at, and is
   responsible for indenting anything it puts on a second line further right
   than that.

   The OCaml backend takes an [ind] too, but only to keep the output readable
   -- OCaml would accept any of it.  Here it has to be right, and "the column
   this begins at" is not something a printer can guess: it is the caller's
   column plus the width of whatever the caller has already emitted on that
   line.  {!after} computes exactly that, and every nested call goes through
   it.  That is the whole mechanism, and it is why this backend does not
   inherit the indentation problems of the old [--codegen FSharp] one, which
   emitted a fixed four-space prefix and hoped. *)
let spaces (n:int) : ML string =
  if n <= 0 then "" else FStarC.String.make n ' '

(* The column just past [s], where [s] itself began at column [c].  A [s] that
   spans lines resets the count: what comes next sits after its *last* line,
   and the earlier ones no longer say anything about where that is.

   It scans backwards from the end and stops at the first newline, so it costs
   the width of one line rather than the size of [s].  That is not a
   micro-optimization: [s] here is everything emitted so far on the enclosing
   construct, this runs once per nested subterm, and the corpus contains a
   single expression that prints to 587kB (section 122.2.1). *)
let col_after (c:int) (s:string) : ML int =
  let n = String.length s in
  let rec go (i:int) : ML int =
    if i <= 0 then c + n
    else if FStarC.String.get s (i - 1) = '\n' then n - i
    else go (i - 1) in
  go n

(* The indentation for the column {!col_after} names. *)
let after (ind:string) (s:string) : ML string =
  spaces (col_after (String.length ind) s)

(* Render [xs] left to right, each at the column it actually begins at,
   joined by [sep], onto the end of [pre].  Threading the accumulated column
   is what keeps the columns honest when an earlier element was itself
   multi-line; the pieces are accumulated in reverse and joined once, because
   a left-fold with [^] would copy the whole prefix per element. *)
let rec join_at_aux (#a:Type) (acc:list string) (col:int) (sep:string)
                    (f : string -> a -> ML string) (xs : list a)
                    : ML (list string) =
  match xs with
  | [] -> acc
  | [x] -> f (spaces col) x :: acc
  | x :: xs ->
    let s = f (spaces col) x in
    let col = col_after (col_after col s) sep in
    join_at_aux (sep :: s :: acc) col sep f xs

let join_at (#a:Type) (ind:string) (pre:string) (sep:string)
            (f : string -> a -> ML string) (xs : list a) : ML string =
  let col = col_after (String.length ind) pre in
  String.concat "" (List.rev (join_at_aux [pre] col sep f xs))

(* Past this many columns a line stops being one a reader takes in at a
   glance, which is the only thing the layout here is for. *)
let line_width : int = 80

(* -------------------------------------------------------------------- *)
(* Tables                                                               *)
(* -------------------------------------------------------------------- *)

(* Symbols with no F* definition.  Unlike the OCaml backend, where this is the
   main event -- nearly everything resolves to a hand-written realization in
   [ulib/ml] -- here it holds only two kinds of thing: a [@@custard_extern]
   target, which the program supplied itself, and the handful of names the
   support library of section 122.8 implements.  Everything else is refused
   (section 122.9), which is why this table can be small. *)
let externals : ref (SMap.t string) = mk_ref (SMap.create 0)

let external_target (n:name) : ML (option string) =
  SMap.try_find !externals (string_of_name n)

(* [FStar.Pervasives.Native.tupleN] is .NET's own N-tuple: no constructor to
   name, no field to project.  Keyed by both the type's name and its
   constructor's, valued by the arity. *)
let tuples : ref (SMap.t int) = mk_ref (SMap.create 0)

(* Constructors declared with no arguments.  [| C _ -> ] is a type error in F#
   when [C] is nullary, and a discriminator has to be written one way or the
   other, so the arity is recorded rather than guessed. *)
let nullary : ref (SMap.t unit) = mk_ref (SMap.create 0)

(* How many type parameters each record type takes, and which of its labels
   are contested.  F# resolves a bare label to the *last* record type declared
   with it, exactly as OCaml does, and is silent about it in exactly the same
   way; the fix is the same too. *)
let record_params : ref (SMap.t int) = mk_ref (SMap.create 0)
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

let is_nullary_ctor (n:name) : ML bool =
  Some? (SMap.try_find !nullary (string_of_name n))

(* A tuple component's field name is [_1], [_2], ...; its position is the
   number. *)
let tuple_index (f:string) : ML int =
  let s = if String.strlen f > 0 && String.substring f 0 1 = "_"
          then String.substring f 1 (String.strlen f - 1) else f in
  match FStarC.Util.safe_int_of_string s with Some i -> i | None -> 0

(* Place [fs] at the positions their field names give, filling the gaps with
   [dflt]. *)
let by_position (k:int) (dflt:string) (fs : list (string & string)) : ML (list string) =
  let at (i:int) : ML string =
    match fs |> List.tryPick (fun (f, s) ->
                  if tuple_index f = i then Some s else None) with
    | Some s -> s
    | None -> dflt in
  let rec go (i:int) : ML (list string) =
    if i > k then [] else at i :: go (i + 1) in
  go 1

(* -------------------------------------------------------------------- *)
(* Names                                                                *)
(* -------------------------------------------------------------------- *)

(* The F# keywords, the ones reserved for future use, and the ones reserved
   for OCaml compatibility.  All three kinds are equally unusable as an
   identifier, so the list does not distinguish them. *)
let fsharp_keywords = [
  "abstract"; "and"; "as"; "assert"; "base"; "begin"; "class"; "default";
  "delegate"; "do"; "done"; "downcast"; "downto"; "elif"; "else"; "end";
  "exception"; "extern"; "false"; "finally"; "fixed"; "for"; "fun";
  "function"; "global"; "if"; "in"; "inherit"; "inline"; "interface";
  "internal"; "lazy"; "let"; "match"; "member"; "module"; "mutable";
  "namespace"; "new"; "not"; "null"; "of"; "open"; "or"; "override";
  "private"; "public"; "rec"; "return"; "select"; "static"; "struct";
  "then"; "to"; "true"; "try"; "type"; "upcast"; "use"; "val"; "void";
  "when"; "while"; "with"; "yield";
  (* Reserved for future use. *)
  "atomic"; "break"; "checked"; "component"; "const"; "constraint";
  "constructor"; "continue"; "eager"; "event"; "external"; "functor";
  "include"; "method"; "mixin"; "object"; "parallel"; "process";
  "protected"; "pure"; "sealed"; "tailcall"; "trait"; "virtual";
  (* Reserved for OCaml compatibility.  F# does not give these a meaning,
     but it does refuse them as identifiers, and F* code does use [mod]. *)
  "asr"; "land"; "lor"; "lsl"; "lsr"; "lxor"; "mod"; "sig";
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
    else "u_" ^ s

let uppercase_first (s:string) : ML string =
  if s = "" then "X"
  else
    let i = BU.int_of_char (List.hd (String.list_of_string s)) in
    let hd = String.uppercase (String.substring s 0 1) in
    let tl = String.substring s 1 (String.length s - 1) in
    if is_alpha i then hd ^ tl else "U" ^ s

(* Section 122.3.  A keyword is escaped by F#'s own double-backtick
   quotation rather than by the OCaml backend's trailing underscore.

   The underscore has to be applied to a *stripped* name to stay injective --
   [method] and [method_] would otherwise both come out [method_], and the
   second would silently capture the first (section 115).  Backticks need no
   such care: [``mod``] is a spelling nothing else produces, because the only
   names that get them are keywords and a keyword is never the result of
   appending anything.  So the escape is injective by construction rather than
   by an argument, which is the better of the two ways to be right.

   {!sanitize} has already restricted the character set, so the quoted form is
   always well formed. *)
let escape_keyword (s:string) : ML string =
  if List.existsb (fun k -> k = s) fsharp_keywords then "``" ^ s ^ "``" else s

let fsharp_value_name (n:name) : ML string =
  escape_keyword (lowercase_first (sanitize (mangled_name n)))

let fsharp_type_name (n:name) : ML string =
  escape_keyword (lowercase_first (sanitize (mangled_name n)))

(* A union case and an exception both have to begin with a capital, or F#
   reads them as variables in a pattern (warning 49) and, worse, matches
   anything. *)
let fsharp_ctor_ident (n:name) : ML string =
  uppercase_first (sanitize (mangled_name n))

let module_name_of_unit (u:string) : ML string = uppercase_first (sanitize u)

let fsharp_var (x:string) : ML string =
  escape_keyword (lowercase_first (sanitize x))

(* Section 122.3.1.  A type variable is written with a leading quote, and F*
   names them [a'] and [t'] routinely -- so the obvious spelling produces
   ['t'], which F# lexes as a character literal and reports as [Invalid
   literal in type], about a line nobody wrote.  A quote inside the name
   becomes an underscore, and an underscore doubles, which keeps the mapping
   injective: two variables of one declaration must not collide.  The
   backtick escape is not available here, since a quoted identifier is not a
   type variable. *)
let fsharp_tyvar (x:string) : ML string =
  let s = lowercase_first (sanitize x) in
  let s = String.concat "" (List.map (fun c ->
            match BU.int_of_char c with
            | 39 -> "_"
            | 95 -> "__"
            | _ -> BU.string_of_char c) (String.list_of_string s)) in
  "'" ^ (if List.existsb (fun k -> k = s) fsharp_keywords then s ^ "_q" else s)

(* Section 30.13.  The top-level names this file will define.  A reference to
   one is unqualified -- there is no way to say [Custard.foo] inside module
   [Custard] -- so a local of the same name captures it silently. *)
let reserved_top : ref (list string) = mk_ref []

let fsharp_local (x:string) : ML string =
  let s = fsharp_var x in
  if List.existsb (fun k -> k = s) !reserved_top then s ^ "_" else s

(* -------------------------------------------------------------------- *)
(* Types                                                                *)
(* -------------------------------------------------------------------- *)

(* Section 122.4.  A machine integer is .NET's own, not a support module's.
   This is the single largest difference from the OCaml backend and the reason
   this one exists: OCaml has no unsigned 32-bit type, so [FStar.UInt32.t]
   there is [Stdint.Uint32.t] and every operation on it is a call into
   [ulib/ml]; .NET has [uint32], and an addition is [+]. *)
let int_type (sw : signedness & iwidth) : ML string =
  let s, w = sw in
  match w with
  (* [FStar.SizeT.t] is 64 bits at every target F* supports, so it is
     [uint64] and not [unativeint]: the latter would be 32 bits on a 32-bit
     runtime, which is a different type and a different program. *)
  | WSizet -> "uint64"
  | W128 -> (match s with
             | Unsigned -> "System.UInt128"
             | Signed -> "System.Int128")
  | _ ->
    (match s with Unsigned -> "uint" | Signed -> "int") ^
    (match w with
     | W8 -> "8" | W16 -> "16" | W32 -> "32" | W64 -> "64"
     | W128 | WSizet -> "64")

(* The suffix an F# literal of this width carries.  The 128-bit widths have
   none -- F# has no literal for them at all -- and are handled at the literal
   itself. *)
let int_suffix (sw : signedness & iwidth) : ML string =
  let s, w = sw in
  match w with
  | WSizet -> "UL"
  | W8  -> (match s with Unsigned -> "uy" | Signed -> "y")
  | W16 -> (match s with Unsigned -> "us" | Signed -> "s")
  | W32 -> (match s with Unsigned -> "u"  | Signed -> "")
  | W64 -> (match s with Unsigned -> "UL" | Signed -> "L")
  | W128 -> ""

let is_w128 (sw : signedness & iwidth) : bool = W128? (snd sw)

(* Section 122.5.  F# has a real binary32, so unlike the OCaml backend this
   one does not have to refuse [FStar.Float32].  The 16-bit widths it does:
   [System.Half] exists but has no literal and no primitive arithmetic, and
   emitting an emulation of a format the program asked for by name would be
   the same silent substitution section 38 refuses on the OCaml path. *)
let reject_fwidth (fw:fwidth) : ML unit =
  if Float64? fw || Float32? fw then () else
  let format = (match fw with
                | Float32 -> "binary32" | Float64 -> "binary64"
                | Float16 -> "binary16" | BFloat16 -> "bfloat16") in
  E.raise_error0 E.Error_CustardNoCRepresentation [
    text ("Custard: " ^ format ^ " has no F# representation.");
    text ("F# has float (binary64) and float32 (binary32) and nothing \
           narrower that arithmetic is defined on, so such a program would \
           compute at a width it did not ask for (sections 38 and 122.5).");
    text "Use FStar.Float32 or FStar.Float64, or extract with \
          --custard_backend C." ]

(* Types F# already has.  Emitting a declaration for one of these would
   shadow the real thing; a monomorphized clone carries a [spec] suffix and is
   a genuinely new type, so it is declared like any other. *)
let builtin_type (n:name) : ML (option string) =
  match (if Some? n.spec then "" else String.concat "." (n.ns @ [n.id])) with
  | "Prims.unit" -> Some "unit"
  | "Prims.bool" -> Some "bool"
  (* A .NET string is a sequence of UTF-16 code units rather than of code
     points.  Every operation Custard emits on one is equality or a literal,
     both of which agree with F*'s reading; anything that would notice the
     difference lives in [FStar.String], which this backend refuses
     (section 122.9). *)
  | "Prims.string" -> Some "string"
  (* [Prims.int] is arbitrary precision, so it is [System.Numerics.BigInteger]
     -- which F# spells [bigint] and gives literals and operators. *)
  | "Prims.int" -> Some "bigint"
  | "Prims.exn" -> Some "exn"
  | "Prims.list" -> Some "list"
  (* [FStar.Char.char] is a Unicode scalar and a .NET [char] is a UTF-16 code
     unit, so the two agree on the Basic Multilingual Plane and part company
     above it.  The support library's [FStar.String] is written against this
     reading throughout -- [list_of_string] yields code units, [strlen] counts
     them -- so a program that stays inside it is consistent with itself; what
     it is not is faithful to F*'s specification for text outside the BMP.
     That is the same trade [Prims.string] already makes. *)
  | "FStar.Char.char"
  | "FStar.String.char" -> Some "char"
  | "FStar.Pervasives.Native.option" -> Some "option"
  | _ -> None

let is_builtin_type (n:name) : ML bool = Some? (builtin_type n)

let rec ty (t:cty) : ML string =
  match t with
  | TUnit -> "unit"
  | TExn -> "exn"
  (* Section 122.6.  [TAny] is a value whose representation was lost, which in
     .NET is [obj]: every type boxes into it and unboxes back out. *)
  | TAny -> "obj"
  | TVar x -> fsharp_tyvar x
  | TInt sw -> int_type sw
  | TFloat Float64 -> "float"
  | TFloat Float32 -> "float32"
  | TFloat fw -> reject_fwidth fw; "float"
  (* Section 122.14.  A [unit] argument is not an argument: the IR drops such
     a binder from a definition that has another one, exactly as the C backend
     drops it from a signature, and an arrow type that kept it would disagree
     with the definition it describes.  The disagreement is invisible while a
     function is only called -- a call site consults the definition -- and
     surfaces the moment one is passed as a value.

     An arrow whose every argument is [unit] keeps one, because a definition
     with no binders at all is a value rather than a function, and a value is
     evaluated once. *)
  | TArrow _ ->
    let rec split (t:cty) : ML (list cty & cty) =
      match t with
      | TArrow (a, _, b) -> let args, r = split b in (a :: args, r)
      | _ -> ([], t) in
    let args, ret = split t in
    let kept = args |> List.filter (fun a -> not (TUnit? a)) in
    let kept = if Nil? kept then [TUnit] else kept in
    "(" ^ String.concat " -> " (List.map ty kept) ^ " -> " ^ ty ret ^ ")"
  | TTuple ts -> "(" ^ String.concat " * " (List.map ty ts) ^ ")"
  (* Section 8.4: a buffer is a .NET array.  Faithful for everything but
     [BufSub], which needs an interior pointer; that one is refused at run
     time rather than mistranslated. *)
  | TBuf t -> "(" ^ ty t ^ ")[]"
  | TRef t -> "(" ^ ty t ^ " ref)"
  | TInline _ ->
    failwith "Custard: an inline-field marker reached the F# backend"
  | TConst _ ->
    E.raise_error0 E.Error_CustardBadTemplateArg [
      text "Custard: an external type with a template target reached the F# \
            backend.";
      text "[wmma::fragment<matrix_a, 16, 16, 16, half, row_major>] is one \
            type and [wmma::fragment<matrix_b, ...>] another; F# has no such \
            construction, so section 69 is a C-backend feature \
            (--custard_backend C).";
      text "The unparameterized form still works everywhere: a \
            [@@custard_extern] target with no [{0}] placeholder names one \
            target type, and its arguments are dropped." ]
  | TApp (n, args) when is_tuple_type n && Cons? args ->
    "(" ^ String.concat " * " (List.map ty args) ^ ")"
  | TApp (n, []) ->
    (match builtin_type n with
     | Some s -> s
     | None -> fsharp_type_name n)
  (* F#'s postfix application only takes one argument, so the generic form is
     written the .NET way.  It is also accepted at one argument, which is why
     there is one case here and not two. *)
  | TApp (n, args) ->
    let hd = match builtin_type n with
             | Some s -> s
             | None -> fsharp_type_name n in
    hd ^ "<" ^ String.concat ", " (List.map ty args) ^ ">"

(* Section 122.6.2.  A [box] followed by an [unbox] is exact when the two sides
   name the same runtime type and a checked failure otherwise -- .NET does not
   have OCaml's uniform representation, so [Obj.magic]'s "nothing at run time"
   has no counterpart.  Almost every coercion Custard emits is exact anyway:
   the value really was boxed at the type it is being read back at, and the
   IR's own type for it differs only because a field it came out of was laid
   out as [any].

   The one shape that is not is a *parameterized* type read at a different
   parameter: [sized<uint32>] and [sized<obj>] are two runtime types, and no
   amount of agreeing about layout makes one the other.  An array and a
   reference cell are the same situation with the constructor built in.  Those
   are refused rather than emitted, because what they do at run time is throw
   [InvalidCastException] from a line the reader did not write. *)
let rec erased_pun (a:cty) (b:cty) : bool =
  match a, b with
  | TApp (n1, a1), TApp (n2, a2) ->
    (Cons? a1 || Cons? a2) && not (n1 = n2 && a1 = a2)
  | TBuf t1, TBuf t2 -> not (t1 = t2)
  | TRef t1, TRef t2 -> not (t1 = t2)
  | TBuf t1, TRef t2 | TRef t1, TBuf t2 -> erased_pun t1 t2
  | _ -> false

let reject_coercion (a:cty) (b:cty) : ML string =
  E.raise_error0 E.Error_CustardNoFSharpRealization [
    text ("Custard: this value changes representation from " ^ ty a ^ " to " ^
          ty b ^ ", which .NET cannot express.");
    text "The OCaml backend writes such a change as Obj.magic, which is \
          nothing at run time because every OCaml value has the same shape.  \
          .NET types are not uniform: an unbox is a checked cast, and \
          sized<uint32> is not sized<obj> however the two are laid out \
          (section 122.6.2).";
    text "The change is under a type constructor rather than at the top of \
          the type, which is where an erased field can be.  Extract this \
          program with --custard_backend OCaml, or give the declaration a \
          type whose erased part is a field rather than a parameter." ]

(* -------------------------------------------------------------------- *)
(* Constants                                                            *)
(* -------------------------------------------------------------------- *)

(* F* strings are sequences of Unicode code points and .NET strings are
   sequences of UTF-16 code units, so a code point is escaped only when it has
   to be: the F# compiler reads the source as UTF-8 and decodes the rest for
   itself, which is what the reader wanted in the first place. *)
let hexd (i:int) : string =
  let d = ["0";"1";"2";"3";"4";"5";"6";"7";"8";"9";"a";"b";"c";"d";"e";"f"] in
  match List.nth d i with x -> x

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
      if i < 32 || i = 127
      then "\\u00" ^ hexd ((i / 16) % 16) ^ hexd (i % 16)
      else BU.string_of_char c
  in
  String.concat "" (List.map esc (String.list_of_string s))

(* Section 122.7.  A 128-bit literal is parsed at run time, because F# has no
   literal for [System.UInt128] and no way to write one: the two-word
   constructor would need the value split into halves here, and [Parse] of the
   decimal spelling is the reading that cannot be got wrong.  Literals of this
   width are rare enough -- they exist at all only under --custard_int128 --
   that the cost is not worth an arithmetic step in the compiler. *)
let int128_literal (sw : signedness & iwidth) (v:int) (b:int_base) : ML string =
  "(" ^ int_type sw ^ ".Parse \"" ^ int_lit_to_string v Dec ^ "\")"

(* Section 122.9.  [FStar.Char.char] is .NET's [char], which is a UTF-16 code
   unit: it holds the Basic Multilingual Plane and nothing above it.  A
   literal outside that range is refused here rather than truncated, since a
   silently different character is section 38's substitution again.

   The escapes are F#'s own, which are C's for the four that matter plus
   [\\uXXXX]; anything outside printable ASCII goes through the latter so that
   the output does not depend on how the file is decoded. *)
let char_literal (c:char) : ML string =
  let i = BU.int_of_char c in
  if i > 65535
  then E.raise_error0 E.Error_CustardNoCRepresentation [
         text ("Custard: the character literal U+" ^
               hexd ((i / 65536) % 16) ^ hexd ((i / 4096) % 16) ^
               hexd ((i / 256) % 16) ^ hexd ((i / 16) % 16) ^ hexd (i % 16) ^
               " has no F# representation.");
         text "An F# char is a UTF-16 code unit and so cannot hold a code \
               point above the Basic Multilingual Plane (section 122.9)." ]
  else
    let body =
      match c with
      | '\n' -> "\\n"
      | '\t' -> "\\t"
      | '\r' -> "\\r"
      | '\'' -> "\\'"
      | '\\' -> "\\\\"
      | c ->
        if i < 32 || i > 126
        then "\\u" ^ hexd ((i / 4096) % 16) ^ hexd ((i / 256) % 16) ^
                      hexd ((i / 16) % 16) ^ hexd (i % 16)
        else BU.string_of_char c in
    "'" ^ body ^ "'"

let constant (c:constant) : ML string =
  match c with
  | CUnit -> "()"
  | CBool b -> if b then "true" else "false"
  (* Section 39.  F#'s lexer accepts the same grammar section 39.2 does; a
     binary32 literal is the same text with an [f] after it.  Section 125.5's
     two special values are identifiers instead, and F# suffixes those with
     [f] too. *)
  | CFloat (FLNan, fw) ->
    reject_fwidth fw; if Float32? fw then "(nanf)" else "(nan)"
  | CFloat (FLInf neg, fw) ->
    reject_fwidth fw;
    (if neg then "(-" else "(") ^ (if Float32? fw then "infinityf" else "infinity") ^ ")"
  | CFloat (v, fw) ->
    reject_fwidth fw;
    "(" ^ float_lit_to_string v ^ (if Float32? fw then "f" else "") ^ ")"
  (* F# writes a [bigint] literal with an [I] suffix, in decimal only. *)
  | CInt (v, b, None) -> "(" ^ int_lit_to_string v Dec ^ "I)"
  | CInt (v, b, Some sw) when is_w128 sw -> int128_literal sw v b
  (* F# takes 0x, 0o and 0b exactly as F* writes them, so the base a program
     chose to write a constant in survives into the output. *)
  | CInt (v, b, Some sw) -> "(" ^ int_lit_to_string v b ^ int_suffix sw ^ ")"
  | CChar c -> char_literal c
  | CString s -> "\"" ^ escape s ^ "\""

(* -------------------------------------------------------------------- *)
(* Operators                                                            *)
(* -------------------------------------------------------------------- *)

(* The F# spelling of a binary operator, where there is one.  At a machine
   width these are .NET's own primitives, and unchecked: [+] on [uint8] wraps,
   which is what [add_mod] means and what [add]'s precondition promises will
   not happen.  The connectives are separated out by {!at_int_width}, since
   [And] at a width is bitwise and [And] without one is [&&]. *)
let binop (at_width:bool) (o:op) : ML (option string) =
  match o with
  | Add | AddW -> Some "+"
  | Sub | SubW -> Some "-"
  | Mult | MultW -> Some "*"
  | Div | DivW -> Some "/"
  | Mod -> Some "%"
  | Eq -> Some "=" | Neq -> Some "<>"
  | Lt -> Some "<" | Lte -> Some "<=" | Gt -> Some ">" | Gte -> Some ">="
  | BOr -> Some "|||" | BAnd -> Some "&&&" | BXor -> Some "^^^"
  | And -> Some (if at_width then "&&&" else "&&")
  | Or -> Some (if at_width then "|||" else "||")
  | _ -> None

let unop (at_width:bool) (o:op) : ML (option string) =
  match o with
  | BNot -> Some "~~~"
  | Not -> Some (if at_width then "~~~" else "not")
  | _ -> None

(* Section 122.7.  [System.UInt128] implements every arithmetic and bitwise
   interface .NET has, but F#'s [~~~] resolves against [op_LogicalNot], which
   is not one of the names those interfaces use, so the complement is the one
   operator that has to be spelled out.  Everything else -- [+], [&&&],
   [<<<], [<] -- resolves. *)
let w128_unop (sw : signedness & iwidth) (o:op) : ML (option string) =
  if not (is_w128 sw) then None else
  match o with
  | BNot | Not -> Some ("FStarCustard." ^
                        (if Unsigned? (fst sw) then "notU128" else "notI128"))
  | _ -> None

let is_shift (o:op) : bool = BShiftL? o || BShiftR? o

(* Whether a width conversion can change the mathematical value.
   [width_bits] is [Syntax]'s. *)
let value_preserving (a b : signedness & iwidth) : bool =
  let sa, wa = a in
  let sb, wb = b in
  match sa, sb with
  | Unsigned, Unsigned
  | Signed, Signed -> width_bits wa <= width_bits wb
  | Unsigned, Signed -> width_bits wa < width_bits wb
  | Signed, Unsigned -> false

(* Section 122.4.  The conversion function for a target width.  F#'s own
   [uint8], [int16] and friends are unchecked and truncating, which is exactly
   what [FStar.Int.Cast] specifies; the 128-bit pair has no such function, and
   widening into it needs the source's sign, so it goes through the support
   library instead ({!runtime_source}). *)
let int_conv (sw : signedness & iwidth) : ML string =
  let s, w = sw in
  match w with
  | WSizet -> "uint64"
  | W128 -> (match s with
             | Unsigned -> "FStarCustard.toU128"
             | Signed -> "FStarCustard.toI128")
  | _ -> int_type sw

(* -------------------------------------------------------------------- *)
(* Patterns                                                             *)
(* -------------------------------------------------------------------- *)

(* Which record type is meant.  F# resolves a label to the last record type
   declared with it, silently, so an expression built out of labels alone can
   be given the wrong type and fail somewhere else entirely.  Unlike OCaml, F#
   lets the *label* name its type -- [{ foo.a = 1; b = 2 }] -- which says
   which one is meant at the one place a reader is looking, so that is what is
   used to build and to match. *)
let qualified_label (n:name) (f:string) : ML string =
  if is_builtin_type n then fsharp_var f
  else fsharp_type_name n ^ "." ^ fsharp_var f

(* A projection has no label list to hang the type off, so it takes an
   ascription instead, with a wildcard for each parameter: it is the type's
   identity that is in question and never its arguments. *)
let ascribe_record (n:name) (f:string) (s:string) : ML string =
  if not (ambiguous_label n f) then s else
  match SMap.try_find !record_params (string_of_name n) with
  | None -> s
  | Some k ->
    let rec wilds (i:int) : ML (list string) =
      if i <= 0 then [] else "_" :: wilds (i - 1) in
    let args = if k = 0 then "" else "<" ^ String.concat ", " (wilds k) ^ ">" in
    s ^ " : " ^ fsharp_type_name n ^ args

(* F# has no integer pattern that means what the IR's [PConst (CInt _)] means:
   a [bigint] literal is not a pattern, and neither is a [UInt128.Parse].  The
   fixed-width ones *are* patterns, so only those two cases are deferred into
   a [when] clause. *)
let deferred_const (c:FStarC.Custard.Syntax.constant) : bool =
  match c with
  | CInt (_, _, None) -> true
  | CInt (_, _, Some sw) -> is_w128 sw
  | _ -> false

let rec defer_ints (n:int) (p:pat) : (int & pat & list (string & FStarC.Custard.Syntax.constant)) =
  match p with
  | PConst c when deferred_const c ->
    let x = "_iconst" ^ string_of_int n in
    (n + 1, PVar x, [(x, c)])
  | PCtor (nm, ps) -> let n, ps, eqs = defer_ints_list n ps in (n, PCtor (nm, ps), eqs)
  | PRecord (nm, fs) -> let n, fs, eqs = defer_ints_fields n fs in (n, PRecord (nm, fs), eqs)
  | PTuple ps -> let n, ps, eqs = defer_ints_list n ps in (n, PTuple ps, eqs)
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

(* The F# type a constant pattern matches against, used by {!term} to unbox a
   scrutinee whose representation was erased (section 122.6.1). *)
let rec pat_scalar_ty (p:pat) : ML (option string) =
  match p with
  | PConst CUnit -> Some "unit"
  | PConst (CBool _) -> Some "bool"
  | PConst (CChar _) -> Some "char"
  | PConst (CString _) -> Some "string"
  | PConst (CFloat (_, fw)) -> reject_fwidth fw;
                               Some (if Float32? fw then "float32" else "float")
  | PConst (CInt (_, _, None)) -> Some "bigint"
  | PConst (CInt (_, _, Some sw)) -> Some (int_type sw)
  | POr ps -> List.tryPick pat_scalar_ty ps
  | _ -> None

let rec pattern (p:pat) : ML string =
  match p with
  | PWild -> "_"
  | PVar x -> fsharp_local x
  | PConst c -> constant c
  | PCtor (n, []) -> ctor_ref n
  | PCtor (n, [p1; p2]) when builtin_ctor n = Some "::" ->
    "(" ^ pattern p1 ^ " :: " ^ pattern p2 ^ ")"
  | PCtor (n, ps) when Some? (tuple_arity n) ->
    "(" ^ String.concat ", " (List.map pattern ps) ^ ")"
  | PCtor (n, ps) -> "(" ^ ctor_ref n ^ " (" ^ String.concat ", " (List.map pattern ps) ^ "))"
  | PRecord (n, fs) when Some? (tuple_arity n) ->
    let k = Some?.v (tuple_arity n) in
    "(" ^ String.concat ", "
            (by_position k "_" (fs |> List.map (fun (f, p) -> (f, pattern p)))) ^ ")"
  (* An F# record pattern is partial by construction and warns about nothing,
     so unlike OCaml's it neither needs nor accepts a trailing wildcard. *)
  | PRecord (n, fs) ->
    "{ " ^ String.concat "; " (List.mapi (fun i (f, p) ->
             (if i = 0 then qualified_label n f else fsharp_var f)
             ^ " = " ^ pattern p) fs) ^ " }"
  | PTuple ps -> "(" ^ String.concat ", " (List.map pattern ps) ^ ")"
  | POr ps -> "(" ^ String.concat " | " (List.map pattern ps) ^ ")"

and ctor_ref (n:name) : ML string =
  match builtin_ctor n with
  | Some c -> c
  | None -> fsharp_ctor_ident n

and builtin_ctor (n:name) : ML (option string) =
  match (if Some? n.spec then "" else String.concat "." (n.ns @ [n.id])) with
  | "Prims.Nil" -> Some "[]"
  | "Prims.Cons" -> Some "::"
  | "FStar.Pervasives.Native.None" -> Some "None"
  | "FStar.Pervasives.Native.Some" -> Some "Some"
  | _ -> None

(* -------------------------------------------------------------------- *)
(* Expressions                                                          *)
(* -------------------------------------------------------------------- *)

let rec term (ind:string) (e:expr) : ML string =
  match e.e with
  | EConst c -> constant c
  | EVar x -> fsharp_local x
  | EQual (n, _) ->
    (match external_target n with
     | Some t -> t
     | None -> fsharp_value_name n)
  | ECtor (n, []) -> ctor_ref n
  | ECtor (n, [a; b]) when builtin_ctor n = Some "::" ->
    join_at ind "(" " :: " term [a; b] ^ ")"
  | ECtor (n, args) when Some? (tuple_arity n) ->
    join_at ind "(" ", " term args ^ ")"
  | ECtor (n, args) ->
    join_at ind ("(" ^ ctor_ref n ^ " (") ", " term args ^ "))"
  | ETuple es -> join_at ind "(" ", " term es ^ ")"
  (* Section 122.14, the call side of the same rule. *)
  | EApp (hd, args) ->
    let kept = args |> List.filter (fun (a:expr) -> not (TUnit? a.ty)) in
    let kept = if Nil? kept then args else kept in
    join_at ind "(" " " term (hd :: kept) ^ ")"
  (* Section 122.10.  Every binder carries its type.  F#'s inference is
     weaker than OCaml's -- it is left-to-right and has no principal types for
     a field access -- so a lambda whose parameter is only used as the subject
     of a projection does not type-check unannotated.  Custard knows the type
     exactly, so it writes it down. *)
  | EFun (bs, body) ->
    let pre = "(fun " ^ String.concat " "
                (List.map (fun b -> "(" ^ fsharp_local b.b_name ^ " : " ^ ty b.b_ty ^ ")") bs)
              ^ " -> " in
    pre ^ term (after ind pre) body ^ ")"
  (* A binding and a statement both open a *sequence*, which {!stmts} prints
     as one run at one column.  That column is one past the paren. *)
  | ELet _ | ESeq _ -> "(" ^ stmts (ind ^ " ") e ^ ")"
  | EIf (c, t, f) ->
    let pre = "(if " in
    let pre = pre ^ term (after ind pre) c ^ " then " in
    let pre = pre ^ term (after ind pre) t ^ " else " in
    pre ^ term (after ind pre) f ^ ")"
  | EMatch (scrut, brs) ->
    (* Section 122.6.1.  The scrutinee is an [obj] and the patterns are not:
       [any]-splitting leaves the coercion to the reader of the value, and in
       .NET reading an [obj] as a [bool] is an unbox rather than nothing at
       all.  OCaml needs no such thing because [Obj.magic] has no type.  Only
       a constant pattern is handled: it names its type by itself, while a
       constructor pattern would need the type arguments too, and the layout
       analysis does not produce that case. *)
    let ub = if TAny? scrut.ty
             then List.tryPick (fun (p, _, _) -> pat_scalar_ty p) brs
             else None in
    let pre = "(match " ^ (match ub with
                           | Some t -> "(unbox<" ^ t ^ "> "
                           | None -> "") in
    let hd = pre ^ term (after ind pre) scrut
             ^ (if Some? ub then ")" else "") ^ " with\n" in
    (* The bar of a case sits under the [match], which is one past the paren;
       F# requires it to be no further left than that. *)
    let ind' = ind ^ " " in
    hd ^ String.concat "\n" (List.map (case ind') brs) ^ ")"
  | ERecord (n, fs) when Some? (tuple_arity n) ->
    let k = Some?.v (tuple_arity n) in
    "(" ^ String.concat ", "
            (by_position k "(Unchecked.defaultof<_>)"
               (fs |> List.map (fun (f, e) -> (f, term (ind ^ " ") e)))) ^ ")"
  (* One field per line, unless the whole literal fits on the line it is
     already on: a record is where a reader looks up what a value is made of,
     and the fields of the ones this compiler builds are whole expressions
     rather than names -- but a two-field record of variables is not clearer
     for being spread over two lines. *)
  | ERecord (n, fs) ->
    let ind' = ind ^ "  " in
    let parts = List.mapi (fun i (f, e) ->
                  (if i = 0 then qualified_label n f else fsharp_var f)
                  ^ " = " ^ term ind' e) fs in
    let one = "{ " ^ String.concat "; " parts ^ " }" in
    if String.length ind + String.length one <= line_width
       && not (List.existsb (fun c -> c = '\n') (String.list_of_string one))
    then one
    else "{ " ^ String.concat (";\n" ^ ind') parts ^ " }"
  (* A tuple has no projection in F# beyond [fst] and [snd], so every
     component is read by a match that names it and ignores the rest. *)
  | EProj (e1, n, f) when Some? (tuple_arity n) ->
    let k = Some?.v (tuple_arity n) in
    let pre = "(match " in
    pre ^ term (after ind pre) e1 ^ " with (" ^
    String.concat ", " (by_position k "_" [(f, "custard_tup")]) ^ ") -> custard_tup)"
  | EProj (e1, n, f) ->
    "(" ^ ascribe_record n f (term (ind ^ " ") e1) ^ ")." ^ fsharp_var f
  (* A tuple type has one constructor, so the test is vacuous. *)
  | EDiscrim (_, n) when Some? (tuple_arity n) -> "true"
  | EDiscrim (e1, n) ->
    let arg = if is_nullary_ctor n then "" else " _" in
    let pre = "(match " in
    pre ^ term (after ind pre) e1 ^ " with " ^ ctor_ref n ^ arg ^
    " -> true | _ -> false)"
  (* Section 122.4.  Every machine width is a distinct .NET type, so a
     conversion between two of them is a conversion and not a reinterpretation
     -- and a narrowing one truncates, which is what [FStar.Int.Cast]
     specifies and what F#'s own conversion functions do.

     A *coercion* is the opposite case: it must not change the representation
     at all, since the same value also crosses the boundary inside a structure
     where no per-element conversion is possible.  So it is a box and an
     unbox, at every width and at every depth. *)
  | ECast (e1, t) ->
    (match e1.ty, t with
     | TInt sw1, TInt sw2 when sw1 = sw2 -> term ind e1
     | TFloat _, TFloat fw2 ->
       reject_fwidth fw2;
       let pre = "(" ^ (if Float32? fw2 then "float32" else "float") ^ " " in
       pre ^ term (after ind pre) e1 ^ ")"
     | TInt _, TFloat fw2 ->
       reject_fwidth fw2;
       let pre = "(" ^ (if Float32? fw2 then "float32" else "float") ^ " " in
       pre ^ term (after ind pre) e1 ^ ")"
     | _, TInt sw2 ->
       let pre = "(" ^ int_conv sw2 ^ " " in
       pre ^ term (after ind pre) e1 ^ ")"
     | _ -> coerce ind e1 t)
  | ECoerce (e1, t) -> coerce ind e1 t
  | EOp ({ po_op = BufCreate _ }, [init; len]) ->
    if TRef? e.ty
    then let pre = "(ref " in pre ^ term (after ind pre) init ^ ")"
    else let pre = "(Array.create " in
         let pre = pre ^ index (after ind pre) len ^ " " in
         pre ^ term (after ind pre) init ^ ")"
  | EOp ({ po_op = BufRead }, [b; i]) ->
    if TRef? b.ty then "((" ^ term (ind ^ "  ") b ^ ").Value)"
    else let pre = "((" in
         let pre = pre ^ term (after ind pre) b ^ ").[" in
         pre ^ index (after ind pre) i ^ "])"
  | EOp ({ po_op = BufWrite }, [b; i; v]) ->
    if TRef? b.ty
    then let pre = "((" in
         let pre = pre ^ term (after ind pre) b ^ ").Value <- " in
         pre ^ term (after ind pre) v ^ ")"
    else let pre = "((" in
         let pre = pre ^ term (after ind pre) b ^ ").[" in
         let pre = pre ^ index (after ind pre) i ^ "] <- " in
         pre ^ term (after ind pre) v ^ ")"
  | EOp ({ po_op = BufFree }, [_]) -> "()"
  (* An empty array stands in for a null buffer; a [ref] cell is a .NET class,
     so it has a null of its own and needs no sentinel.  That is a genuine
     simplification over the OCaml backend, which has to encode one. *)
  | EOp ({ po_op = BufNull }, []) ->
    if TRef? e.ty then "(Unchecked.defaultof<" ^ ty e.ty ^ ">)" else "([||])"
  | EOp ({ po_op = BufIsNull }, [b]) ->
    if TRef? b.ty
    then let pre = "(isNull (box " in pre ^ term (after ind pre) b ^ "))"
    else let pre = "((Array.length " in
         pre ^ term (after ind pre) b ^ ") = 0)"
  | EOp ({ po_op = BufBlit }, [src; si; dst; di; len]) ->
    let pre = "(Array.blit " in
    let pre = pre ^ term (after ind pre) src ^ " " in
    let pre = pre ^ index (after ind pre) si ^ " " in
    let pre = pre ^ term (after ind pre) dst ^ " " in
    let pre = pre ^ index (after ind pre) di ^ " " in
    pre ^ index (after ind pre) len ^ ")"
  | EOp ({ po_op = BufSub }, _) ->
    "(failwith \"Custard: pointer arithmetic has no F# representation\")"
  (* Section 71.  F# has an array literal and no notion of static storage
     duration, so a static array is just an array, built where it is written. *)
  | EOp ({ po_op = BufLit }, elems) ->
    join_at ind "[| " "; " term elems ^ " |]"
  | EOp ({ po_op = BufUnconst }, [b]) -> term ind b
  (* Section 120.  F# spells a block comment the way OCaml does. *)
  | EOp ({ po_op = Commented (before, "") }, [{ e = EConst CUnit }]) ->
    "((* " ^ before ^ " *) ())"
  | EOp ({ po_op = Commented (before, after') }, [b]) ->
    let pre = "((* " ^ before ^ " *) " in
    pre ^ term (after ind pre) b ^ " (* " ^ after' ^ " *))"
  (* A shift's count is an [int] in F# whatever the value being shifted is,
     so it goes through the same conversion an array index does. *)
  | EOp (op, [a; b]) when is_shift op.po_op ->
    let s = if BShiftL? op.po_op then " <<< " else " >>> " in
    let pre = "(" in
    let pre = pre ^ term (after ind pre) a ^ s in
    pre ^ index (after ind pre) b ^ ")"
  | EOp (op, [a; b]) when Some? (binop (at_int_width op) op.po_op) ->
    (match op.po_ty with Some (PFloat fw) -> reject_fwidth fw | _ -> ());
    let pre = "(" in
    let pre = pre ^ term (after ind pre) a ^ " " ^
              Some?.v (binop (at_int_width op) op.po_op) ^ " " in
    pre ^ term (after ind pre) b ^ ")"
  | EOp (op, [a]) when (match op.po_ty with
                        | Some (PInt sw) -> Some? (w128_unop sw op.po_op)
                        | _ -> false) ->
    let sw = (match op.po_ty with Some (PInt sw) -> sw) in
    let pre = "(" ^ Some?.v (w128_unop sw op.po_op) ^ " " in
    pre ^ term (after ind pre) a ^ ")"
  | EOp (op, [a]) when Some? (unop (at_int_width op) op.po_op) ->
    (match op.po_ty with Some (PFloat fw) -> reject_fwidth fw | _ -> ());
    let pre = "(" ^ Some?.v (unop (at_int_width op) op.po_op) ^ " " in
    pre ^ term (after ind pre) a ^ ")"
  | EOp (op, args) -> no_operator op
  (* Section 122.6.  The node's own type is written into the [defaultof], so
     that nothing downstream has to infer it -- which at a type variable it
     could not. *)
  | EAny -> "(Unchecked.defaultof<" ^ ty e.ty ^ ">)"
  | EAbort s -> "(failwith \"" ^ escape s ^ "\")"
  | EWhile (c, body) ->
    let pre = "(while " in
    let hd = pre ^ term (after ind pre) c ^ " do\n" in
    (* F# wants the body strictly right of the [while], which is one past the
       paren; three is the smallest step that reads as one. *)
    let ind' = ind ^ "   " in
    hd ^ ind' ^ term ind' body ^ ")"
  | ERaise e1 -> let pre = "(raise " in pre ^ term (after ind pre) e1 ^ ")"
  | ETry (e1, brs) ->
    let pre = "(try " in
    let hd = pre ^ term (after ind pre) e1 ^ " with\n" in
    let ind' = ind ^ " " in
    hd ^ String.concat "\n" (List.map (case ind') brs) ^ ")"

(* An operator with no F# spelling at the arity it arrived with.  Every such
   case is a bug in this file rather than in the program, so it fails here
   rather than emitting something: the alternative is an [Unexpected symbol]
   from the F# compiler, about a line the reader did not write. *)
and no_operator (_op:prim_op) : ML string =
  failwith "Custard: an operator reached the F# backend at an arity it has \
            no spelling for"

(* A coercion changes no representation.  In .NET that is a box followed by an
   unbox: for a reference type both are identity, and for a value type the
   round trip is exact.  The unbox needs to know what it is unboxing to, and
   at a type variable it cannot be inferred, so the target type is written
   out.  [obj] on either side needs no cast in that direction. *)
and coerce (ind:string) (e1:expr) (t:cty) : ML string =
  match e1.ty, t with
  | TAny, TAny -> term ind e1
  | _, TAny -> let pre = "(box " in pre ^ term (after ind pre) e1 ^ ")"
  | a, b when erased_pun a b -> reject_coercion a b
  | TAny, _ ->
    let pre = "(unbox<" ^ ty t ^ "> " in pre ^ term (after ind pre) e1 ^ ")"
  | _ ->
    let pre = "(unbox<" ^ ty t ^ "> (box " in
    pre ^ term (after ind pre) e1 ^ "))"

(* An array index or a shift count: the IR value is a machine integer, and
   both positions want a .NET [int]. *)
and index (ind:string) (e:expr) : ML string =
  match e.e with
  (* A literal index is the common case, and wrapping [0] in a conversion
     would drown the output. *)
  | EConst (CInt (v, b, Some sw)) when not (is_w128 sw) -> int_lit_to_string v b
  | ECoerce (e1, _) -> index ind e1
  | ECast (e1, t) when (match e1.ty, t with
                        | TInt a, TInt b -> value_preserving a b
                        | _ -> false) -> index ind e1
  | _ ->
    let pre = "(int " in pre ^ term (after ind pre) e ^ ")"

(* The elements of a sequence, at [ind], without the enclosing parentheses.
   [let ... in] extends as far right as it can in F# just as it does in OCaml,
   so one pair around the whole run is exactly as many as are needed. *)
and stmts (ind:string) (e:expr) : ML string =
  match e.e with
  | ELet (x, _, e1, e2) ->
    let pre = "let " ^ fsharp_local x ^ " = " in
    pre ^ term (after ind pre) e1 ^ " in\n" ^ ind ^ stmts ind e2
  | ESeq (e1, e2) ->
    (* The discarded expression need not have type unit, and F# warns about
       that (warning 20), so one that is not goes through [ignore]. *)
    let s = term ind e1 in
    let s = if TUnit? e1.ty then s
            else let pre = "(ignore " in pre ^ term (after ind pre) e1 ^ ")" in
    s ^ ";\n" ^ ind ^ stmts ind e2
  | _ -> term ind e

and case (ind:string) (br:branch) : ML string =
  let p, g, b = br in
  let _, p, eqs = defer_ints 0 p in
  let conds = eqs |> List.map (fun (x, c) -> fsharp_local x ^ " = " ^ constant c) in
  let pre = ind ^ "| " ^ pattern p in
  let pre =
    match conds, g with
    | [], None -> pre ^ " -> "
    | _ ->
      let pre = pre ^ " when " ^ String.concat " && " conds in
      (match g with
       | None -> pre ^ " -> "
       | Some g ->
         let pre = pre ^ (if conds = [] then "" else " && ") in
         pre ^ term (spaces (col_after 0 pre)) g ^ " -> ") in
  (* [pre] already begins with [ind], so the body's column is measured from
     zero.  A body that would start past half the line goes on a line of its
     own instead: nested matches otherwise march to the right one pattern at a
     time, and the corpus reaches column 400 that way. *)
  let col = col_after 0 pre in
  if col > line_width / 2
  then pre ^ "\n" ^ ind ^ "    " ^ term (ind ^ "    ") b
  else pre ^ term (spaces col) b

(* -------------------------------------------------------------------- *)
(* Declarations                                                         *)
(* -------------------------------------------------------------------- *)

let params (ps : list string) : ML string =
  match ps with
  | [] -> ""
  | _ -> "<" ^ String.concat ", " (List.map (fun p -> "'" ^ fsharp_var p) ps) ^ ">"

let print_decl (first:bool) (d:decl) : ML (option string) =
  match d with
  | DType t ->
    if is_builtin_type t.dt_name || has_flag t.dt_flags Realized then None
    else
      let hd = (if first then "type " else "and ") ^
               fsharp_type_name t.dt_name ^ params t.dt_params in
      (match t.dt_body with
       (* F# has no way to declare a type and not say what it is, and an
          abstract one here means the representation was lost rather than
          hidden, so it stands for a value nothing looks inside. *)
       | TAbstract -> Some (hd ^ " = obj")
       | TAbbrev c -> Some (hd ^ " = " ^ ty c)
       | TRecord fs ->
         Some (hd ^ " = {\n" ^
               String.concat "" (List.map (fun (f, c) ->
                 "  " ^ fsharp_var f ^ " : " ^ ty c ^ ";\n") fs) ^ "}")
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
    Some ("exception " ^ fsharp_ctor_ident e.de_name ^
          (match e.de_args with
           | [] -> ""
           | args -> " of " ^ String.concat " * " (List.map ty args)))

  | DLet l ->
    (* Every binder and the result carry their type.  Custard knows all of
       them exactly, and writing them down turns a mistake in the extraction
       into an F# type error here rather than a puzzle at the use site -- and
       F#'s inference, unlike OCaml's, frequently needs them anyway. *)
    let bs = String.concat "" (List.map (fun b ->
               " (" ^ fsharp_local b.b_name ^ " : " ^ ty b.b_ty ^ ")") l.dl_binders) in
    let rc = if l.dl_flags |> List.existsb Rec? then "rec " else "" in
    let kw = if first then "let " ^ rc else "and " in
    let hd = kw ^ fsharp_value_name l.dl_name ^ bs ^ " : " ^ ty l.dl_ret ^ " =\n  " in
    Some (hd ^ term "  " l.dl_body)

(* -------------------------------------------------------------------- *)
(* Rejections                                                           *)
(* -------------------------------------------------------------------- *)

(* Section 122.8.  The names the support library implements, as
   {!string_of_name} spells them.  Everything here is a symbol with no F*
   definition whose realization is a line or two of F#; the list is the
   backend's whole library surface, and it is short because .NET supplies
   directly almost everything [ulib/ml] has to supply by hand. *)
let supported_realizations : list (string & string) = [
  (* Section 122.13.  [Prims.int] is [bigint], so every one of these is a
     .NET operator already; they are named here only because F* declares them
     rather than defining them.  The division and remainder round toward
     zero, which is what Prims specifies and what [System.Numerics.BigInteger]
     does. *)
  "Prims.op_Plus",                "Prims.op_Plus";
  "Prims.op_Minus",               "Prims.op_Minus";
  "Prims.op_Star",                "Prims.op_Star";
  "Prims.op_Slash",               "Prims.op_Slash";
  "Prims.op_Percent",             "Prims.op_Percent";
  "Prims.op_Minus_Minus",         "Prims.op_Minus_Minus";
  "Prims.op_Less",                "Prims.op_Less";
  "Prims.op_Less_Equals",         "Prims.op_Less_Equals";
  "Prims.op_Greater",             "Prims.op_Greater";
  "Prims.op_Greater_Equals",      "Prims.op_Greater_Equals";
  "Prims.abs",                    "Prims.abs";
  "Prims.pow2",                   "Prims.pow2";
  "Prims.strcat",                 "Prims.strcat";
  "Prims.op_Hat",                 "Prims.strcat";
  "Prims.string_of_bool",         "Prims.string_of_bool";
  "Prims.string_of_int",          "Prims.string_of_int";
  (* Section 122.13.  [Prims.list] is F#'s own list, so this module is the
     one place where the OCaml realization has a line-for-line F#
     counterpart: [FStar.List.Tot.Base] is realized rather than compiled
     because F* declares no [decreases] that OCaml would accept, not because
     it needs anything OCaml has.  The whole module is here rather than the
     part the corpus happens to use, because the next program to want one of
     these would otherwise be rejected for a function that is one line. *)
  "FStar.List.Tot.Base.isEmpty",               "FStar_List_Tot_Base.isEmpty";
  "FStar.List.Tot.Base.hd",                    "FStar_List_Tot_Base.hd";
  "FStar.List.Tot.Base.tail",                  "FStar_List_Tot_Base.tail";
  "FStar.List.Tot.Base.tl",                    "FStar_List_Tot_Base.tl";
  "FStar.List.Tot.Base.last",                  "FStar_List_Tot_Base.last";
  "FStar.List.Tot.Base.init",                  "FStar_List_Tot_Base.init";
  "FStar.List.Tot.Base.length",                "FStar_List_Tot_Base.length";
  "FStar.List.Tot.Base.nth",                   "FStar_List_Tot_Base.nth";
  "FStar.List.Tot.Base.index",                 "FStar_List_Tot_Base.index";
  "FStar.List.Tot.Base.count",                 "FStar_List_Tot_Base.count";
  "FStar.List.Tot.Base.rev_acc",               "FStar_List_Tot_Base.rev_acc";
  "FStar.List.Tot.Base.rev",                   "FStar_List_Tot_Base.rev";
  "FStar.List.Tot.Base.append",                "FStar_List_Tot_Base.append";
  "FStar.List.Tot.Base.snoc",                  "FStar_List_Tot_Base.snoc";
  "FStar.List.Tot.Base.flatten",               "FStar_List_Tot_Base.flatten";
  "FStar.List.Tot.Base.map",                   "FStar_List_Tot_Base.map";
  "FStar.List.Tot.Base.mapi",                  "FStar_List_Tot_Base.mapi";
  "FStar.List.Tot.Base.concatMap",             "FStar_List_Tot_Base.concatMap";
  "FStar.List.Tot.Base.fold_left",             "FStar_List_Tot_Base.fold_left";
  "FStar.List.Tot.Base.fold_right",            "FStar_List_Tot_Base.fold_right";
  "FStar.List.Tot.Base.fold_left2",            "FStar_List_Tot_Base.fold_left2";
  "FStar.List.Tot.Base.mem",                   "FStar_List_Tot_Base.mem";
  "FStar.List.Tot.Base.contains",              "FStar_List_Tot_Base.contains";
  "FStar.List.Tot.Base.existsb",               "FStar_List_Tot_Base.existsb";
  "FStar.List.Tot.Base.find",                  "FStar_List_Tot_Base.find";
  "FStar.List.Tot.Base.filter",                "FStar_List_Tot_Base.filter";
  "FStar.List.Tot.Base.for_all",               "FStar_List_Tot_Base.for_all";
  "FStar.List.Tot.Base.collect",               "FStar_List_Tot_Base.collect";
  "FStar.List.Tot.Base.tryFind",               "FStar_List_Tot_Base.tryFind";
  "FStar.List.Tot.Base.tryPick",               "FStar_List_Tot_Base.tryPick";
  "FStar.List.Tot.Base.choose",                "FStar_List_Tot_Base.choose";
  "FStar.List.Tot.Base.partition",             "FStar_List_Tot_Base.partition";
  "FStar.List.Tot.Base.noRepeats",             "FStar_List_Tot_Base.noRepeats";
  "FStar.List.Tot.Base.assoc",                 "FStar_List_Tot_Base.assoc";
  "FStar.List.Tot.Base.split",                 "FStar_List_Tot_Base.split";
  "FStar.List.Tot.Base.unzip",                 "FStar_List_Tot_Base.unzip";
  "FStar.List.Tot.Base.unzip3",                "FStar_List_Tot_Base.unzip3";
  "FStar.List.Tot.Base.splitAt",               "FStar_List_Tot_Base.splitAt";
  "FStar.List.Tot.Base.unsnoc",                "FStar_List_Tot_Base.unsnoc";
  "FStar.List.Tot.Base.split3",                "FStar_List_Tot_Base.split3";
  "FStar.List.Tot.Base.bool_of_compare",       "FStar_List_Tot_Base.bool_of_compare";
  "FStar.List.Tot.Base.compare_of_bool",       "FStar_List_Tot_Base.compare_of_bool";
  "FStar.List.Tot.Base.sortWith",              "FStar_List_Tot_Base.sortWith";
  "FStar.List.Tot.Base.subset",                "FStar_List_Tot_Base.subset";
  "FStar.List.Tot.Base.list_unref",            "FStar_List_Tot_Base.list_unref";
  "FStar.List.Tot.Base.list_ref",              "FStar_List_Tot_Base.list_ref";
  "FStar.List.Tot.Base.list_refb",             "FStar_List_Tot_Base.list_refb";
  "FStar.List.Tot.Base.op_At",   "FStar_List_Tot_Base.append";

  (* The machine-integer printers.  [FStar.UIntN.t] is .NET's own [uintN],
     so these are [ToString] and nothing else; they are declared rather than
     defined because the F* side has no notion of a decimal expansion. *)
  "FStar.UInt8.to_string",        "Prims.string_of_int8";
  "FStar.UInt16.to_string",       "Prims.string_of_int16";
  "FStar.UInt32.to_string",       "Prims.string_of_int32";
  "FStar.UInt64.to_string",       "Prims.string_of_int64";
  "FStar.Int8.to_string",         "Prims.string_of_sint8";
  "FStar.Int16.to_string",        "Prims.string_of_sint16";
  "FStar.Int32.to_string",        "Prims.string_of_sint32";
  "FStar.Int64.to_string",        "Prims.string_of_sint64";
  "FStar.IO.print_newline",       "FStar_IO.print_newline";
  "FStar.IO.print_string",        "FStar_IO.print_string";
  "FStar.IO.print_uint8",         "FStar_IO.print_uint8";
  "FStar.IO.print_uint16",        "FStar_IO.print_uint16";
  "FStar.IO.print_uint32",        "FStar_IO.print_uint32";
  "FStar.IO.print_uint64",        "FStar_IO.print_uint64";
  "FStar.IO.print_uint8_dec",     "FStar_IO.print_uint8_dec";
  "FStar.IO.print_uint16_dec",    "FStar_IO.print_uint16_dec";
  "FStar.IO.print_uint32_dec",    "FStar_IO.print_uint32_dec";
  "FStar.IO.print_uint64_dec",    "FStar_IO.print_uint64_dec";
  "FStar.IO.print_uint8_hex_pad", "FStar_IO.print_uint8_hex_pad";
  "FStar.IO.print_uint16_hex_pad","FStar_IO.print_uint16_hex_pad";
  "FStar.IO.print_uint32_hex_pad","FStar_IO.print_uint32_hex_pad";
  "FStar.IO.print_uint64_hex_pad","FStar_IO.print_uint64_hex_pad";
  "FStar.IO.print_uint8_dec_pad", "FStar_IO.print_uint8_dec_pad";
  "FStar.IO.print_uint16_dec_pad","FStar_IO.print_uint16_dec_pad";
  "FStar.IO.print_uint32_dec_pad","FStar_IO.print_uint32_dec_pad";
  "FStar.IO.print_uint64_dec_pad","FStar_IO.print_uint64_dec_pad";
  "FStar.IO.debug_print_string",  "FStar_IO.debug_print_string";

  (* [FStar.Char] and [FStar.String] over .NET's own [char] and [string].  See
     {!builtin_type}: the representation is UTF-16 rather than a sequence of
     code points, which is the reading every one of these is written against. *)
  "FStar.Char.lowercase",         "FStar_Char.lowercase";
  "FStar.Char.uppercase",         "FStar_Char.uppercase";
  "FStar.Char.int_of_char",       "FStar_Char.int_of_char";
  "FStar.Char.char_of_int",       "FStar_Char.char_of_int";
  "FStar.Char.u32_of_char",       "FStar_Char.u32_of_char";
  "FStar.Char.char_of_u32",       "FStar_Char.char_of_u32";
  "FStar.String.make",            "FStar_String.make";
  "FStar.String.strcat",          "FStar_String.strcat";
  "FStar.String.op_Hat",          "FStar_String.strcat";
  "FStar.String.split",           "FStar_String.split";
  "FStar.String.compare",         "FStar_String.compare";
  "FStar.String.concat",          "FStar_String.concat";
  "FStar.String.length",          "FStar_String.length";
  "FStar.String.strlen",          "FStar_String.length";
  "FStar.String.substring",       "FStar_String.substring";
  "FStar.String.sub",             "FStar_String.substring";
  "FStar.String.get",             "FStar_String.get";
  "FStar.String.index",           "FStar_String.get";
  "FStar.String.collect",         "FStar_String.collect";
  "FStar.String.lowercase",       "FStar_String.lowercase";
  "FStar.String.uppercase",       "FStar_String.uppercase";
  "FStar.String.index_of",        "FStar_String.index_of";
  "FStar.String.list_of_string",  "FStar_String.list_of_string";
  "FStar.String.string_of_list",  "FStar_String.string_of_list";
  "FStar.String.string_of_char",  "FStar_String.string_of_char";

  (* [FStar.All]: the two that end a program, and the exception handler. *)
  "FStar.All.failwith",           "FStar_All.failwith";
  "FStar.All.exit",               "FStar_All.exit";
  "FStar.All.try_with",           "FStar_All.try_with";
  "FStar.All.pipe_right",         "FStar_All.pipe_right";
  "FStar.All.pipe_left",          "FStar_All.pipe_left";

  (* [FStar.List] is [FStar.List.Tot.Base] with an [ML] effect on the
     higher-order arguments, which in F# is no difference at all: the
     realizations are the same .NET functions under the other name.  Only
     [nth] differs, returning the element rather than an [option]. *)
  "FStar.List.hd",                "FStar_List_Tot_Base.hd";
  "FStar.List.tl",                "FStar_List_Tot_Base.tl";
  "FStar.List.tail",              "FStar_List_Tot_Base.tl";
  "FStar.List.last",              "FStar_List_Tot_Base.last";
  "FStar.List.init",              "FStar_List_Tot_Base.init";
  "FStar.List.length",            "FStar_List_Tot_Base.length";
  "FStar.List.rev",               "FStar_List_Tot_Base.rev";
  "FStar.List.append",            "FStar_List_Tot_Base.append";
  "FStar.List.op_At",             "FStar_List_Tot_Base.append";
  "FStar.List.flatten",           "FStar_List_Tot_Base.flatten";
  "FStar.List.mem",               "FStar_List_Tot_Base.mem";
  "FStar.List.contains",          "FStar_List_Tot_Base.contains";
  "FStar.List.isEmpty",           "FStar_List_Tot_Base.isEmpty";
  "FStar.List.split",             "FStar_List_Tot_Base.split";
  "FStar.List.unzip",             "FStar_List_Tot_Base.unzip";
  "FStar.List.unzip3",            "FStar_List_Tot_Base.unzip3";
  "FStar.List.splitAt",           "FStar_List_Tot_Base.splitAt";
  "FStar.List.nth",               "FStar_List.nth";
  "FStar.List.iter",              "FStar_List.iter";
  "FStar.List.iteri",             "FStar_List.iteri";
  "FStar.List.map",               "FStar_List_Tot_Base.map";
  "FStar.List.mapi",              "FStar_List_Tot_Base.mapi";
  "FStar.List.collect",           "FStar_List_Tot_Base.collect";
  "FStar.List.concatMap",         "FStar_List_Tot_Base.concatMap";
  "FStar.List.fold_left",         "FStar_List_Tot_Base.fold_left";
  "FStar.List.fold_right",        "FStar_List_Tot_Base.fold_right";
  "FStar.List.fold_left2",        "FStar_List_Tot_Base.fold_left2";
  "FStar.List.filter",            "FStar_List_Tot_Base.filter";
  "FStar.List.for_all",           "FStar_List_Tot_Base.for_all";
  "FStar.List.existsb",           "FStar_List_Tot_Base.existsb";
  "FStar.List.find",              "FStar_List_Tot_Base.find";
  "FStar.List.tryFind",           "FStar_List_Tot_Base.tryFind";
  "FStar.List.tryPick",           "FStar_List_Tot_Base.tryPick";
  "FStar.List.choose",            "FStar_List_Tot_Base.choose";
  "FStar.List.partition",         "FStar_List_Tot_Base.partition";
  "FStar.List.assoc",             "FStar_List_Tot_Base.assoc";
  "FStar.List.sortWith",          "FStar_List_Tot_Base.sortWith";
]

let supported_realization (n:name) : ML (option string) =
  if Some? n.spec then None
  else supported_realizations
       |> List.tryPick (fun (k, v) ->
            if k = string_of_name n then Some v else None)

(* Section 122.9.  A symbol with no F* definition, no [@@custard_extern]
   target and no entry in the support library is a reference to a
   hand-written OCaml realization in [ulib/ml].  There is no F# counterpart of
   those, and there is not going to be a useful one: [FStarC.Util] alone is
   several thousand lines of OCaml against OCaml's own runtime.

   Emitting the name anyway -- which is what the OCaml backend does, because
   there it resolves -- would produce a file that does not compile, and the
   diagnostic would come from the F# compiler, about generated code, naming a
   module the reader never wrote.  So it is refused here, where the F* name
   and the reason are both still in hand. *)
let reject_unrealized (p:program) : ML unit =
  p |> List.iter (fun d ->
    match d with
    | DExternal e when None? e.dx_target && None? (supported_realization e.dx_name) ->
      let m = String.concat "." e.dx_name.ns in
      E.raise_error0 E.Error_CustardNoFSharpRealization [
        text ("Custard: " ^ string_of_name e.dx_name ^ " has no F* definition \
               and no F# realization.");
        text ("It is declared by " ^ m ^ ", which F* realizes with \
               hand-written OCaml in ulib/ml.  The F# backend compiles to \
               .NET's own types rather than to that library, so it accepts \
               the programs the C backend accepts and not the ones the OCaml \
               backend accepts (section 122).");
        text "Give it a target with [@@custard_extern \"...\"] and supply \
              that name yourself, or extract this program with \
              --custard_backend OCaml." ]
    | _ -> ())

(* A realized *type* is the same situation one level up.  The ones .NET
   already has -- the tuples, [option], [list] -- are {!builtin_type}s and
   never reach here; what is left is a type whose shape lives in an OCaml
   file. *)
let reject_realized_types (p:program) : ML unit =
  p |> List.iter (fun d ->
    match d with
    | DType t when has_flag t.dt_flags Realized
                && not (is_builtin_type t.dt_name)
                && not (is_tuple_type t.dt_name) ->
      E.raise_error0 E.Error_CustardNoFSharpRealization [
        text ("Custard: the type " ^ string_of_name t.dt_name ^ " is realized \
               by hand-written OCaml and has no F# realization.");
        text ("Its declaration says what shape the type has, but not what it \
               is: the definition is in ulib/ml, and there is no F# \
               counterpart of that library (section 122.9).");
        text "Extract this program with --custard_backend OCaml, or keep it \
              to the fragment the C backend compiles." ]
    | _ -> ())

(* Sections 69 and 70.2.  Two C++ constructions with no counterpart here. *)
let reject_target_only_types (p:program) : ML unit =
  p |> List.iter (fun d ->
    match d with
    | DType t ->
      t.dt_flags |> List.iter (fun f ->
        match f with
        | Extern (Some target, _) when is_template (template_of_string target) ->
          E.raise_error0 E.Error_CustardBadTemplateArg [
            text ("Custard: the external type " ^ string_of_name t.dt_name ^
                  " has a template target, and templates reached the F# \
                   backend.");
            text ("Its target spelling [" ^ target ^ "] has a placeholder for \
                   an argument, so two instantiations of it are two different \
                   target types; F# has no such construction.  Section 69 is \
                   a C-backend feature (--custard_backend C).") ]
        | CReference ->
          E.raise_error0 E.Error_CustardBadReference [
            text ("Custard: the type " ^ string_of_name t.dt_name ^
                  " is [@@custard_c_reference], and reference bindings \
                   reached the F# backend.");
            text "The attribute says that values of the type are handles, so \
                  a binding of one has to alias rather than copy, which is \
                  C++ [T &x = ...] and F# has no way to spell.  Section 70.2 \
                  is a C-backend feature (--custard_backend C)." ]
        | _ -> ())
    | _ -> ())

(* Section 122.11.  F# generalizes a [let] that is not a function only when it
   can see that doing so is sound -- the value restriction -- so a top-level
   definition with no parameters whose type still mentions a type variable is
   rejected by the F# compiler, at the definition, with a message about a
   rule the reader has no reason to have heard of.

   Custard monomorphizes, so this is rare by construction: what survives is a
   value in a [Poly] position that nothing ever specialized.  It is refused
   here, naming the value and what to do about it, rather than downstream. *)
let rec mentions_tyvar (t:cty) : ML bool =
  match t with
  | TVar _ -> true
  | TArrow (a, _, b) -> mentions_tyvar a || mentions_tyvar b
  | TTuple ts -> ts |> List.existsb mentions_tyvar
  | TBuf t | TRef t | TInline t -> mentions_tyvar t
  | TApp (_, args) -> args |> List.existsb mentions_tyvar
  | _ -> false

let reject_generic_values (p:program) : ML unit =
  p |> List.iter (fun d ->
    match d with
    | DLet l when Nil? l.dl_binders && mentions_tyvar l.dl_ret ->
      E.raise_error0 E.Error_CustardUnrepresentableValue [
        text ("Custard: " ^ string_of_name l.dl_name ^ " is a top-level value \
               with no parameters whose type " ^ ty l.dl_ret ^ " is still \
               polymorphic.");
        text "F#'s value restriction does not generalize such a definition, \
              so it cannot be written at all (section 122.11).  Nothing in \
              this program specialized it, which means nothing uses it at a \
              type either.";
        text "Give it a parameter, specialize it at the type it is wanted at, \
              or extract with --custard_backend OCaml." ]
    | _ -> ())

(* -------------------------------------------------------------------- *)
(* Tables and assembly                                                  *)
(* -------------------------------------------------------------------- *)

let build_tables (p:program) : ML unit =
  let tbl = SMap.create 50 in
  let tups = SMap.create 20 in
  let nul = SMap.create 50 in
  let recs : SMap.t int = SMap.create 100 in
  let labels : SMap.t int = SMap.create 100 in
  p |> List.iter (fun d ->
    match d with
    | DExternal e ->
      (match e.dx_target with
       | Some t -> SMap.add tbl (string_of_name e.dx_name) t
       | None ->
         (match supported_realization e.dx_name with
          | Some t -> SMap.add tbl (string_of_name e.dx_name) t
          (* Refused by {!reject_unrealized} before anything is printed. *)
          | None -> ()))
    | DExn e ->
      if Nil? e.de_args then SMap.add nul (string_of_name e.de_name) ()
    | DType t ->
      (match t.dt_body with
       | TVariant cs ->
         cs |> List.iter (fun (cn, fs) ->
           if Nil? fs then SMap.add nul (string_of_name cn) ());
         (* [tupleN] is the one realized type whose F# form is syntax rather
            than a name; record its arity under every name it is reached by. *)
         if is_tuple_type t.dt_name then
           (match cs with
            | [(cn, fs)] ->
              SMap.add tups (string_of_name t.dt_name) (List.length fs);
              SMap.add tups (string_of_name cn) (List.length fs)
            | _ -> ())
       | TRecord fs ->
         if is_tuple_type t.dt_name then
           SMap.add tups (string_of_name t.dt_name) (List.length fs);
         SMap.add recs (string_of_name t.dt_name) (List.length t.dt_params);
         fs |> List.iter (fun (f, _) ->
           let k = label_key t.dt_name f in
           SMap.add labels k (1 + (match SMap.try_find labels k with
                                   | Some i -> i
                                   | None -> 0)))
       | _ -> ())
    | _ -> ());
  externals := tbl;
  tuples := tups;
  nullary := nul;
  record_params := recs;
  record_labels := labels

(* Section 122.2.  The warnings turned off here are the ones that are about
   the *shape* of generated code rather than about anything that could be
   wrong with it: a match the extractor knows is exhaustive, a recursive
   binding it knows is well founded, a name that happens to start with a
   capital.  Three are deliberately left on.  Warning 58 is the indentation
   one, and it is the one this backend exists to get right, so silencing it
   would remove the only check that it did.  Warning 20 catches a discarded
   non-unit result, which {!stmts} handles with [ignore] and which would
   otherwise mean a dropped effect.  Warning 3370 catches the deprecated [!]
   on a reference cell, which this backend never emits. *)
let header (m:string) : string =
  "// Generated by F* Custard extraction. Do not edit.\n\
   module " ^ m ^ "\n\
   #nowarn \"25\" \"26\" \"40\" \"49\" \"64\" \"1182\" \"3220\"\n\
   open FStarCustard\n"

let group_of (d:decl) : ML (option (list string)) =
  match decl_flags d |> List.tryFind Rec? with
  | Some (Rec ns) -> Some (List.map string_of_name ns)
  | _ -> None

let print_decls (p:program) : ML (list string) =
  let prev : ref (option (list string)) = mk_ref None in
  p |> List.collect (fun d ->
    let g = group_of d in
    let first = None? g || g <> !prev in
    match print_decl first d with
    | Some s -> prev := g; [s]
    | None -> [])

let entrypoints (p:program) : ML (list dlet) =
  p |> List.collect (fun d ->
    match d with
    | DLet l when l.dl_flags |> List.existsb Entrypoint?
               && l.dl_binders |> List.for_all (fun b -> TUnit? b.b_ty) -> [l]
    | _ -> [])

(* Custard compiles standalone programs (section 4.4), so the entry points are
   called from the generated code itself.  An entry point returning a machine
   integer is the process exit status, exactly as it is on the C backend --
   the two must agree, or the same program tested on both reports success on
   one and failure on the other.

   .NET names its entry point with an attribute rather than by position, and
   requires it to be the last declaration of the last file. *)
let entry_calls (p:program) : ML (list string) =
  match entrypoints p with
  | [] -> []
  | ls ->
    let body =
      ls |> List.map (fun l ->
        let args = String.concat " " (List.map (fun _ -> "()") l.dl_binders) in
        let call = "(" ^ fsharp_value_name l.dl_name ^ " " ^ args ^ ")" in
        match l.dl_ret with
        | TInt _ -> "  (int " ^ call ^ ")"
        | TUnit -> "  " ^ call ^ "\n  0"
        | _ -> "  (ignore " ^ call ^ ")\n  0") in
    ["[<EntryPoint>]\nlet main (_argv : string[]) : int =\n" ^
     String.concat "\n" body]

let assemble (m:string) (ds : list string) : ML string =
  header m ^ "\n" ^ String.concat "\n\n" ds ^ "\n"

let reserve_top (p:program) : ML unit =
  reserved_top := p |> List.collect (fun d ->
    match d with
    | DLet l -> [fsharp_value_name l.dl_name]
    | DExternal e -> [fsharp_value_name e.dx_name]
    | _ -> [])

let print_program (stem:string) (p:program) : ML string =
  reject_target_only_types p;
  reject_realized_types p;
  reject_unrealized p;
  reject_generic_values p;
  build_tables p;
  reserve_top p;
  assemble (module_name_of_unit stem) (print_decls p @ entry_calls p)

(* -------------------------------------------------------------------- *)
(* The project                                                          *)
(* -------------------------------------------------------------------- *)

(* Section 122.8.  The support library, written out beside the program rather
   than installed anywhere.

   It is *here*, as text, and not a file in [ulib/fs] that the driver copies,
   for one reason: the output directory has to build with nothing else
   present.  That is the property that makes the C backend's output shippable
   -- a [.c] and a [.h] and no include path to get right -- and it is worth
   more than the small amount of tidiness lost by carrying sixty lines of F#
   in the printer that emits F#.  A search for an installed file is also one
   more thing that can be absent, and its absence would surface as a broken
   build of generated code rather than as a diagnostic.

   It is short, and it is meant to stay short.  Two of its entries exist
   because F# has no way to spell the conversion inline ({!int_conv}); the
   rest are [FStar.IO], which is what a standalone program needs to say
   anything at all.  A realization is added here when a program needs it, and
   {!supported_realizations} is the list of what that is so far. *)
let runtime_source : string =
  "// Generated by F* Custard extraction. Do not edit.\n\
   //\n\
   // The Custard F# support library.  See section 122.8 of\n\
   // doc/ref/custard.md.  It holds exactly what .NET does not already\n\
   // supply under the name F* declares: the Prims operators on bigint, two\n\
   // 128-bit conversions that have no inline spelling, and FStar.IO.\n\
   module FStarCustard\n\
   \n\
   open System\n\
   \n\
   // A widening conversion into a 128-bit integer has to know the sign of\n\
   // what it came from -- FStar.Int.Cast.Full specifies the result mod\n\
   // 2^128, so a negative source sets the high bits -- and F# resolves an\n\
   // op_Implicit on the argument type, which at a type variable it cannot\n\
   // see.  These two do the resolving with an explicit conversion through\n\
   // the widest same-signed type, which is exact in both directions.\n\
   let inline toU128 (x : ^a) : UInt128 =\n\
   \x20 UInt128.CreateTruncating x\n\
   \n\
   let inline toI128 (x : ^a) : Int128 =\n\
   \x20 Int128.CreateTruncating x\n\
   \n\
   // F#'s ~~~ resolves against op_LogicalNot, which the 128-bit types do not\n\
   // define even though they define every other bitwise operator.  The\n\
   // complement of x is x xor all-ones, and for a signed one it is -x - 1.\n\
   let notU128 (x : UInt128) : UInt128 = UInt128.MaxValue ^^^ x\n\
   let notI128 (x : Int128) : Int128 = -x - Int128.One\n\
   \n\
   // Section 122.13.  Prims.int is bigint, so these are the .NET operators\n\
   // under the names F* declares for them.\n\
   module Prims =\n\
   \x20 let op_Plus (x : bigint) (y : bigint) : bigint = x + y\n\
   \x20 let op_Minus (x : bigint) (y : bigint) : bigint = x - y\n\
   \x20 let op_Star (x : bigint) (y : bigint) : bigint = x * y\n\
   \x20 let op_Slash (x : bigint) (y : bigint) : bigint = x / y\n\
   \x20 let op_Percent (x : bigint) (y : bigint) : bigint = x % y\n\
   \x20 let op_Minus_Minus (x : bigint) : bigint = -x\n\
   \x20 let op_Less (x : bigint) (y : bigint) : bool = x < y\n\
   \x20 let op_Less_Equals (x : bigint) (y : bigint) : bool = x <= y\n\
   \x20 let op_Greater (x : bigint) (y : bigint) : bool = x > y\n\
   \x20 let op_Greater_Equals (x : bigint) (y : bigint) : bool = x >= y\n\
   \x20 let abs (x : bigint) : bigint = if x < 0I then -x else x\n\
   \x20 let pow2 (n : bigint) : bigint =\n\
   \x20   System.Numerics.BigInteger.Pow (2I, int n)\n\
   \x20 let strcat (x : string) (y : string) : string = x + y\n\
   \x20 let string_of_bool (b : bool) : string = if b then \"true\" else \"false\"\n\
   \x20 let string_of_int (x : bigint) : string = x.ToString ()\n\
   \x20 let string_of_int8 (x : uint8) : string = x.ToString ()\n\
   \x20 let string_of_int16 (x : uint16) : string = x.ToString ()\n\
   \x20 let string_of_int32 (x : uint32) : string = x.ToString ()\n\
   \x20 let string_of_int64 (x : uint64) : string = x.ToString ()\n\
   \x20 let string_of_sint8 (x : int8) : string = x.ToString ()\n\
   \x20 let string_of_sint16 (x : int16) : string = x.ToString ()\n\
   \x20 let string_of_sint32 (x : int32) : string = x.ToString ()\n\
   \x20 let string_of_sint64 (x : int64) : string = x.ToString ()\n\
   \n\
   // Section 122.13.  Prims.list is F#'s own list, so FStar.List.Tot.Base is a\n\
   // line-for-line translation of the OCaml realization rather than anything\n\
   // this backend had to invent.\n\
   module FStar_List_Tot_Base =\n\
   \x20 let isEmpty (l : 'a list) : bool = List.isEmpty l\n\
   \x20 let hd (l : 'a list) : 'a = List.head l\n\
   \x20 let tail (l : 'a list) : 'a list = List.tail l\n\
   \x20 let tl (l : 'a list) : 'a list = List.tail l\n\
   \x20 let last (l : 'a list) : 'a = List.last l\n\
   \x20 let init (l : 'a list) : 'a list = List.truncate (List.length l - 1) l\n\
   \x20 let length (l : 'a list) : bigint = bigint (List.length l)\n\
   \x20 let nth (l : 'a list) (i : bigint) : 'a option =\n\
   \x20   if i < 0I || i >= bigint (List.length l) then None\n\
   \x20   else Some (List.item (int i) l)\n\
   \x20 let index (l : 'a list) (i : bigint) : 'a = List.item (int i) l\n\
   \x20 let count (x : 'a) (l : 'a list) : bigint =\n\
   \x20   bigint (List.length (List.filter (fun y -> y = x) l))\n\
   \x20 let rev_acc (l : 'a list) (r : 'a list) : 'a list = List.rev l @ r\n\
   \x20 let rev (l : 'a list) : 'a list = List.rev l\n\
   \x20 let append (l : 'a list) (r : 'a list) : 'a list = l @ r\n\
   \x20 let snoc ((l : 'a list), (x : 'a)) : 'a list = l @ [x]\n\
   \x20 let flatten (l : 'a list list) : 'a list = List.concat l\n\
   \x20 let map (f : 'a -> 'b) (l : 'a list) : 'b list = List.map f l\n\
   \x20 let mapi (f : bigint -> 'a -> 'b) (l : 'a list) : 'b list =\n\
   \x20   List.mapi (fun i x -> f (bigint i) x) l\n\
   \x20 let concatMap (f : 'a -> 'b list) (l : 'a list) : 'b list = List.collect f l\n\
   \x20 let fold_left (f : 'a -> 'b -> 'a) (z : 'a) (l : 'b list) : 'a =\n\
   \x20   List.fold f z l\n\
   \x20 let fold_right (f : 'a -> 'b -> 'b) (l : 'a list) (z : 'b) : 'b =\n\
   \x20   List.foldBack f l z\n\
   \x20 let fold_left2 (f : 'a -> 'b -> 'c -> 'a) (z : 'a) (l : 'b list)\n\
   \x20                (m : 'c list) : 'a = List.fold2 f z l m\n\
   \x20 let mem (x : 'a) (l : 'a list) : bool = List.contains x l\n\
   \x20 let contains (x : 'a) (l : 'a list) : bool = List.contains x l\n\
   \x20 let existsb (f : 'a -> bool) (l : 'a list) : bool = List.exists f l\n\
   \x20 let find (f : 'a -> bool) (l : 'a list) : 'a option = List.tryFind f l\n\
   \x20 let filter (f : 'a -> bool) (l : 'a list) : 'a list = List.filter f l\n\
   \x20 let for_all (f : 'a -> bool) (l : 'a list) : bool = List.forall f l\n\
   \x20 let collect (f : 'a -> 'b list) (l : 'a list) : 'b list = List.collect f l\n\
   \x20 let tryFind (f : 'a -> bool) (l : 'a list) : 'a option = List.tryFind f l\n\
   \x20 let tryPick (f : 'a -> 'b option) (l : 'a list) : 'b option = List.tryPick f l\n\
   \x20 let choose (f : 'a -> 'b option) (l : 'a list) : 'b list = List.choose f l\n\
   \x20 let partition (f : 'a -> bool) (l : 'a list) : 'a list * 'a list =\n\
   \x20   List.partition f l\n\
   \x20 let noRepeats (l : 'a list) : bool =\n\
   \x20   List.length (List.distinct l) = List.length l\n\
   \x20 let assoc (x : 'a) (l : ('a * 'b) list) : 'b option =\n\
   \x20   List.tryPick (fun (k, v) -> if k = x then Some v else None) l\n\
   \x20 let split (l : ('a * 'b) list) : 'a list * 'b list = List.unzip l\n\
   \x20 let unzip (l : ('a * 'b) list) : 'a list * 'b list = List.unzip l\n\
   \x20 let unzip3 (l : ('a * 'b * 'c) list) : 'a list * 'b list * 'c list =\n\
   \x20   List.unzip3 l\n\
   \x20 let splitAt (n : bigint) (l : 'a list) : 'a list * 'a list =\n\
   \x20   List.splitAt (int n) l\n\
   \x20 let unsnoc (l : 'a list) : 'a list * 'a =\n\
   \x20   (List.truncate (List.length l - 1) l, List.last l)\n\
   \x20 let split3 (l : 'a list) (i : bigint) : 'a list * 'a * 'a list =\n\
   \x20   let a, b = List.splitAt (int i) l\n\
   \x20   (a, List.head b, List.tail b)\n\
   \x20 let bool_of_compare (f : 'a -> 'a -> bigint) (x : 'a) (y : 'a) : bool =\n\
   \x20   f x y > 0I\n\
   \x20 let compare_of_bool (r : 'a -> 'a -> bool) (x : 'a) (y : 'a) : bigint =\n\
   \x20   if r x y then 1I elif x = y then 0I else -1I\n\
   \x20 let sortWith (f : 'a -> 'a -> bigint) (l : 'a list) : 'a list =\n\
   \x20   List.sortWith (fun x y -> int (f x y)) l\n\
   \x20 let subset (l : 'a list) (r : 'a list) : bool =\n\
   \x20   List.forall (fun x -> List.contains x r) l\n\
   \x20 let list_unref (l : 'a list) : 'a list = l\n\
   \x20 let list_ref (l : 'a list) : 'a list = l\n\
   \x20 let list_refb (l : 'a list) : 'a list = l\n\
   \n\
   module FStar_IO =\n\
   \x20 let private w (s : string) : unit =\n\
   \x20   Console.Out.Write s\n\
   \x20   Console.Out.Flush ()\n\
   \n\
   \x20 let print_newline (_ : unit) : unit = w \"\\n\"\n\
   \x20 let print_string (s : string) : unit = w s\n\
   \x20 let debug_print_string (s : string) : bool = w s; false\n\
   \n\
   \x20 let private hex (v : uint64) : string = \"0x\" + v.ToString \"x\"\n\
   \x20 let private hexpad (n : int) (v : uint64) : string =\n\
   \x20   \"0x\" + v.ToString(\"x\").PadLeft(n, '0')\n\
   \x20 let private decpad (n : int) (v : uint64) : string =\n\
   \x20   v.ToString().PadLeft(n, '0')\n\
   \n\
   \x20 let print_uint8 (v : uint8) : unit = w (hex (uint64 v))\n\
   \x20 let print_uint16 (v : uint16) : unit = w (hex (uint64 v))\n\
   \x20 let print_uint32 (v : uint32) : unit = w (hex (uint64 v))\n\
   \x20 let print_uint64 (v : uint64) : unit = w (hex v)\n\
   \n\
   \x20 let print_uint8_dec (v : uint8) : unit = w (string v)\n\
   \x20 let print_uint16_dec (v : uint16) : unit = w (string v)\n\
   \x20 let print_uint32_dec (v : uint32) : unit = w (string v)\n\
   \x20 let print_uint64_dec (v : uint64) : unit = w (string v)\n\
   \n\
   \x20 let print_uint8_hex_pad (v : uint8) : unit = w (hexpad 2 (uint64 v))\n\
   \x20 let print_uint16_hex_pad (v : uint16) : unit = w (hexpad 4 (uint64 v))\n\
   \x20 let print_uint32_hex_pad (v : uint32) : unit = w (hexpad 8 (uint64 v))\n\
   \x20 let print_uint64_hex_pad (v : uint64) : unit = w (hexpad 16 v)\n\
   \n\
   \x20 let print_uint8_dec_pad (v : uint8) : unit = w (decpad 3 (uint64 v))\n\
   \x20 let print_uint16_dec_pad (v : uint16) : unit = w (decpad 5 (uint64 v))\n\
   \x20 let print_uint32_dec_pad (v : uint32) : unit = w (decpad 10 (uint64 v))\n\
   \x20 let print_uint64_dec_pad (v : uint64) : unit = w (decpad 20 v)\n\
   \n\
   // Section 122.9.  [FStar.Char.char] is .NET's [char] and [Prims.string] is\n\
   // .NET's [string], so these are UTF-16 code units throughout -- see the\n\
   // note on [builtin_type].  Ordinal comparison and the invariant-culture\n\
   // case mappings, so that the result does not depend on the machine's\n\
   // locale the way a verified program's does not.\n\
   module FStar_Char =\n\
   \x20 let lowercase (c : char) : char = System.Char.ToLowerInvariant c\n\
   \x20 let uppercase (c : char) : char = System.Char.ToUpperInvariant c\n\
   \x20 let int_of_char (c : char) : bigint = bigint (int c)\n\
   \x20 let char_of_int (i : bigint) : char = char (int i)\n\
   \x20 let u32_of_char (c : char) : uint32 = uint32 (int c)\n\
   \x20 let char_of_u32 (u : uint32) : char = char (int u)\n\
   \n\
   module FStar_String =\n\
   \x20 let make (n : bigint) (c : char) : string = System.String (c, int n)\n\
   \x20 let strcat (s : string) (t : string) : string = s + t\n\
   \x20 let split (seps : char list) (s : string) : string list =\n\
   \x20   List.ofArray (s.Split (Array.ofList seps))\n\
   \x20 let compare (x : string) (y : string) : bigint =\n\
   \x20   bigint (System.String.CompareOrdinal (x, y))\n\
   \x20 let concat (sep : string) (l : string list) : string =\n\
   \x20   System.String.Join (sep, l)\n\
   \x20 let length (s : string) : bigint = bigint s.Length\n\
   \x20 let substring (s : string) (i : bigint) (j : bigint) : string =\n\
   \x20   s.Substring (int i, int j)\n\
   \x20 let get (s : string) (i : bigint) : char = s.[int i]\n\
   \x20 let collect (f : char -> string) (s : string) : string =\n\
   \x20   System.String.Join (\"\", Seq.map f s)\n\
   \x20 let lowercase (s : string) : string = s.ToLowerInvariant ()\n\
   \x20 let uppercase (s : string) : string = s.ToUpperInvariant ()\n\
   \x20 let index_of (s : string) (c : char) : bigint = bigint (s.IndexOf c)\n\
   \x20 let list_of_string (s : string) : char list = List.ofSeq s\n\
   \x20 let string_of_list (l : char list) : string = System.String (Array.ofList l)\n\
   \x20 let string_of_char (c : char) : string = System.String (c, 1)\n\
   \n\
   module FStar_All =\n\
   \x20 let failwith (s : string) : 'a = failwith s\n\
   \x20 let exit (i : bigint) : 'a = exit (int i)\n\
   \x20 let try_with (f : unit -> 'a) (g : exn -> 'a) : 'a =\n\
   \x20   try f () with e -> g e\n\
   \x20 let pipe_right (x : 'a) (f : 'a -> 'b) : 'b = f x\n\
   \x20 let pipe_left (f : 'a -> 'b) (x : 'a) : 'b = f x\n\
   \n\
   // [FStar.List] is [FStar.List.Tot.Base] with an [ML] effect, which F#\n\
   // does not distinguish; only the three that are not in the total module\n\
   // under the same meaning are given here.\n\
   module FStar_List =\n\
   \x20 let nth (l : 'a list) (i : bigint) : 'a = List.item (int i) l\n\
   \x20 let iter (f : 'a -> unit) (l : 'a list) : unit = List.iter f l\n\
   \x20 let iteri (f : bigint -> 'a -> unit) (l : 'a list) : unit =\n\
   \x20   List.iteri (fun i x -> f (bigint i) x) l\n"

(* The target framework.  .NET 10 is the current long-term-support release and
   the first that this backend was written against; [System.Int128] needs 7 or
   later, so nothing older than that would work in any case. *)
let target_framework : string = "net10.0"

let project_source (stem:string) (exe:bool) : ML string =
  "<!-- Generated by F* Custard extraction. Do not edit. -->\n\
   <Project Sdk=\"Microsoft.NET.Sdk\">\n\
   \x20 <PropertyGroup>\n\
   \x20   <OutputType>" ^ (if exe then "Exe" else "Library") ^ "</OutputType>\n\
   \x20   <TargetFramework>" ^ target_framework ^ "</TargetFramework>\n\
   \x20   <Nullable>disable</Nullable>\n\
   \x20   <InvariantGlobalization>true</InvariantGlobalization>\n\
   \x20   <SatelliteResourceLanguages>en</SatelliteResourceLanguages>\n\
   \x20   <GenerateDocumentationFile>false</GenerateDocumentationFile>\n\
   \x20 </PropertyGroup>\n\
   \x20 <ItemGroup>\n\
   \x20   <Compile Include=\"FStarCustard.fs\" />\n\
   \x20   <Compile Include=\"" ^ stem ^ ".fs\" />\n\
   \x20 </ItemGroup>\n\
   </Project>\n"

let project_files (stem:string) (p:program) : ML (list (string & string)) =
  [ ("FStarCustard.fs", runtime_source);
    (stem ^ ".fsproj", project_source stem (Cons? (entrypoints p))) ]
