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

(** The direct-to-C backend (section 6, milestone M8).

    The output is a single self-contained C11 file: nothing but the C standard
    library, no krmllib headers and no macros of our own beyond one typedef
    for the unit type.  Allocation is [malloc]/[free] and failure is
    [abort ()].

    Two things make this a mostly syntax-directed printer rather than a
    compiler.  The program is *monomorphic*, so every type has a size, and it
    is in *A-normal form* (section 6, pass 1), so every operand is already a
    variable or a constant and there is nothing left to sequence.  What is left
    is the impedance mismatch between an expression language and a statement
    language: [ELet], [EIf], [EMatch], [ESeq] and [EWhile] can all appear where
    C wants an expression.  So there are two mutually recursive printers --
    [emit], which compiles an expression into statements that deliver its value
    to a destination, and [c_expr], which prints an expression that really is a
    C expression, hoisting anything that is not into a preceding statement.

    What C cannot express is *rejected by name*, with error 368, rather than
    mistranslated: closures, exceptions, unbounded [Prims.int], pattern
    disjunctions and guards, and datatypes that contain themselves by value.
    Section 5.0.1's type monomorphization is a prerequisite -- without it the
    program still has type variables, which have no size. *)
module FStarC.Custard.PrintC

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Class.Show
open FStarC.BaseTypes
open FStarC.Const
open FStarC.Custard.Syntax
open FStarC.Pprint
open FStarC.Errors.Msg

module BU     = FStarC.Util
module SMap   = FStarC.SMap
module E      = FStarC.Errors
module String = FStarC.String
module Options = FStarC.Options
module Simplify = FStarC.Custard.Simplify

(* -------------------------------------------------------------------- *)
(* Rejections                                                           *)
(* -------------------------------------------------------------------- *)

(* The declaration being printed, so that a rejection can say where it is.
   The IR carries no source positions (section 2.2), so the declaration's name
   is the best locator there is -- and, since Custard's names are readable by
   construction, a good one. *)
let current : ref string = mk_ref "<toplevel>"

(* Section 31.2.  A declaration name on its own is not enough to act on.
   Errors 364, 365 and 373 all print a "Reached through" chain, because
   extraction is demand-driven and the chain is the demand; error 368 printed
   none, and twice in a row that was the thing that stopped a reader.
   [Prims.op_Less] is the extreme case: it is used everywhere, it appears
   nowhere in the output, and being told only its name says nothing about
   which use of it survived.

   The backend has no request chain -- it runs after extraction, on the
   program -- but it has the call graph, and reachability from a root is the
   same information seen from the other end.  [parents] maps a declaration to
   the one that pulled it in, filled by a breadth-first walk from the roots
   so that the chain it yields is a shortest one. *)
let parents : SMap.t string = SMap.create 50

(* Section 31.3.  For a type declaration that was left polymorphic, the
   external whose signature mentions it -- which is *why* it was left
   polymorphic, by §5.0.1 rule 4.  Naming it is the difference between "the
   pass did not reach this, please report a bug" and "this declaration is
   realized outside the program, so the pass was not allowed to clone it". *)
let frozen_by : SMap.t string = SMap.create 20
(* Section 32.5.  Whether the external that froze a type is a [custard_extern]
   -- a C symbol the program named -- or a hand-written OCaml realization.
   The advice differs, and asserting the wrong one sends a reader to look for
   an .ml file that does not exist. *)
let frozen_by_target : SMap.t string = SMap.create 20

(* Section 33.4.  Type name -> the constructor and [Type0] field that make it
   an existential, from the {!Existential} flag the extractor sets.  Kept as
   its own table rather than read off {!types} for the ordinary reason: a
   rejection has to be able to explain itself before the printer's tables
   exist, and this one is filled from the program at the same time they are. *)
let existentials : SMap.t (string & string) = SMap.create 20

let reached_through (n:string) : ML (list string) =
  let rec up (n:string) (fuel:int) (acc:list string) : ML (list string) =
    if fuel <= 0 then List.rev acc
    else match SMap.try_find parents n with
         | None -> List.rev acc
         | Some p -> up p (fuel - 1) (p :: acc) in
  up n 12 []

(* Section 32.1.  Bounded for the same reason {!Extract.clip_chain_entry} is:
   a declaration name carries a specialization suffix, and although section
   30.15 bounds the one Custard emits, a chain is not a place where an
   unbounded string may appear on the strength of "it should be short". *)
let chain_entry_width : int = 200

let chain_msg () : ML (list Pprint.document) =
  let clip (s:string) : ML string =
    if String.length s <= chain_entry_width then s
    else String.substring s 0 chain_entry_width ^
         " ... (" ^ show (String.length s) ^ " chars)" in
  match reached_through !current with
  | [] -> []
  | ns -> text "Reached through:" ::
          (ns |> List.map (fun n -> text ("  " ^ clip n)))

(* Section 33.4.  Rule 4b rejects an existential type twice over: error 364
   when a monomorphized binder has one for its type, and error 368 when the
   backend meets a field of it whose representation is gone.  Only the first
   could say so, because only the first still has the source type in hand --
   by the time the backend sees the type, the [Type0] field is erased and
   what is left is a [TAny] or a type variable with no visible cause.

   The reporter's two Kuiper paths are both the second, which is why the
   advice they were given was "please report a Custard bug" about a type that
   is correctly rejected.  So the answer is looked up rather than inferred,
   and along the whole chain and not only at the head: the type that lost its
   representation is often a *field's* type, and the existential is then the
   record above it that the chain already names. *)
let existential_msg () : ML (list Pprint.document) =
  let rec first (ns:list string) : ML (list Pprint.document) =
    match ns with
    | [] -> []
    | n :: ns ->
      (match SMap.try_find existentials n with
       | Some (c, f) ->
         [text (n ^ " is an existential package, not an instance of a \
                parameterized type: its constructor " ^ c ^ " stores the \
                type " ^ f ^ ", and a later field's type mentions it, so its \
                representation depends on its contents (section 30.3).");
          text "That is why the representation above is unknown, and it is \
                not a Custard bug: no C layout exists for it, and no \
                annotation changes that.  Replace the stored type by an \
                index the program can case on, or make it a parameter of the \
                type rather than a field of the constructor."]
       | None -> first ns) in
  first (!current :: reached_through !current)

let reject (#a:Type) (what:string) (why:list string) : ML a =
  E.raise_error0 E.Error_CustardNoCRepresentation
    ([text ("Custard: " ^ what ^ " has no C representation, in " ^ !current ^ ".")]
     @ List.map text why @ existential_msg () @ chain_msg ())

(* The other kind of refusal: not "C cannot express this", which is a fact
   about the source, but "the IR is malformed", which is a fact about the
   compiler.  Worth telling apart in the message, since only one of the two is
   something the reader can act on. *)
let reject_ir (#a:Type) (what:string) (why:list string) : ML a =
  E.raise_error0 E.Error_CustardNoCRepresentation
    ([text ("Custard: " ^ what ^ " reached the C backend, in " ^ !current ^ ".")]
     @ List.map text why @ chain_msg ())

(* -------------------------------------------------------------------- *)
(* Names                                                                *)
(* -------------------------------------------------------------------- *)

(* C reserves rather few words, but a generated identifier that happens to be
   one of them is a syntax error a long way from its cause. *)
let c_keywords = [
  "auto"; "break"; "case"; "char"; "const"; "continue"; "default"; "do";
  "double"; "else"; "enum"; "extern"; "float"; "for"; "goto"; "if"; "inline";
  "int"; "long"; "register"; "restrict"; "return"; "short"; "signed";
  "sizeof"; "static"; "struct"; "switch"; "typedef"; "union"; "unsigned";
  "void"; "volatile"; "while"; "_Bool"; "_Complex"; "_Imaginary"; "bool";
  "true"; "false"; "NULL"; "main";
]

let is_alpha (i:int) : bool = (i >= 97 && i <= 122) || (i >= 65 && i <= 90)

(* Section 30.15.  One pass.  This used to call [list_of_string] three times,
   twice only to look at the first character, and [list_of_string] was itself
   quadratic; [sanitize] is on the path of every name Custard prints, so the
   product showed up as 96% of a run once names got long. *)
let sanitize (s:string) : ML string =
  let ok (i:int) : bool = is_alpha i || (i >= 48 && i <= 57) || i = 95 in
  match String.list_of_string s with
  | [] -> "x"
  | c0 :: cs ->
    let s = String.concat ""
              (List.map (fun c -> if ok (BU.int_of_char c)
                                  then BU.string_of_char c else "_")
                        (c0 :: cs)) in
    (* A C identifier may not start with a digit.  The test is on the mapped
       first character, as it was when it read the mapped string back. *)
    let i0 = BU.int_of_char c0 in
    let i0 = if ok i0 then i0 else 95 in
    if is_alpha i0 || i0 = 95 then s else "x" ^ s

(* Section 32.10.  [c_expr] parenthesizes every operator application, so a
   condition arrives already wrapped and [if (...)] adds a second pair.  clang
   calls that -Wparentheses-equality and emitted it 78 times on one generated
   file; a consumer building with -Werror cannot use the output.

   One pair, and only when the string *is* one group -- the leading paren must
   be the one the trailing paren closes, or [(a) && (b)] would lose its
   meaning. *)
let is_group (s:string) : ML bool =
  let n = String.length s in
  if n < 2 || String.substring s 0 1 <> "(" || String.substring s (n - 1) 1 <> ")"
  then false
  else
    let cs = String.list_of_string s in
    let rec scan (cs:list FStarC.BaseTypes.char) (i:int) (depth:int) : ML bool =
      match cs with
      | [] -> true
      | c :: rest ->
        let d = if BU.int_of_char c = 40 then depth + 1
                else if BU.int_of_char c = 41 then depth - 1
                else depth in
        (* Reaching zero before the last character means the opening paren
           closed early, so it is not the outermost group. *)
        if d = 0 && i < n - 1 then false else scan rest (i + 1) d in
    scan cs 0 0

let unparen (s:string) : ML string =
  if is_group s then String.substring s 1 (String.length s - 2) else s

(* Section 35.2.  Wrap in one pair, unless the string is already one group.
   Every position that needs its operand parenthesized goes through here, so
   that none of them can be the one that adds the second pair. *)
let group (s:string) : ML string =
  if is_group s then s else "(" ^ s ^ ")"

(* [!e] binds tighter than any operator, so the operand has to be a group;
   one that already is keeps its own parens rather than gaining a second. *)
let negate (s:string) : ML string =
  "!" ^ group s

let escape_kw (s:string) : ML string =
  if List.existsb (fun k -> k = s) c_keywords then s ^ "_" else s

(* Section 32.4.  [--custard_c_no_prefix] renames a public definition to its
   unqualified identifier.  The map is keyed by {!string_of_name} and is
   consulted by every printer, because a rename has to reach the definition,
   the prototype and every call site in the file alike: this is one C name
   for one IR name, not a second name for the same thing. *)
let renames : ref (SMap.t string) = mk_ref (SMap.create 0)

let c_name (n:name) : ML string =
  match SMap.try_find !renames (string_of_name n) with
  | Some s -> s
  | None -> escape_kw (sanitize (mangled_name n))
let c_var (x:string) : ML string = escape_kw (sanitize x)

(* An enum tag.  Uppercased so that it cannot collide with a value or a type
   name derived from the same lid. *)
(* Through {!renames}, so that a constructor of a --custard_c_no_prefix module
   gets the unqualified tag its type and its functions got.  Uppercasing is
   what keeps it from colliding with a value or type name of the same lid, and
   {!build_renames} checks the un-uppercased form, so a rename that is legal
   there is legal here. *)
let c_tag (n:name) : ML string =
  String.uppercase (match SMap.try_find !renames (string_of_name n) with
                    | Some s -> s
                    | None -> sanitize (mangled_name n))

(* -------------------------------------------------------------------- *)
(* The declaration tables                                               *)
(* -------------------------------------------------------------------- *)

(* Printing a pattern or a constructor application needs the layout of the
   type involved, which is not on the node.  Both tables are constant for a
   whole program, so they are globals rather than a threaded environment. *)
let types : ref (SMap.t dtype) = mk_ref (SMap.create 0)
(* constructor name -> (its type, its field list) *)
let ctors : ref (SMap.t (dtype & list (string & cty))) = mk_ref (SMap.create 0)
(* external name -> the symbol to call it by *)
let externs : ref (SMap.t string) = mk_ref (SMap.create 0)

(* Which parameters of a definition survive into C.  A [unit] parameter the
   body never mentions carries no information -- it is F*'s way of writing a
   thunk, and C has no laziness to preserve -- so it is dropped from the
   signature and from every call site.  The flags are computed once, in
   [print_program], because the call site has to make the same decision as the
   definition. *)
let keeps : ref (SMap.t (list bool)) = mk_ref (SMap.create 0)

(* Which definitions return [unit], and are therefore emitted as C [void].
   Consulted at the call site, where a [void] call is a statement and cannot be
   an operand. *)
let void_fns : ref (SMap.t bool) = mk_ref (SMap.create 0)

(* How many arguments each named definition takes, after the dropped
   parameters of [keeps] are removed.  Only used to refuse a call that does
   not match: C has neither partial application nor a way to apply a call's
   result without saying so, and both come out as a plain call with the wrong
   number of operands -- valid IR, and C that does not compile (section 25). *)
let arities : ref (SMap.t int) = mk_ref (SMap.create 0)

(* Whether the definition currently being printed returns [void]. *)
let void_ret : ref bool = mk_ref false

let rec filter_by (#a:Type) (flags:list bool) (xs:list a) : list a =
  match flags, xs with
  | b :: flags, x :: xs -> (if b then [x] else []) @ filter_by flags xs
  | _ -> xs

let find_type (n:name) : ML (option dtype) = SMap.try_find !types (string_of_name n)
let find_ctor (n:name) : ML (option (dtype & list (string & cty))) =
  SMap.try_find !ctors (string_of_name n)

(* A variant with a single constructor needs neither a tag nor a union: it is
   just a struct of that constructor's fields.  This is what keeps a pair from
   costing a discriminator, and it is the shape most patterns in real code
   match against. *)
let single_ctor (d:dtype) : bool =
  match d.dt_body with TVariant [_] -> true | _ -> false

(* A variant none of whose constructors carries a field is an enum. *)
let is_enum (d:dtype) : ML bool =
  match d.dt_body with
  | TVariant cs -> Cons? cs && cs |> List.for_all (fun (_, fs) -> Nil? fs)
  | _ -> false

(* -------------------------------------------------------------------- *)
(* Types                                                                *)
(* -------------------------------------------------------------------- *)

let int_type (sw : signedness & width) : string =
  let s, w = sw in
  match w with
  | Sizet -> "size_t"
  | _ ->
    (match s with Unsigned -> "uint" | Signed -> "int") ^
    (match w with Int8 -> "8" | Int16 -> "16" | Int32 -> "32"
                | Int64 -> "64" | Sizet -> "") ^ "_t"

(* The types the standard library already realizes.  [Prims.int] is
   deliberately *not* among them: it is unbounded, and silently truncating it
   to a machine width is the one mistranslation that would be invisible in the
   output.  Section 6 makes the same argument for leaving the [Prims]
   arithmetic operators as unresolved symbols. *)
(* Section 19.13.  What to say about a type the direct backend cannot size.
   The obvious advice -- turn on [--custard_monomorphize_types] -- is only
   advice when it is not already on, and telling a reader to set a flag they
   have set sends them looking in the wrong place.  When it is on, the pass
   ran and this type is one it did not reach, which is a bug report rather
   than a configuration change. *)
(* Section 31.3.  With the flag on, "the pass did not reach it" was a guess,
   and usually the wrong one: the common cause is §5.0.1 rule 4, which freezes
   every type an externally realized declaration mentions, because a clone of
   it would name something the hand-written realization does not define.  That
   is not a bug, it is a decision, and it has a culprit worth printing. *)
let mono_advice_for (n:option name) : ML (list string) =
  if not (Options.custard_monomorphize_types ())
  then ["The direct-to-C backend requires --custard_monomorphize_types true \
         (section 5.0.1)."]
  else
    match (match n with
           | None -> None
           | Some n -> SMap.try_find frozen_by (string_of_name n)) with
    | Some ext ->
      let where =
        match (match n with
               | None -> None
               | Some n -> SMap.try_find frozen_by_target (string_of_name n)) with
        | Some sym ->
          "it is the C symbol `" ^ sym ^ "', named by a custard_extern \
           attribute, and that symbol's own declaration decides the layout"
        | None ->
          "it is a hand-written realization for the OCaml backend, and there \
           is no C counterpart" in
      ["--custard_monomorphize_types is set, and the pass deliberately left \
        this type alone: it is mentioned in the signature of " ^ ext ^ ", \
        which is realized outside this program, so a monomorphic clone of it \
        would name a declaration the realization does not define (section \
        5.0.1, rule 4).";
       "The type is frozen because " ^ ext ^ " is external, not because it \
        could not be sized.  Give " ^ ext ^ " a definition Custard can \
        compile -- " ^ where ^ " -- or keep this type out of its signature."]
    | None ->
      (* Section 33.4.  "Please report a bug" is the wrong thing to say when
         the cause is known and is not a bug.  {!existential_msg} is about to
         say what it is, so this branch stands down rather than contradict
         it. *)
      if Cons? (existential_msg ())
      then ["--custard_monomorphize_types is already set, so nothing was left \
             polymorphic by choice; the reason is below."]
      else
      ["--custard_monomorphize_types is already set, so this type is one the \
        monomorphization pass did not reach (section 5.0.1).";
       "That is a Custard bug, not a configuration problem: please report it, \
        with the definition named above."]

let mono_advice () : ML (list string) = mono_advice_for None

let builtin_type (n:name) : ML (option string) =
  match (if Some? n.spec then "" else String.concat "." (n.ns @ [n.id])) with
  | "Prims.unit" -> Some "custard_unit"
  | "Prims.bool" -> Some "bool"
  | "Prims.string" -> Some "const char *"
  | "FStar.Char.char" -> Some "uint32_t"
  | _ -> None

(* Section 44.2.  [Prims.string] is [const char *], so C's [==] on two of them
   is a comparison of addresses.  That is right for no F* program: F*'s
   equality on strings is equality of contents, and whether two equal strings
   share an address is a decision the C compiler makes about its literal pool.
   Every site that would emit [==] has to know when it is looking at one. *)
let is_string_ty (t:cty) : ML bool =
  match t with
  | TApp (n, []) ->
    None? n.spec && String.concat "." (n.ns @ [n.id]) = "Prims.string"
  | _ -> false

(* C declarations are not "type, then name": the [*] of a pointer and the
   [(...)] of a function bind to the *declarator*, so the name has to be built
   from the inside out.  [decl_of t x] is the declaration of [x] at type [t],
   and [x = ""] gives the abstract declarator -- the form a cast or a compound
   literal wants.  Building the two together is what lets a returned pointer
   ([uint32_t *f(void)]) and a stored function ([size_t ( *hashf)(size_t)]) come
   out right without special cases at each use. *)
let rec decl_of (t:cty) (x:string) : ML string =
  match t with
  | TBuf e | TRef e -> decl_of e ("*" ^ x)
  (* A function cannot be stored, only a pointer to one, so a [TArrow] in a
     data position becomes a function pointer.  Custard has no closures --
     [EFun] in a value position is rejected below -- so the value is always a
     top-level definition, and its name is exactly this pointer. *)
  | TArrow _ ->
    let rec spine (t:cty) (acc:list cty) : ML (list cty & cty) =
      match t with
      | TArrow (a, _, b) -> spine b (a :: acc)
      | _ -> (List.rev acc, t) in
    let args, ret = spine t [] in
    decl_of ret ("(*" ^ x ^ ")(" ^
                 String.concat ", " (args |> List.map (fun a -> decl_of a "")) ^ ")")
  | _ -> base_ty t ^ (if x = "" then "" else " " ^ x)

and base_ty (t:cty) : ML string =
  match t with
  | TUnit -> "custard_unit"
  | TInt sw -> int_type sw
  | TFloat Float32 -> "float"
  | TFloat Float64 -> "double"
  | TApp (n, []) ->
    (match builtin_type n with
     | Some s -> s
     | None ->
       (match find_type n with
        (* An external type is declared in a header, so its size and its name
           are someone else's business (section 8.1, kind 4). *)
        | Some { dt_body = TAbstract; dt_flags = fs }
          when List.existsb Extern? fs ->
          (match List.tryPick (fun f -> match f with
                                        | Extern (t, _) -> t
                                        | _ -> None) fs with
           | Some t -> t
           | None -> c_name n)
        | Some { dt_body = TAbstract } ->
          reject ("the abstract type " ^ string_of_name n)
            ["A type with no definition has no size, so C cannot store it.";
             "Prims.int in particular is unbounded: use a machine integer type \
              instead."]
        | _ -> c_name n))
  (* Section 19.13.  Advice the reader can act on, which means not naming a
     flag that is already set.  With [--custard_monomorphize_types] off, that
     flag is the whole answer; with it on, the pass ran and did not reach this
     type, which is a different problem with a different cause and deserves to
     be told apart. *)
  | TApp (n, _) ->
    reject ("the polymorphic type " ^ string_of_name n) (mono_advice_for (Some n))
  | TVar x ->
    reject ("the type variable '" ^ x) (mono_advice ())
  | TTuple _ ->
    reject "an anonymous tuple type"
      ["Tuples reach the backend as FStar.Pervasives.Native.tupleN, which is \
        an ordinary inductive; a bare TTuple means a rule introduced one."]
  | TAny ->
    reject "a value whose representation is unknown (TAny)"
      ["Run with --custard_warn_any to see where the representation was lost \
        (section 5.9)."]
  | TExn ->
    reject "an exception type"
      ["C has no exceptions."]
  | TBuf _ | TRef _ | TArrow _ -> decl_of t ""

(* The abstract declarator: a type as a cast or a compound literal spells it. *)
let ty (t:cty) : ML string = decl_of t ""

(* -------------------------------------------------------------------- *)
(* Constants                                                            *)
(* -------------------------------------------------------------------- *)

(* The unit value.  There is only one, and nothing may be done with it, so it
   is worth recognizing on sight. *)
let unit_value : string = "((custard_unit)0)"

(* The suffix a decimal literal of this width needs.  [U] is enough below 64
   bits, since a value that fits in [uint32_t] fits in [long] anyway on every
   target F\* supports; at 64 bits there is no wider standard type, so the
   suffix is the only thing that gives the literal a type. *)
let int_suffix (sw : signedness & width) : string =
  let s, w = sw in
  let wide = (match w with Int64 -> true | Sizet -> true | _ -> false) in
  match s with
  | Unsigned -> if wide then "ULL" else "U"
  | Signed -> if wide then "LL" else ""

(* [-9223372036854775808LL] is not a literal: it is unary minus applied to
   [9223372036854775808LL], whose magnitude is one past [LLONG_MAX].  Every
   signed width has this one value, and only at 64 bits is there no wider type
   to fall back on -- so it is written the way [<stdint.h>] writes [INT64_MIN]. *)
let int_literal (sw : signedness & width) (v:int) (b:int_base) : ML string =
  let sg, w = sw in
  let wide = (match w with Int64 -> true | Sizet -> true | _ -> false) in
  if Signed? sg && wide && v = -9223372036854775808
  then "(-9223372036854775807LL - 1)"
  else c_int_lit_to_string v b ^ int_suffix sw

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
      if i < 32 || i > 126
      then "\\" ^ (if i < 8 then "00" else if i < 64 then "0" else "") ^
           (* C string escapes are octal. *)
           show ((i / 64) * 100 + ((i / 8) % 8) * 10 + (i % 8))
      else BU.string_of_char c
  in
  String.concat "" (List.map esc (String.list_of_string s))

let constant (c:constant) : ML string =
  match c with
  | CUnit -> unit_value
  | CBool b -> if b then "true" else "false"
  | CInt (v, b, Some sw) ->
    (* The cast pins the type: an unsuffixed literal is [int], which would make
       [x + 1] promote and then wrap at the wrong width.  The *suffix* is a
       separate question, and a cast cannot answer it: C gives a decimal
       literal the first *signed* type it fits in (6.4.4.1), so
       [18446744073709551615] has no type at all and a conforming compiler
       must diagnose it.  So a literal that needs more than an [int] carries
       the suffix of the width it is meant to have, and the cast only narrows. *)
    "((" ^ int_type sw ^ ")" ^ int_literal sw v b ^ ")"
  | CInt (v, b, None) ->
    reject ("the unbounded integer literal " ^ int_lit_to_string v b)
      ["Prims.int has no C representation; use a machine integer type."]
  (* Section 39.  The literal, with the suffix that gives it the width it is
     meant to have: an unsuffixed C float literal is a [double], so [Float32]
     arithmetic would be done at double precision and rounded once at the end.
     No cast, because a cast cannot supply the literal's own type and the
     suffix already does. *)
  | CFloat (v, Float32) -> float_lit_to_string v ^ "f"
  | CFloat (v, Float64) -> float_lit_to_string v
  | CChar c -> "((uint32_t)" ^ show (BU.int_of_char c) ^ ")"
  | CString s -> "\"" ^ escape s ^ "\""

(* -------------------------------------------------------------------- *)
(* Operators                                                            *)
(* -------------------------------------------------------------------- *)

(* Every arithmetic, bitwise and comparison operator of the IR is a C operator
   at the same width, because the IR's machine integers *are* C's.  The
   difference between [Add] and [AddW] does not survive: C already defines
   unsigned arithmetic to wrap, and at a signed width an overflow is undefined
   either way -- the checked variant's guarantee comes from the F* proof, not
   from anything the backend emits. *)
let infix_op (o:prim_op) : ML (option string) =
  match o.po_op with
  | Add | AddW -> Some "+"
  | Sub | SubW -> Some "-"
  | Mult | MultW -> Some "*"
  | Div | DivW -> Some "/"
  | Mod -> Some "%"
  | BOr -> Some "|" | BAnd -> Some "&" | BXor -> Some "^"
  | BShiftL -> Some "<<" | BShiftR -> Some ">>"
  | Eq -> Some "==" | Neq -> Some "!="
  | Lt -> Some "<" | Lte -> Some "<=" | Gt -> Some ">" | Gte -> Some ">="
  (* At a width these are the *bitwise* operators and are strict; without one
     they are the short-circuiting connectives (section 6, pass 1). *)
  | And -> Some (if at_int_width o then "&" else "&&")
  | Or -> Some (if at_int_width o then "|" else "||")
  | _ -> None

let prefix_op (o:prim_op) : ML (option string) =
  match o.po_op with
  | Not -> Some (if at_int_width o then "~" else "!")
  | BNot -> Some "~"
  | _ -> None

(* C promotes anything narrower than [int] before it operates on it, so at
   [uint8_t] and [uint16_t] the result of a C operator is an [int] and can sit
   outside the width it came from.  For most operators that cannot happen: F\*
   proves that [add], [sub] and [mul] do not overflow, and [/], [%], [&], [|]
   and [^] cannot leave the range in the first place.  It happens for exactly
   the operators whose F\* meaning is *modular*: [lognot], [shift_left] and the
   [_mod] family.  [FStar.UInt8.lognot 0uy] is [255uy], and [~(uint8_t)0] read
   as an [int] is [-1] -- a wrong answer, not a warning, wherever the result is
   used before it is stored back.

   At 32 and 64 bits there is no promotion, and C's own wrapping is the one F\*
   specifies. *)
let truncate (o:prim_op) (s:string) : ML string =
  let modular =
    match o.po_op with
    | Not -> at_int_width o   (* [~] at a width; [!] on a bool is not this *)
    | BNot | BShiftL | AddW | SubW | MultW -> true
    | _ -> false in
  match o.po_ty with
  | Some (PInt sw) ->
    let _, w = sw in
    let narrow = (match w with Int8 -> true | Int16 -> true | _ -> false) in
    if modular && narrow then "((" ^ int_type sw ^ ")" ^ s ^ ")" else s
  | Some (PFloat _) | None -> s

(* -------------------------------------------------------------------- *)
(* Expressions                                                          *)
(* -------------------------------------------------------------------- *)

(* Where the value of an expression goes once it has been computed. *)
type dest =
  | D_Return
  | D_Assign of string
  | D_Ignore

(* C's block scoping and the IR's do not line up: an [ELet] scopes its variable
   over its body only, while the statements this backend emits for a chain of
   them all land in one C block, and a loop's condition lands in the same block
   as the loop's body.  Two disjoint IR scopes can therefore collide in C --
   which is a compile error, not a wrong answer, but a confusing one.

   Rather than bracing everything (which would bury the output in nesting),
   the backend keeps its own scope: a name is emitted as written unless the
   enclosing *function* has already used it, in which case it takes a
   subscript.  So the generated C reads like the source, and a subscript in it
   means something real. *)
(* Each entry is the C name a variable resolves to, and whether that name is a
   one-cell stack allocation the backend has collapsed into a variable (see
   [ELet] below): a use that wants the cell reads or assigns it, a use that
   wants the pointer takes its address. *)
let scope : ref (list (string & (string & bool))) = mk_ref []
let declared : ref (SMap.t bool) = mk_ref (SMap.create 0)

let reset_scope () : ML unit =
  scope := []; declared := SMap.create 20

let bind_gen (x:string) (cell:bool) : ML string =
  let base = c_var x in
  let rec pick (i:int) : ML string =
    let cand = if i = 0 then base else base ^ "_" ^ show i in
    if Some? (SMap.try_find !declared cand) then pick (i + 1) else cand in
  let nm = pick 0 in
  SMap.add !declared nm true;
  scope := (x, (nm, cell)) :: !scope;
  nm

(* A pattern binding does not need a variable of its own: the value it names is
   already reachable, as a projection out of the scrutinee, and both are
   immutable.  Binding the *path* instead of declaring a copy is what turns
   [{ size_t sz_1 = s.sz; t = sz_1; }] into [t = s.sz;]. *)
let bind_var (x:string) : ML string = bind_gen x false

(* A one-cell stack allocation, collapsed into an ordinary variable. *)
let bind_cell (x:string) : ML string = bind_gen x true

let bind_alias (x:string) (path:string) : ML unit =
  scope := (x, (path, false)) :: !scope

(* Section 18.4.  A name that no binder in the enclosing function introduced
   is a defect in the IR, not something to print and hope for.  The karamel
   backend catches it because its terms are De Bruijn and the conversion has
   to find an index; this backend prints names as names, and so used to emit
   the broken call silently -- an argument the callee does not take, naming a
   variable the caller does not have, which surfaces as a heap of unrelated
   gcc diagnostics about the function *after* it in the file.

   Every binder reaches [bind_var], [bind_cell] or [bind_alias] before its
   scope is printed, and [reset_scope] runs per definition, so a miss here is
   real.  Top-level names are [EQual] and never come through this. *)
let lookup_var (x:string) : ML string =
  match !scope |> List.tryFind (fun (y, _) -> y = x) with
  | Some (_, (nm, _)) -> nm
  | None ->
    reject_ir ("the unbound variable " ^ x)
      ["No binder in this definition introduces it.";
       "This is a compiler bug: please report it, with the definition named above."]

let is_cell (x:string) : ML bool =
  match !scope |> List.tryFind (fun (y, _) -> y = x) with
  | Some (_, (_, c)) -> c
  | None -> false

(* Fresh names for the temporaries the hoisting introduces.  They are the only
   names in the output that no source name stands behind, so they are spelled
   distinctively. *)
let ctr : ref int = mk_ref 0
let fresh (stem:string) : ML string =
  ctr := !ctr + 1;
  let nm = "_c" ^ stem ^ show !ctr in
  SMap.add !declared nm true;
  nm

(* Statement-shaped: a form that C has no expression for.  These are the
   forms [c_expr] has to hoist and [emit] compiles directly. *)
let is_stmt (e:expr) : bool =
  match e.e with
  | ELet _ | EMatch _ | EIf _ | ESeq _ | EWhile _ | EAbort _ -> true
  (* An allocation needs an initializing loop, and the three that return no
     value need a statement to be a statement. *)
  | EOp ({ po_op = BufCreate _ }, _) | EOp ({ po_op = BufWrite }, _)
  | EOp ({ po_op = BufBlit }, _) | EOp ({ po_op = BufFree }, _) -> true
  | _ -> false

(* Every variable that occurs anywhere in a term.  Shadowing is ignored, which
   makes this an over-approximation -- and an over-approximation is the safe
   direction, since the only question asked of it is "is this name definitely
   unused?".  C warns about an unused variable, and with -Werror that is the
   difference between output that compiles and output that does not; F* code
   binds pattern variables it does not use all the time. *)
let rec vars_of (e:expr) : ML (list string) =
  match e.e with
  | EVar x -> [x]
  | EConst _ | EQual _ | EAny | EAbort _ -> []
  | ELet (_, _, a, b) -> vars_of a @ vars_of b
  | EApp (h, es) -> vars_of h @ List.collect vars_of es
  | EFun (_, b) -> vars_of b
  | EMatch (sc, brs) -> vars_of sc @ List.collect vars_of_branch brs
  | ETry (a, brs) -> vars_of a @ List.collect vars_of_branch brs
  | EIf (a, b, c) -> vars_of a @ vars_of b @ vars_of c
  | ESeq (a, b) -> vars_of a @ vars_of b
  | EWhile (a, b) -> vars_of a @ vars_of b
  | ECtor (_, es) | ETuple es | EOp (_, es) -> List.collect vars_of es
  | ERaise e1 -> vars_of e1
  | ERecord (_, fs) -> List.collect (fun (_, e) -> vars_of e) fs
  | EProj (a, _, _) | EDiscrim (a, _) | ECast (a, _)
  | ECoerce (a, _) -> vars_of a

and vars_of_branch (br:branch) : ML (list string) =
  let _, g, b = br in
  (match g with Some g -> vars_of g | None -> []) @ vars_of b

(* Does [e] write to the collapsed cell [x], or take its address (which would
   let something else write to it)?  If not, a value read out of the cell stays
   valid for the whole of [e], and the read needs no copy. *)
let rec mutates (x:string) (e:expr) : ML bool =
  let any (es:list expr) : ML bool = List.existsb (mutates x) es in
  match e.e with
  | EVar y -> y = x
  | EOp ({ po_op = BufRead }, [{ e = EVar y }; i]) when y = x -> mutates x i
  | EConst _ | EQual _ | EAny | EAbort _ -> false
  | ELet (_, _, a, b) -> mutates x a || mutates x b
  | EApp (h, es) -> mutates x h || any es
  | EFun (_, b) -> mutates x b
  | EMatch (sc, brs) -> mutates x sc || List.existsb (mutates_branch x) brs
  | ETry (a, brs) -> mutates x a || List.existsb (mutates_branch x) brs
  | EIf (a, b, c) -> mutates x a || mutates x b || mutates x c
  | ESeq (a, b) | EWhile (a, b) -> mutates x a || mutates x b
  | ECtor (_, es) | ETuple es | EOp (_, es) -> any es
  | ERaise e1 -> mutates x e1
  | ERecord (_, fs) -> List.existsb (fun (_, e) -> mutates x e) fs
  | EProj (a, _, _) | EDiscrim (a, _) | ECast (a, _)
  | ECoerce (a, _) -> mutates x a

and mutates_branch (x:string) (br:branch) : ML bool =
  let _, g, b = br in
  (match g with Some g -> mutates x g | None -> false) || mutates x b

(* An expression whose value cannot change and whose evaluation does nothing:
   a variable that is not a collapsed cell, and projections out of one.  The
   backend never assigns to such a variable, so a copy of it is dead weight. *)
let rec is_stable (e:expr) : ML bool =
  match e.e with
  | EVar x -> not (is_cell x)
  | EProj (a, _, _) -> is_stable a
  | _ -> false

(* No calls, no writes, no loops: an expression that can be moved anywhere
   without changing what the program does. *)
let rec is_pure (e:expr) : ML bool =
  let all (es:list expr) : ML bool = List.for_all is_pure es in
  match e.e with
  | EConst _ | EVar _ | EQual _ | EAny -> true
  | EApp _ | EFun _ | EWhile _ | EAbort _ | ERaise _ | ETry _ -> false
  | EOp ({ po_op = BufRead }, es) -> all es
  | EOp ({ po_op = BufCreate _ }, _) | EOp ({ po_op = BufWrite }, _)
  | EOp ({ po_op = BufFree }, _) | EOp ({ po_op = BufBlit }, _) -> false
  | EOp (_, es) | ECtor (_, es) | ETuple es -> all es
  | ELet (_, _, a, b) | ESeq (a, b) -> is_pure a && is_pure b
  | EIf (a, b, c) -> is_pure a && is_pure b && is_pure c
  | EMatch (sc, brs) -> is_pure sc && List.for_all is_pure_branch brs
  | ERecord (_, fs) -> List.for_all (fun (_, e) -> is_pure e) fs
  | EProj (a, _, _) | EDiscrim (a, _) | ECast (a, _)
  | ECoerce (a, _) -> is_pure a

and is_pure_branch (br:branch) : ML bool =
  let _, g, b = br in
  (match g with Some g -> is_pure g | None -> true) && is_pure b

(* [is_pure] answers "may this be *moved*"; this answers "may this be
   *deleted*", and the second is weaker.  The only difference is a read: a
   read of a collapsed cell cannot move across a write to it, and it can
   always go when nothing wants its value, because reading a cell Pulse has
   established is live does nothing observable.  Nothing else changes -- a
   call, a write, an allocation, a loop and an abort are as undeletable as
   they are unmovable. *)
let rec is_droppable (e:expr) : ML bool =
  let all (es:list expr) : ML bool = List.for_all is_droppable es in
  match e.e with
  | EConst _ | EVar _ | EQual _ | EAny -> true
  | EApp _ | EFun _ | EWhile _ | EAbort _ | ERaise _ | ETry _ -> false
  | EOp ({ po_op = BufRead }, es) -> all es
  | EOp ({ po_op = BufCreate _ }, _) | EOp ({ po_op = BufWrite }, _)
  | EOp ({ po_op = BufFree }, _) | EOp ({ po_op = BufBlit }, _) -> false
  | EOp (_, es) | ECtor (_, es) | ETuple es -> all es
  | ELet (_, _, a, b) | ESeq (a, b) -> is_droppable a && is_droppable b
  | EIf (a, b, c) -> is_droppable a && is_droppable b && is_droppable c
  | EMatch (sc, brs) -> is_droppable sc && List.for_all is_droppable_branch brs
  | ERecord (_, fs) -> List.for_all (fun (_, e) -> is_droppable e) fs
  | EProj (a, _, _) | EDiscrim (a, _) | ECast (a, _)
  | ECoerce (a, _) -> is_droppable a

and is_droppable_branch (br:branch) : ML bool =
  let _, g, b = br in
  (match g with Some g -> is_droppable g | None -> true) && is_droppable b

(* Section 19.8.  A cell that is written and never read.  Pulse's loop measure
   is one: [fn while] carries a decreasing value the checker needs and the
   program does not, so it arrives as a [let mut] whose type has erased to
   [custard_unit] and whose writes assign a constant.  C says
   -Wunused-but-set-variable and C is right.

   [cell_dead] is the side condition, and it has to be stricter than "never
   read".  Every occurrence of the name must be the cell operand of a write,
   which rules out the two ways a cell can be used without being read: an
   address taken and passed somewhere, and a read the surrounding term does
   something else with.  The written values must be pure as well, since
   dropping the write drops them, and the index must be too.  For the measure
   all of this is trivially true; the point of checking is that nothing else
   is quietly caught by it. *)
let rec cell_dead (x:string) (e:expr) : ML bool =
  let all (es:list expr) : ML bool = List.for_all (cell_dead x) es in
  match e.e with
  | EVar y -> y <> x
  | EOp ({ po_op = BufWrite }, [{ e = EVar y }; i; v]) when y = x ->
    is_droppable i && is_droppable v
  | EConst _ | EQual _ | EAny | EAbort _ -> true
  | ELet (_, _, a, b) | ESeq (a, b) | EWhile (a, b) -> cell_dead x a && cell_dead x b
  | EApp (h, es) -> cell_dead x h && all es
  | EFun (_, b) | ERaise b -> cell_dead x b
  | EMatch (sc, brs) -> cell_dead x sc && List.for_all (cell_dead_branch x) brs
  | ETry (a, brs) -> cell_dead x a && List.for_all (cell_dead_branch x) brs
  | EIf (a, b, c) -> cell_dead x a && cell_dead x b && cell_dead x c
  | ECtor (_, es) | ETuple es | EOp (_, es) -> all es
  | ERecord (_, fs) -> List.for_all (fun (_, e) -> cell_dead x e) fs
  | EProj (a, _, _) | EDiscrim (a, _) | ECast (a, _)
  | ECoerce (a, _) -> cell_dead x a

and cell_dead_branch (x:string) (br:branch) : ML bool =
  let _, g, b = br in
  (match g with Some g -> cell_dead x g | None -> true) && cell_dead x b

(* The writes [cell_dead] licensed, replaced by the unit they evaluate to.
   Nothing else in the term mentions the cell, so this is the whole of it. *)
let rec drop_writes (x:string) (e:expr) : ML expr =
  let go (e:expr) : ML expr = drop_writes x e in
  let go_branch (br:branch) : ML branch =
    let p, g, b = br in
    (p, (match g with Some g -> Some (go g) | None -> None), go b) in
  let e' =
    match e.e with
    | EOp ({ po_op = BufWrite }, [{ e = EVar y }; _; _]) when y = x -> EConst CUnit
    | EConst _ | EVar _ | EQual _ | EAny | EAbort _ -> e.e
    | ELet (n, t, a, b) -> ELet (n, t, go a, go b)
    | ESeq (a, b) -> ESeq (go a, go b)
    | EWhile (a, b) -> EWhile (go a, go b)
    | EApp (h, es) -> EApp (go h, List.map go es)
    | EFun (bs, b) -> EFun (bs, go b)
    | ERaise a -> ERaise (go a)
    | EMatch (sc, brs) -> EMatch (go sc, List.map go_branch brs)
    | ETry (a, brs) -> ETry (go a, List.map go_branch brs)
    | EIf (a, b, c) -> EIf (go a, go b, go c)
    | ECtor (n, es) -> ECtor (n, List.map go es)
    | ETuple es -> ETuple (List.map go es)
    | EOp (o, es) -> EOp (o, List.map go es)
    | ERecord (n, fs) -> ERecord (n, List.map (fun (f, e) -> (f, go e)) fs)
    | EProj (a, n, f) -> EProj (go a, n, f)
    | EDiscrim (a, n) -> EDiscrim (go a, n)
    | ECast (a, t) -> ECast (go a, t)
    | ECoerce (a, t) -> ECoerce (go a, t) in
  { e with e = e' }

(* A [BufCreate] of exactly one cell: what Pulse emits for [let mut]. *)
let is_one (e:expr) : bool =
  match e.e with EConst (CInt (1, _, _)) -> true | _ -> false

(* A constructor's field names, paired with the printed arguments.  A length
   mismatch would be an extractor bug; keeping the prefix produces a C error
   at the literal rather than a crash here. *)
let rec zip_fields (fs : list (string & cty)) (vs : list string) : list (string & string) =
  match fs, vs with
  | (f, _) :: fs, v :: vs -> (f, v) :: zip_fields fs vs
  | _ -> []

let rec c_expr (out:ref string) (ind:string) (e:expr) : ML string =
  if is_stmt e then hoist out ind e
  else match e.e with
  | EConst c -> constant c
  (* Every other use of a collapsed cell wants the pointer -- passing it to a
     function expecting a [ref], say -- and C can produce one on demand. *)
  | EVar x -> if is_cell x then "&" ^ lookup_var x else lookup_var x
  | EAny ->
    (* What an uninitialized stack slot holds.  A zero of the right type is a
       legal value of it and is what C would give a static. *)
    "(" ^ ty e.ty ^ "){0}"
  | EQual (n, _) ->
    (match SMap.try_find !externs (string_of_name n) with
     | Some t -> t
     | None -> c_name n)
  | EApp (hd, args) ->
    (* Drop the arguments that correspond to dropped parameters.  ANF has made
       every operand pure, so nothing is lost by not evaluating them. *)
    let args =
      match hd.e with
      | EQual (n, _) ->
        (match SMap.try_find !keeps (string_of_name n) with
         | Some flags -> filter_by flags args
         | None -> args)
      | _ -> args in
    (* Before printing, because a mismatch here is not something the C
       compiler will describe in terms the reader can act on: it reports "too
       few arguments" against a generated prototype. *)
    (match hd.e with
     | EQual (n, _) ->
       (match SMap.try_find !arities (string_of_name n) with
        | Some a when a <> List.length args ->
          let got = string_of_int (List.length args) in
          let want = string_of_int a in
          if List.length args < a
          then reject ("the partial application of " ^ string_of_name n)
                 ["It is applied to " ^ got ^ " of its " ^ want ^ " arguments.";
                  "The result is a closure over the arguments it did get, and \
                   C has no closures.";
                  "A top-level definition is eta-expanded to full arity \
                   automatically (section 25), so this is either a local \
                   partial application -- name it as a top-level function \
                   taking every argument -- or a definition whose body is too \
                   costly to re-evaluate at each call (section 25.3)."]
          else reject_ir ("an over-application of " ^ string_of_name n)
                 ["It takes " ^ want ^ " arguments and is applied to " ^ got ^ ".";
                  "Applying a call's result is a separate application node."]
        | _ -> ())
     | _ -> ());
    let call = c_expr out ind hd ^ "(" ^
               String.concat ", " (args |> List.map (c_expr out ind)) ^ ")" in
    (* A [void] call is a statement, not an operand.  It runs here and stands
       for the unit value, which is what the caller was going to do with it. *)
    (match hd.e with
     | EQual (n, _) when Some? (SMap.try_find !void_fns (string_of_name n)) ->
       out := !out ^ ind ^ call ^ ";\n"; unit_value
     | _ -> call)
  (* Both nodes are a C cast, but for opposite reasons: a conversion is what
     the cast *does*, and a coercion is a reinterpretation the C type system
     needs told about and the generated code does not act on. *)
  | ECast (e1, t) ->
    (match e1.ty, t with
     | TInt a, TInt b when a = b -> c_expr out ind e1
     | _ -> "(" ^ ty t ^ ")" ^ c_expr out ind e1)
  | ECoerce (e1, t) ->
    if e1.ty = t then c_expr out ind e1
    else "(" ^ ty t ^ ")" ^ c_expr out ind e1
  | EProj (e1, _, f) -> proj (c_expr out ind e1) e1.ty f
  | EDiscrim (e1, cn) ->
    (match find_ctor cn with
     | Some (d, _) -> if single_ctor d then "true"
                      else "(" ^ tag_of (c_expr out ind e1) d ^ " == " ^ c_tag cn ^ ")"
     | None -> reject ("the constructor " ^ string_of_name cn)
                 ["It belongs to no type declaration in the program."])
  | ECtor (cn, args) -> ctor_lit out ind e.ty cn args
  | ERecord (_, fs) ->
    "(" ^ ty e.ty ^ "){ " ^
    String.concat ", " (fs |> List.map (fun (f, v) ->
      "." ^ c_var f ^ " = " ^ c_expr out ind v)) ^ " }"
  | EOp ({ po_op = BufRead }, [b; i]) ->
    (match b.e with
     | EVar y when is_cell y -> lookup_var y
     | _ -> c_expr out ind b ^ "[" ^ c_expr out ind i ^ "]")
  | EOp ({ po_op = BufSub }, [b; i]) ->
    "(" ^ c_expr out ind b ^ " + " ^ c_expr out ind i ^ ")"
  | EOp ({ po_op = BufNull }, []) -> "(" ^ ty e.ty ^ ")NULL"
  | EOp ({ po_op = BufIsNull }, [b]) -> "(" ^ c_expr out ind b ^ " == NULL)"
  (* Section 44.2.  The same comparison in expression position.  [strcmp] is
     declared by the <string.h> the header already includes. *)
  | EOp (o, [a; b]) when (Eq? o.po_op || Neq? o.po_op) && is_string_ty a.ty ->
    "(strcmp(" ^ c_expr out ind a ^ ", " ^ c_expr out ind b ^ ") " ^
    (if Eq? o.po_op then "==" else "!=") ^ " 0)"
  | EOp (o, [a; b]) when Some? (infix_op o) ->
    truncate o ("(" ^ c_expr out ind a ^ " " ^ Some?.v (infix_op o) ^ " " ^
                c_expr out ind b ^ ")")
  | EOp (o, [a]) when Some? (prefix_op o) ->
    truncate o ("(" ^ Some?.v (prefix_op o) ^ c_expr out ind a ^ ")")
  | EOp (o, args) ->
    reject ("an operator applied to " ^ show (List.length args) ^ " arguments") []
  (* Section 19.12.  A *closed* lambda has been lifted to a top-level function
     by now, so one that reaches here captures something, and that is a real
     closure.  Saying so is the difference between an accurate diagnostic and
     one that sends the reader after an annotation that would not have helped
     -- the earlier message advised [@@@monomorphize] for both cases, which is
     the right advice only for this one. *)
  | EFun _ ->
    reject "a lambda that captures a local variable"
      ["C has no closures, and this one is not closed, so it cannot be lifted \
        to a top-level function (section 19.12).";
       "Mark the parameter it is passed to [@@@monomorphize] so that it is \
        specialized away (section 3.1), or name the captured values as extra \
        parameters of a top-level function."]
  | ETuple _ ->
    reject "an anonymous tuple"
      ["Tuples reach the backend as FStar.Pervasives.Native.MktupleN."]
  | ERaise _ | ETry _ ->
    reject "an exception"
      ["C has no exceptions."]
  | _ -> reject "this term" []

(* Statement-shaped, and needed as a value: give it a name.  This is what makes
   [let x = if ... ] and an allocation work in an operand position; ANF has
   already removed most of the reasons for it to trigger. *)
and hoist (out:ref string) (ind:string) (e:expr) : ML string =
  if TUnit? e.ty then (out := !out ^ emit ind D_Ignore e; unit_value) else
  let x = fresh "t" in
  let body = emit ind (D_Assign x) e in
  (* If the whole thing came out as a single assignment to the temporary, and
     evaluating it does nothing, then the temporary was only ever going to hold
     the right-hand side: use that instead.  This is what turns a record
     projection -- which reaches the backend as a one-branch match -- back into
     the projection it was. *)
  match String.split ['\n'] body with
  | [l; ""] when is_pure e && starts_with l (ind ^ x ^ " = ") ->
    String.substring l (String.length ind + String.length x + 3)
                     (String.length l - String.length ind - String.length x - 4)
  | _ -> out := !out ^ ind ^ decl_of e.ty x ^ ";\n" ^ body; x

(* The C spelling of field [f] of a value of type [t].  A single-constructor
   variant is a plain struct, so its fields are reached directly; a record's
   always are. *)
and proj (v:string) (t:cty) (f:string) : ML string =
  match t with
  | TApp (n, _) ->
    (match find_type n with
     | Some d when single_ctor d -> v ^ "." ^ c_var f
     | Some ({ dt_body = TRecord _ }) -> v ^ "." ^ c_var f
     | Some d ->
       (* A projector on a multi-constructor variant: F* only generates one
          when the field is unambiguous, so the case is determined by the
          field name. *)
       (match d.dt_body with
        | TVariant cs ->
          (match cs |> List.tryFind (fun (_, fs) ->
                         fs |> List.existsb (fun (g, _) -> g = f)) with
           | Some (cn, _) -> v ^ ".val." ^ c_var (mangled_name cn) ^ "." ^ c_var f
           | None -> reject ("the field " ^ f) ["No constructor declares it."])
        | _ -> reject ("the field " ^ f) [])
     | None -> reject ("a projection out of " ^ string_of_name n)
                 ["The type has no declaration in the program."])
  | _ -> reject ("the field " ^ f) ["Its owner is not a declared type."]

and tag_of (v:string) (d:dtype) : ML string =
  if is_enum d then v else v ^ ".tag"

(* A constructor application.  Three shapes, and each is the natural C for the
   layout its type got: an enum constant, a struct literal, a tagged union
   literal. *)
and ctor_lit (out:ref string) (ind:string) (t:cty) (cn:name) (args:list expr) : ML string =
  match find_ctor cn with
  | None -> reject ("the constructor " ^ string_of_name cn)
              ["It belongs to no type declaration in the program."]
  | Some (d, fields) ->
    let vals = args |> List.map (c_expr out ind) in
    let named = zip_fields fields vals in
    if is_enum d then c_tag cn
    else if single_ctor d then
      "(" ^ c_name d.dt_name ^ "){ " ^
      String.concat ", " (named |> List.map (fun (f, v) -> "." ^ c_var f ^ " = " ^ v)) ^ " }"
    else if Nil? fields then
      "(" ^ c_name d.dt_name ^ "){ .tag = " ^ c_tag cn ^ " }"
    else
      "(" ^ c_name d.dt_name ^ "){ .tag = " ^ c_tag cn ^ ", .val = { ." ^
      c_var (mangled_name cn) ^ " = { " ^
      String.concat ", " (named |> List.map (fun (f, v) -> "." ^ c_var f ^ " = " ^ v)) ^
      " } } }"

(* -------------------------------------------------------------------- *)
(* Statements                                                           *)
(* -------------------------------------------------------------------- *)

and finish (ind:string) (d:dest) (s:string) : ML string =
  match d with
  (* Nothing follows a [finish]: every construct hands its destination to its
     tail positions and emits no statement after them.  So in a [void]
     function the value can simply be dropped and control fall off the end --
     which is where it was going anyway. *)
  | D_Return when !void_ret ->
    if s = unit_value then "" else ind ^ "(void)(" ^ s ^ ");\n"
  | D_Return -> ind ^ "return " ^ s ^ ";\n"
  | D_Assign x -> ind ^ x ^ " = " ^ s ^ ";\n"
  (* The value is computed for its effect; the cast silences the warning that
     it is unused.  A unit constant computes nothing, so it needs neither. *)
  | D_Ignore ->
    if s = unit_value then "" else ind ^ "(void)(" ^ s ^ ");\n"

and emit (ind:string) (d:dest) (e:expr) : ML string =
  let ind' = ind ^ "  " in
  match e.e with
  (* [e1] is elaborated before [x] is bound: the IR scopes [x] over [e2] only,
     and a name reused between the two must not capture. *)
  (* A [unit] binding names the only value of its type, so there is nothing to
     store: the right-hand side runs for its effect and the variable becomes an
     alias for the constant.  Without this a [void] call would be assigned to a
     variable that C would then warn about. *)
  | ELet (x, TUnit, e1, e2) ->
    let saved = !scope in
    let s1 = emit ind D_Ignore e1 in
    bind_alias x unit_value;
    let s2 = emit ind d e2 in
    scope := saved;
    s1 ^ s2

  (* Pulse's [let mut] is a stack allocation of one cell (section 7.4), and a
     one-cell array is just a variable: reads and writes of the cell become
     uses and assignments of it, and the uses that want a pointer take its
     address, which is what a C programmer would have written.  The Pulse
     checker has already established that the cell does not outlive its scope,
     so the address is never stale. *)
  (* [let x = !r] where nothing in the rest of the term writes [r] or takes its
     address.  The read cannot go stale, so [x] is just another name for [r]
     and the copy is dead weight.  Where a write *does* follow -- the loop
     counter Pulse increments at the end of each iteration -- the copy stays,
     because it is what makes the body see the value it started with. *)
  | ELet (x, _, { e = EOp ({ po_op = BufRead }, [{ e = EVar y }; _]) }, e2)
      when is_cell y && not (mutates y e2) ->
    let saved = !scope in
    bind_alias x (lookup_var y);
    let s2 = emit ind d e2 in
    scope := saved;
    s2

  (* Section 19.10.  [let x = <stable expr> in e2] declares a second name for
     a value the backend never assigns to, and a second name is not worth a
     variable: [x] can be bound to the path itself, which is what [emit_match]
     already does for a stable scrutinee and for every pattern binding.  The
     rule below it, which drops a binding nothing reads, does not reach these
     -- the [_letpattern] of a match *is* read, by the match -- so a match
     that ends up emitting no read of its scrutinee left the declaration
     behind with no users at all, which C refuses. *)
  | ELet (x, _, e1, e2) when is_stable e1 ->
    let out = mk_ref "" in
    let path = c_expr out ind e1 in
    let saved = !scope in
    bind_alias x path;
    let s2 = emit ind d e2 in
    scope := saved;
    !out ^ s2

  (* Section 19.8: written, never read.  The writes go with the cell. *)
  | ELet (x, TRef t, { e = EOp ({ po_op = BufCreate LStack }, [init; len]) }, e2)
  | ELet (x, TBuf t, { e = EOp ({ po_op = BufCreate LStack }, [init; len]) }, e2)
      when is_one len && is_droppable init && cell_dead x e2 ->
    emit ind d (drop_writes x e2)

  | ELet (x, TRef t, { e = EOp ({ po_op = BufCreate LStack }, [init; len]) }, e2)
  | ELet (x, TBuf t, { e = EOp ({ po_op = BufCreate LStack }, [init; len]) }, e2)
      when is_one len ->
    let out = mk_ref "" in
    let iv = c_expr out ind init in
    let saved = !scope in
    let nm = bind_cell x in
    let s2 = emit ind d e2 in
    scope := saved;
    !out ^ ind ^ decl_of t nm ^ " = " ^ iv ^ ";\n" ^ s2

  (* A binding nothing reads.  A pattern match that names no field it uses
     leaves one behind -- [let _letpattern = x in ...] -- and C, told
     [-Werror=unused-variable], refuses the file over it.  [vars_of]
     over-approximates the uses, so this only fires when the name is
     definitely dead.

     What licenses dropping the initializer with it is not [is_pure] but
     something weaker, and the difference matters: [is_pure] answers "can this
     be *moved*", and a read of a collapsed cell cannot, since a later write
     changes it.  Dropping is not moving.  A read whose result nothing wants
     can always go, because reading a cell that Pulse has established is live
     does nothing observable -- which is exactly the case the report hit,
     [_letpattern] bound to a cell.  So: no calls, no writes, no allocation,
     no loops, and reads are free. *)
  | ELet (x, _, e1, e2) when is_droppable e1 && not (List.mem x (vars_of e2)) ->
    emit ind d e2

  | ELet (x, t, e1, e2) ->
    let saved = !scope in
    let s1 =
      if is_stmt e1
      then (let x = bind_var x in
            let body =
              let saved' = !scope in
              scope := saved;
              let s = emit ind (D_Assign x) e1 in
              scope := saved'; s in
            (* A declaration and its only assignment, next to each other, are
               one definition.  Nothing moves, so this needs no purity side
               condition. *)
            match String.split ['\n'] body with
            | [l; ""] when starts_with l (ind ^ x ^ " = ") ->
              ind ^ decl_of t x ^
              String.substring l (String.length ind + String.length x)
                               (String.length l - String.length ind - String.length x) ^
              "\n"
            | _ -> ind ^ decl_of t x ^ ";\n" ^ body)
      else (let out = mk_ref "" in
            let v = c_expr out ind e1 in
            let x = bind_var x in
            !out ^ ind ^ decl_of t x ^ " = " ^ v ^ ";\n") in
    let s2 = emit ind d e2 in
    scope := saved;
    s1 ^ s2

  | ESeq (e1, e2) -> emit ind D_Ignore e1 ^ emit ind d e2

  | EIf (c, t, f) ->
    let out = mk_ref "" in
    let cs = c_expr out ind c in
    let tt = emit ind' d t in
    let ft = emit ind' d f in
    (* An empty arm is not worth a pair of braces.  When it is the [then] arm,
       negating the condition is what removes it -- which happens whenever a
       branch's only job is to fall through, as an [if] with no [else] in the
       source does.  When it is *both*, the test is not worth emitting either:
       [c_expr] has already hoisted whatever evaluating the condition does
       into [out], so what is left of it is pure and discarding it changes
       nothing.  Pulse's [return] compiles to a flag and a test of that flag
       around the rest of the block, so a [return] in the last position leaves
       exactly this behind. *)
    !out ^
    (if tt = "" && ft = "" then ""
     else if tt = "" then ind ^ "if (" ^ negate cs ^ ")" ^ brace ind ft
     else ind ^ "if (" ^ unparen cs ^ ")" ^ brace ind tt ^
          (if ft = "" then "" else ind ^ "else" ^ brace ind ft))

  | EMatch (scrut, brs) -> emit_match ind d scrut brs

  (* Pulse's loop (section 7.4).  The condition is a computation, not an
     expression, so it goes inside the loop and the exit is a [break]. *)
  | EWhile (c, body) ->
    let out = mk_ref "" in
    let cs = c_expr out ind' c in
    ind ^ "while (true) {\n" ^ !out ^
    ind' ^ "if (" ^ negate cs ^ ") { break; }\n" ^
    emit ind' D_Ignore body ^
    ind ^ "}\n" ^
    (match d with D_Ignore -> "" | _ -> finish ind d unit_value)

  (* Control does not reach here.  [abort] is [_Noreturn], so no [return]
     has to follow it even in a value position. *)
  | EAbort s -> ind ^ "/* " ^ escape s ^ " */\n" ^ ind ^ "abort();\n"

  | EOp ({ po_op = BufCreate lt }, [init; len]) ->
    emit_alloc ind d lt e.ty init len

  | EOp ({ po_op = BufWrite }, [b; i; v]) ->
    let out = mk_ref "" in
    let lhs =
      match b.e with
      | EVar y when is_cell y -> lookup_var y
      | _ -> c_expr out ind b ^ "[" ^ c_expr out ind i ^ "]" in
    let v = c_expr out ind v in
    !out ^ ind ^ lhs ^ " = " ^ v ^ ";\n" ^ unit_result ind d

  (* Pulse emits a matching "free" for a stack allocation too.  A collapsed
     cell is freed by leaving the scope, so there is nothing to say. *)
  | EOp ({ po_op = BufFree }, [{ e = EVar y }]) when is_cell y ->
    unit_result ind d

  | EOp ({ po_op = BufFree }, [b]) ->
    let out = mk_ref "" in
    let b = c_expr out ind b in
    !out ^ ind ^ "free(" ^ b ^ ");\n" ^ unit_result ind d

  | EOp ({ po_op = BufBlit }, [src; si; dst; di; len]) ->
    let out = mk_ref "" in
    let elt = match dst.ty with
              | TBuf e | TRef e -> ty e
              | _ -> reject "a blit whose destination is not a pointer" [] in
    let srcv = c_expr out ind src in
    let siv = c_expr out ind si in
    let dstv = c_expr out ind dst in
    let div = c_expr out ind di in
    let lenv = c_expr out ind len in
    (* [group] and not a hand-written pair: section 41.1.  The length is
       almost always already parenthesized -- a literal, a cast, a field of a
       struct -- and a second pair around it is what section 32.10's gate
       rejects. *)
    !out ^ ind ^ "memmove(" ^ dstv ^ " + " ^ div ^ ", " ^ srcv ^ " + " ^ siv ^
    ", " ^ group lenv ^ " * sizeof(" ^ elt ^ "));\n" ^ unit_result ind d

  | _ ->
    let out = mk_ref "" in
    let s = c_expr out ind e in
    !out ^ finish ind d s

and unit_result (ind:string) (d:dest) : ML string =
  match d with D_Ignore -> "" | _ -> finish ind d unit_value

(* [BufCreate] is [init; len]: a run of [len] copies of [init].  A stack
   allocation is a local array -- a variable-length one when the length is not
   a constant, which C99 has and both target compilers implement -- and a heap
   allocation is [malloc].  Either way the run has to be filled, since C
   initializes neither. *)
and emit_alloc (ind:string) (d:dest) (lt:lifetime) (t:cty) (init:expr) (len:expr) : ML string =
  let out = mk_ref "" in
  let iv = c_expr out ind init in
  let lv = c_expr out ind len in
  let elt = match t with
            | TBuf e | TRef e -> ty e
            | _ -> reject "an allocation whose result is not a pointer" [] in
  let arr = fresh "buf" in
  let i = fresh "i" in
  let elt_of = match t with TBuf e | TRef e -> e | _ -> t in
  (* Same collapse as the [ELet] case above, for a one-cell stack allocation
     that is not bound to a name: the pointer the caller wanted is the address
     of the variable. *)
  if LStack? lt && is_one len then
    !out ^ ind ^ decl_of elt_of arr ^ " = " ^ iv ^ ";\n" ^
    finish ind d ("&" ^ arr)
  else
  let alloc =
    match lt with
    | LStack -> ind ^ decl_of elt_of (arr ^ "[" ^ lv ^ "]") ^ ";\n"
    | LHeap ->
      ind ^ elt ^ " *" ^ arr ^ " = (" ^ elt ^ " *)malloc(" ^ group lv ^
      " * sizeof(" ^ elt ^ "));\n" ^
      ind ^ "if (" ^ arr ^ " == NULL) { abort(); }\n" in
  !out ^ alloc ^
  ind ^ "for (size_t " ^ i ^ " = 0; " ^ i ^ " < (size_t)" ^ group lv ^ "; " ^ i ^ "++) {\n" ^
  ind ^ "  " ^ arr ^ "[" ^ i ^ "] = " ^ iv ^ ";\n" ^
  ind ^ "}\n" ^
  finish ind d arr

(* -------------------------------------------------------------------- *)
(* Matching                                                             *)
(* -------------------------------------------------------------------- *)

(* A pattern becomes a list of tests on the scrutinee and a list of bindings
   introduced by it, both expressed as C against a *path* -- the C expression
   that reaches the sub-value the pattern is matching.  Compiling to an
   if/else chain rather than a [switch] is what lets a nested pattern, a
   constant pattern and a variable pattern all be handled by one mechanism. *)
and pat_tests (path:string) (t:cty) (p:pat)
    : ML (list string & list (string & string)) =
  match p with
  | PWild -> ([], [])
  | PVar x -> ([], [(x, path)])
  (* Section 44.2.  A string pattern is a test on contents, not on address:
     [pat_tests] is handed the type of the path, so it can see the difference
     without looking at the constant. *)
  | PConst (CString v) when is_string_ty t ->
    (["strcmp(" ^ path ^ ", " ^ constant (CString v) ^ ") == 0"], [])
  | PConst c -> ([path ^ " == " ^ constant c], [])
  | PTuple _ ->
    reject "an anonymous tuple pattern"
      ["Tuples reach the backend as FStar.Pervasives.Native.MktupleN."]
  | POr _ ->
    reject "a pattern disjunction"
      ["Split the branch into one per alternative."]
  (* A record's fields are reached by name off the same path a
     single-constructor [PCtor]'s are, and there is no tag to test. *)
  | PRecord (tn, fs) ->
    (match find_type tn with
     | Some ({ dt_body = TRecord fields }) ->
       fs |> List.fold_left (fun (ts, bs) (f, q) ->
         let ft = (match fields |> List.tryFind (fun (g, _) -> g = f) with
                   | Some (_, ft) -> ft
                   | None -> TAny) in
         let t1, b1 = pat_tests (path ^ "." ^ c_var f) ft q in
         (ts @ t1, bs @ b1)) ([], [])
     | _ -> reject ("the record type " ^ string_of_name tn)
              ["It belongs to no record declaration in the program."])
  | PCtor (cn, ps) ->
    (match find_ctor cn with
     | None -> reject ("the constructor " ^ string_of_name cn)
                 ["It belongs to no type declaration in the program."]
     | Some (d, fields) ->
       let tests = if single_ctor d then []
                   else [tag_of path d ^ " == " ^ c_tag cn] in
       let sub (f:string) : ML string =
         if single_ctor d then path ^ "." ^ c_var f
         else path ^ ".val." ^ c_var (mangled_name cn) ^ "." ^ c_var f in
       let rec go (fs : list (string & cty)) (ps : list pat)
                : ML (list string & list (string & string)) =
         match fs, ps with
         | (f, ft) :: fs, p :: ps ->
           let t1, b1 = pat_tests (sub f) ft p in
           let t2, b2 = go fs ps in
           (t1 @ t2, b1 @ b2)
         | _ -> ([], []) in
       let t2, b2 = go fields ps in
       (tests @ t2, b2))

and drop_indent (l:string) : ML string =
  if String.length l > 0 && String.substring l 0 1 = " "
  then drop_indent (String.substring l 1 (String.length l - 1))
  else l

(* The body of an [if] or an [else], which the caller has emitted at [ind ^
   "  "].  A single statement does not need a block, and one statement per
   line is an invariant of this printer, so a body with one newline in it is
   one statement.  Nothing that could dangle is ever unbraced: a nested [if]
   spans more than a line. *)
and brace (ind:string) (body:string) : ML string =
  let lines = String.split ['\n'] body in
  match lines with
  | [""] -> " { }\n"
  | [l; ""] -> " " ^ drop_indent l ^ "\n"
  | _ -> " {\n" ^ body ^ ind ^ "}\n"

and starts_with (s:string) (pre:string) : ML bool =
  String.length s >= String.length pre &&
  String.substring s 0 (String.length pre) = pre

and guard_rejected (#a:Type) () : ML a =
  reject "a pattern guard"
    ["Rewrite the guard as an 'if' in the branch body."]

and emit_match (ind:string) (d:dest) (scrut:expr) (brs:list branch) : ML string =
  let out = mk_ref "" in
  let sv = c_expr out ind scrut in
  (* Branches whose body only aborts are gone by now (section 5.6); what is
     left is an empty match, which cannot be entered. *)
  if Nil? brs then !out ^ finish ind D_Ignore sv ^ ind ^ "abort();\n" else
  (* The scrutinee is tested once per branch, so it has to be a name -- unless
     no branch looks at it, in which case naming it would leave an unused
     variable behind.  That happens for a single catch-all branch, which is
     what a [let] over an irrefutable pattern turns into. *)
  (* The scrutinee is read once per test and once per binding, so it normally
     has to be named.  When it is already a name -- or a projection out of one,
     which the backend never assigns to -- naming it again would only add an
     indirection. *)
  let direct = is_stable scrut in
  let x = if direct then sv else fresh "s" in
  let ind' = ind ^ "  " in
  (* The bindings of a branch are aliases, not declarations (see
     [bind_alias]), so a branch body is emitted with them in scope and the
     scope is restored afterwards. *)
  let branch_body (bi:string) (p:pat) (b:expr) : ML string =
    let saved = !scope in
    let _, binds = pat_tests x scrut.ty p in
    binds |> List.iter (fun (v, path) -> bind_alias v path);
    let body = emit bi d b in
    scope := saved;
    body in
  (* A branch whose body emits nothing is an empty block, which is worth
     removing for the same reason [EIf] already removes an empty arm.  Two
     things make it less free than it looks.  It is sound only at the *end* of
     the chain: dropping an empty [else if (c) {}] from the middle would let
     the inputs that satisfied [c] fall through to a later arm.  And the arm
     that becomes last has to keep its test, because it is no longer the arm
     that runs when nothing else did -- it is one of several, with the
     do-nothing cases now falling off the end.

     A unit-valued match with several unit branches is where these come from,
     and Pulse writes them all the time: only one case of a session state does
     anything, and the rest return [()]. *)
  (* Whether a body emits anything is easiest to answer by emitting it, but a
     trial emission must leave nothing behind: [fresh] and the name allocator
     are counters, and letting them run would renumber the variables of the
     branch that is kept ([ns] would come out as [ns_3]).  [scope] is already
     saved by [branch_body]; these two are saved here. *)
  let emits_nothing (p:pat) (b:expr) : ML bool =
    let saved_ctr = !ctr in
    let saved_declared = SMap.copy !declared in
    let s = branch_body ind' p b in
    ctr := saved_ctr;
    declared := saved_declared;
    s = "" in
  let rec trim (rbs:list branch) : ML (list branch) =
    match rbs with
    | (p, _, b) :: rest when emits_nothing p b -> trim rest
    | _ -> rbs in
  let kept = List.rev (trim (List.rev brs)) in
  let all_tested = List.length kept < List.length brs in
  (* Nothing left to run at all: the match is just its scrutinee. *)
  if Nil? kept then !out ^ finish ind D_Ignore sv else
  (* The scrutinee is read once per test and once per binding, so it normally
     has to be named.  When it is already a name -- or a projection out of one,
     which the backend never assigns to -- naming it again would only add an
     indirection.  When no surviving branch looks at it, naming it would leave
     an unused variable behind; that happens for a single catch-all branch,
     which is what a [let] over an irrefutable pattern turns into. *)
  let looked_at =
    kept |> List.existsb (fun (p, _, _) ->
      let ts, bs = pat_tests x scrut.ty p in
      Cons? ts || Cons? bs) in
  if not looked_at then
    (match kept with
     | (_, None, b) :: _ -> !out ^ finish ind D_Ignore sv ^ emit ind d b
     | _ -> !out ^ finish ind D_Ignore sv ^ ind ^ "abort();\n")
  else
  let head = if direct then !out
             else !out ^ ind ^ decl_of scrut.ty x ^ " = " ^ sv ^ ";\n" in
  let rec go (first:bool) (brs:list branch) : ML string =
    (* The arm that runs when no earlier one did.  With no [if] before it there
       is nothing to attach a block to, so it is emitted flat -- otherwise the
       rest of the function would sit inside a pair of braces that says
       nothing. *)
    let last (p:pat) (b:expr) : ML string =
      if first then branch_body ind p b
      else ind ^ "else" ^ brace ind (branch_body ind' p b) in
    match brs with
    | [] -> ""
    (* F* has already checked that the match is exhaustive, so the last branch
       is the one that runs when no earlier one did: its tests would always
       succeed, and testing them anyway would only add a branch C cannot see
       is dead.  This is the same reasoning that lets a projector be emitted
       without a tag check.  Unless arms were trimmed, in which case it is not
       the last branch of the match any more. *)
    | [(p, g, b)] when not all_tested ->
      if Some? g then guard_rejected ();
      last p b
    | (p, g, b) :: rest ->
      if Some? g then guard_rejected ();
      let tests, _ = pat_tests x scrut.ty p in
      (* Irrefutable, so it is the last branch that can run; anything after it
         is dead and C would warn about it. *)
      if Nil? tests then last p b
      else
        (if first then ind else ind ^ "else ") ^
        "if (" ^ String.concat " && " tests ^ ")" ^
        brace ind (branch_body ind' p b) ^
        go false rest in
  head ^ go true kept

(* -------------------------------------------------------------------- *)
(* Declarations                                                         *)
(* -------------------------------------------------------------------- *)

(* Would a value of [t] contain a value of the type being defined?  C has no
   way to store that, and karamel's answer -- box the recursive occurrence --
   is a representation decision that belongs in the layout pass, not here. *)
let rec occurs (target:string) (fuel:int) (t:cty) : ML bool =
  if fuel <= 0 then false else
  match t with
  | TApp (n, _) ->
    string_of_name n = target ||
    (match find_type n with
     | Some d -> body_occurs target (fuel - 1) d.dt_body
     | None -> false)
  | TTuple ts -> ts |> List.existsb (occurs target (fuel - 1))
  (* A pointer is a size; what it points to is not part of this value. *)
  | _ -> false

and body_occurs (target:string) (fuel:int) (b:tydef) : ML bool =
  match b with
  | TAbbrev c -> occurs target fuel c
  | TRecord fs -> fs |> List.existsb (fun (_, c) -> occurs target fuel c)
  | TVariant cs ->
    cs |> List.existsb (fun (_, fs) -> fs |> List.existsb (fun (_, c) -> occurs target fuel c))
  | TAbstract -> false

let check_finite (d:dtype) : ML unit =
  if body_occurs (string_of_name d.dt_name) 100 d.dt_body then
    reject ("the recursive datatype " ^ string_of_name d.dt_name)
      ["A C struct cannot contain itself by value.";
       "Use an explicit pointer (a Pulse ref, array or box) for the \
        recursive field."]

(* Every struct Custard emits carries a *tag*, and every one is
   forward-declared before any of them is defined.

   A type that reaches itself through a pointer -- a [ref t] or a [t *] inside
   a [t], which is how every tree and every linked structure is written -- is
   perfectly good C, and [check_finite] above lets it through for that reason.
   But the field mentioning it is written before the type it names exists, so
   the name has to be introduced first, and an anonymous
   [typedef struct { ... } t;] offers nowhere to do that: there is no tag to
   forward-declare.  So the definition is [struct t_s { ... };], with
   [typedef struct t_s t;] hoisted above every definition.

   Only a struct needs this.  An enum cannot be recursive, and C has no
   incomplete enum type to forward-declare anyway; a typedef of a pointer is
   already fine, because the forward declarations precede it. *)
let struct_tag (n:string) : string = n ^ "_s"

let is_struct (d:dtype) : ML bool =
  match d.dt_body with
  | TRecord _ -> true
  | TVariant _ -> not (is_enum d)
  | TAbbrev _ | TAbstract -> false

let type_fwd (d:dtype) : ML (option string) =
  if Some? (builtin_type d.dt_name) then None else
  if is_struct d
  then let n = c_name d.dt_name in
       Some ("typedef struct " ^ struct_tag n ^ " " ^ n ^ ";\n")
  else None

(* The types [d] must see the *definition* of, not merely the name.

   A field held by value needs a complete type: the compiler has to know its
   size to lay out the struct containing it.  A field held through a pointer
   does not, which is what the forward declarations above are for, and it is
   also the only way a cycle can arise -- [check_finite] rejects a by-value
   cycle outright.  So the by-value edges form a DAG, and emitting the
   definitions in one of its topological orders is always possible.

   The order Custard receives is the SCC pass's, which is computed over *all*
   dependencies.  A pointer edge is one of those, so a group that is cyclic
   through pointers is an SCC, and the order within it is arbitrary -- which
   is exactly where a by-value field can end up ahead of its definition.
   EverParse's [cbor_array] holding a [slice cbor_raw] by value, in a group
   made cyclic by [cbor_raw] pointing back, is the reported case. *)
let rec value_deps (t:cty) : ML (list string) =
  match t with
  | TApp (n, args) -> string_of_name n :: List.collect value_deps args
  | TTuple ts -> List.collect value_deps ts
  (* A pointer is a size, and a function is a pointer: an incomplete type is
     enough to declare either. *)
  | TBuf _ | TRef _ | TArrow _ -> []
  | _ -> []

let body_value_deps (b:tydef) : ML (list string) =
  match b with
  | TAbbrev c -> value_deps c
  | TRecord fs -> fs |> List.collect (fun (_, c) -> value_deps c)
  | TVariant cs ->
    cs |> List.collect (fun (_, fs) -> fs |> List.collect (fun (_, c) -> value_deps c))
  | TAbstract -> []

(* A depth-first emit in the original order, each type preceded by the ones it
   holds by value.  Stable: a type with no unmet dependency keeps its place,
   so the diff against the previous output stays small.

   [busy] guards against a by-value cycle rather than trusting that
   [check_finite] has already run -- it runs from [type_decl], which is below
   this -- and a cycle here would not terminate.  Leaving the node for the
   caller to place is the right recovery: [check_finite] will reject it with a
   message about the source, which is more use than one about this traversal. *)
let sort_types (ds:list dtype) : ML (list dtype) =
  let index : SMap.t dtype = SMap.create 64 in
  ds |> List.iter (fun d -> SMap.add index (string_of_name d.dt_name) d);
  let out : ref (list dtype) = mk_ref [] in
  let seen : SMap.t bool = SMap.create 64 in
  let busy : SMap.t bool = SMap.create 64 in
  let rec visit (d:dtype) : ML unit =
    let k = string_of_name d.dt_name in
    if Some? (SMap.try_find seen k) || Some? (SMap.try_find busy k) then () else begin
      SMap.add busy k true;
      body_value_deps d.dt_body |> List.iter (fun n ->
        match SMap.try_find index n with
        | Some d' -> visit d'
        | None -> ());
      SMap.remove busy k;
      SMap.add seen k true;
      out := d :: !out
    end
  in
  ds |> List.iter visit;
  List.rev !out

let type_decl (d:dtype) : ML (option string) =
  if Some? (builtin_type d.dt_name) then None else
  let n = c_name d.dt_name in
  let open_struct () : string = "struct " ^ struct_tag n ^ " {\n" in
  match d.dt_body with
  | TAbstract -> None
  | TAbbrev c -> Some ("typedef " ^ decl_of c n ^ ";\n")
  | TRecord fs ->
    check_finite d;
    Some (open_struct () ^
          String.concat "" (fs |> List.map (fun (f, c) ->
            "  " ^ decl_of c (c_var f) ^ ";\n")) ^
          "};\n")
  | TVariant cs ->
    check_finite d;
    if is_enum d then
      Some ("typedef enum {\n" ^
            String.concat ",\n" (cs |> List.map (fun (c, _) -> "  " ^ c_tag c)) ^
            "\n} " ^ n ^ ";\n")
    else if single_ctor d then
      let _, fs = List.hd cs in
      Some (open_struct () ^
            String.concat "" (fs |> List.map (fun (f, c) ->
              "  " ^ decl_of c (c_var f) ^ ";\n")) ^
            "};\n")
    else
      (* A tagged union.  The per-constructor structs are anonymous members of
         one union, named after the constructor, so that a use site can name a
         field knowing only the constructor -- which after monomorphization it
         always does. *)
      let nonempty = cs |> List.filter (fun (_, fs) -> Cons? fs) in
      Some (open_struct () ^
            "  enum {\n" ^
            String.concat ",\n" (cs |> List.map (fun (c, _) -> "    " ^ c_tag c)) ^
            "\n  } tag;\n" ^
            (match nonempty with
             | [] -> ""
             | _ ->
               "  union {\n" ^
               String.concat "" (nonempty |> List.map (fun (c, fs) ->
                 "    struct {\n" ^
                 String.concat "" (fs |> List.map (fun (f, t) ->
                   "      " ^ decl_of t (c_var f) ^ ";\n")) ^
                 "    } " ^ c_var (mangled_name c) ^ ";\n")) ^
               "  } val;\n") ^
            "};\n")

let kept_binders (l:dlet) : ML (list binder) =
  match SMap.try_find !keeps (string_of_name l.dl_name) with
  | Some flags -> filter_by flags l.dl_binders
  | None -> l.dl_binders

(* The C signature of a definition, without the trailing [;] or body. *)
let signature (l:dlet) : ML string =
  let args =
    match kept_binders l with
    | [] -> "void"
    | bs -> String.concat ", " (bs |> List.map (fun b -> decl_of b.b_ty (lookup_var b.b_name))) in
  let hd = c_name l.dl_name ^ "(" ^ args ^ ")" in
  if TUnit? l.dl_ret then "void " ^ hd else decl_of l.dl_ret hd

(* A definition with no parameters is a C *variable*, not a function of no
   arguments, and C requires the initializer of one with static storage
   duration to be a constant expression -- which the body of an arbitrary F*
   definition is not.

   Most of them are, though.  A global whose body is a literal, or a cast of
   one, is initialized where it is declared, so that the linker puts it in
   [.data] or [.rodata] and nothing runs before [main]; anything else is
   declared uninitialized and assigned by [custard_init_globals], which the
   generated [main] calls before anything else and which a program embedding
   this translation unit has to call itself.  This is what karamel's
   [krmlinit_globals] does, for the same reason -- karamel just always takes
   the second road.

   The subset recognized here is deliberately small.  C's own notion of a
   constant expression is wider (arithmetic on literals is one), but a
   constant *initializer* is checked by the compiler rather than evaluated at
   runtime, so anything admitted here that C does not accept is a build
   failure rather than a slower program.  A struct or array initializer is
   left out for a sharper reason: the compound literal Custard emits for one
   is not a constant expression at file scope, however constant its
   contents. *)
let rec static_init (x:expr) : ML (option string) =
  match x.e with
  | EConst c ->
    (match c with
     | CInt (_, _, None) -> None
     | _ -> Some (constant c))
  | ECast (e1, t) ->
    (match e1.ty, t, static_init e1 with
     | TInt a, TInt b, Some v when a = b -> Some v
     | _, _, Some v -> Some ("(" ^ ty t ^ ")" ^ v)
     | _ -> None)
  | ECoerce (e1, t) ->
    (match static_init e1 with
     | Some v -> if e1.ty = t then Some v else Some ("(" ^ ty t ^ ")" ^ v)
     | None -> None)
  (* A null pointer constant, which is what an uninitialized buffer global is
     and the one aggregate-typed thing on this list. *)
  | EOp ({ po_op = BufNull }, []) -> Some ("(" ^ ty x.ty ^ ")NULL")
  | _ -> None

let has_static_init (l:dlet) : ML bool =
  current := string_of_name l.dl_name;
  Some? (static_init l.dl_body)

let global_decl (l:dlet) : ML string =
  current := string_of_name l.dl_name;
  let d = decl_of l.dl_ret (c_name l.dl_name) in
  match static_init l.dl_body with
  | Some v -> d ^ " = " ^ v ^ ";\n"
  | None -> d ^ ";\n"

let global_init (l:dlet) : ML string =
  current := string_of_name l.dl_name;
  ctr := 0;
  void_ret := false;
  reset_scope ();
  emit "  " (D_Assign (c_name l.dl_name)) l.dl_body

let let_decl (l:dlet) : ML string =
  current := string_of_name l.dl_name;
  ctr := 0;
  void_ret := TUnit? l.dl_ret;
  reset_scope ();
  kept_binders l |> List.iter (fun b -> let _ = bind_var b.b_name in ());
  if Nil? l.dl_binders then
    reject ("the top-level value " ^ string_of_name l.dl_name)
      ["C has no way to initialize a global from a computation.";
       "Make it a function of unit."];
  let used = vars_of l.dl_body in
  (* C also warns about an unused *parameter*, and a definition's parameters
     have to be named, so the ones the body never mentions are voided
     explicitly. *)
  let voids = String.concat "" (kept_binders l |> List.collect (fun b ->
    if List.existsb (fun y -> y = b.b_name) used then []
    else ["  (void)" ^ lookup_var b.b_name ^ ";\n"])) in
  signature l ^ " {\n" ^ voids ^ emit "  " D_Return l.dl_body ^ "}\n"

(* An external is a symbol someone else defines.  When it comes with a header
   we include the header and say nothing more; otherwise we declare it from
   its Custard type, which is exactly the contract the hand-written C has to
   meet. *)
(* The argument types of an arrow spine, left to right, and what it returns. *)
let rec arg_ctys (t:cty) : ML (list cty) =
  match t with
  | TArrow (a, _, b) -> a :: arg_ctys b
  | _ -> []

let rec ret_cty (t:cty) : ML cty =
  match t with
  | TArrow (_, _, b) -> ret_cty b
  | _ -> t

let extern_decl (x:dexternal) : ML (option string) =
  if Some? x.dx_header then None else
  let nm = match SMap.try_find !externs (string_of_name x.dx_name) with
           | Some t -> t
           | None -> c_name x.dx_name in
  current := string_of_name x.dx_name;
  let rec spine (t:cty) (acc:list cty) : ML (option (list cty & cty)) =
    match t with
    | TArrow (a, _, b) -> spine b (a :: acc)
    | _ -> (match acc with [] -> None | _ -> Some (List.rev acc, t)) in
  match spine x.dx_ty [] with
  | Some (args, ret) ->
    (* The unit parameters the call sites drop have to go from the prototype
       too, and an argument list that empties out is spelled [void] -- an empty
       one in C means "unspecified", which -Wstrict-prototypes objects to and
       which would hide a real arity mismatch. *)
    let args = args |> List.filter (fun a -> not (TUnit? a)) in
    let params = match args with
                 | [] -> "void"
                 | _ -> String.concat ", " (args |> List.map ty) in
    let hd = nm ^ "(" ^ params ^ ")" in
    Some ("extern " ^ (if TUnit? ret then "void " ^ hd else decl_of ret hd) ^ ";\n")
  | None -> Some ("extern " ^ decl_of x.dx_ty nm ^ ";\n")

(* -------------------------------------------------------------------- *)
(* The file                                                             *)
(* -------------------------------------------------------------------- *)

let rec dedup (xs : list string) : ML (list string) =
  match xs with
  | [] -> []
  | x :: rest -> x :: dedup (rest |> List.filter (fun y -> y <> x))

(* A declaration is part of this translation unit's *interface* exactly when
   something outside the unit can name it: that is, when it is a [Root].  A
   root exists because [--custard_entry] or [--custard_entry_module] said so,
   and saying so is the only way a caller Custard cannot see gets in.

   Everything else is [static].  That is not cosmetic: without it a
   whole-program C file exports every definition it happens to contain, so
   linking two of them together is a symbol collision, and no definition can
   be inlined across a call by a compiler that must assume some other unit
   might call it.

   It is also why the [Entrypoint] is *not* public.  [--custard_main] makes
   its target a [Root] so that one option is enough to keep a program alive
   (see [Driver.run_phases]), but that root exists for dead-code elimination
   and not for the linker: the generated [main] calls the entry point from
   inside this file, and a standalone program's interface is [main].  Naming
   the same definition with [--custard_entry] as well does not export it
   either, which is the one case this rule gets wrong and the one nobody has
   asked for.

   Every declaration that survives dead-code elimination is reachable from a
   root or from the entry point, so a [static] one is always called from
   within the file and [-Wunused-function] has nothing to report.

   [Private] overrides the whole rule.  Section 36.3's [lift_named] has to set
   [Root] on what it lifts -- the declaration exists only because a rule made
   it, so nothing else can keep it alive -- but a lifted function is usually
   an implementation detail of the call the rule emitted, not an export.  A
   rule that wants it [static] passes [Private] and gets it. *)
let no_unit : unit_info = { cu_name = None; cu_headers = []; cu_inits = [] }

(* Section 42.3.  One fixed name per unit is a duplicate symbol the moment two
   units are linked, so [--custard_unit] namespaces it.  With no unit name the
   old spelling is kept, so a whole-program output is unchanged. *)
let init_name (cu:unit_info) : ML string =
  match cu.cu_name with
  | Some u -> sanitize u ^ "_init_globals"
  | None   -> "custard_init_globals"

(* A declaration a linked unit compiled is present so that the printer's tables
   see its shape, and is emitted by nobody: the header it came from is included
   instead (section 42.2). *)
let local (d:decl) : ML bool = None? (imported_unit d)

(* The globals this unit has to set up at startup.  Shared by the printer and
   by {!init_globals_name}, so that what the interface promises and what the
   source defines cannot drift apart. *)
let global_inits_of (p:program) : ML (list dlet) =
  p |> List.collect (fun d ->
    if not (local d) then [] else
    match d with
    | DLet l when Nil? l.dl_binders && not (has_static_init l) -> [l]
    | _ -> [])

let init_globals_name (cu:unit_info) (p:program) : ML (option string) =
  if Cons? (global_inits_of p) then Some (init_name cu) else None

let is_public (l:dlet) : ML bool =
  l.dl_flags |> List.existsb Root? &&
  not (l.dl_flags |> List.existsb Entrypoint?) &&
  not (l.dl_flags |> List.existsb Private?)

let storage (l:dlet) : ML string =
  if is_public l then "" else "static "

(* Section 36.3.  Decoration a plugin asked for and Custard does not read.
   [Prologue] goes on the *declaration* as well as the definition: CUDA wants
   [__global__] on both, and a qualifier that appears on one and not the other
   is a redeclaration error rather than a missing qualifier, which is the
   better failure of the two.  [Epilogue] follows the definition only, since
   there is nothing after a prototype for it to attach to. *)
let prologue_of (l:dlet) : ML string =
  String.concat "" (l.dl_flags |> List.collect
    (function Prologue s -> [s ^ "\n"] | _ -> []))

let epilogue_of (l:dlet) : ML string =
  String.concat "" (l.dl_flags |> List.collect
    (function Epilogue s -> [s ^ "\n"] | _ -> []))

(* Custard's own [Inline] means "substitute this and emit nothing", which is a
   decision; this one is a request to the C compiler and leaves the definition
   where it is. *)
let inline_of (l:dlet) : ML string =
  if l.dl_flags |> List.existsb CInline? then "inline " else ""

let comment_of (l:dlet) : ML string =
  String.concat "" (l.dl_flags |> List.collect
    (function Comment c -> ["/* " ^ c ^ " */\n"] | _ -> []))

(* Section 32.4.  Build the [--custard_c_no_prefix] map.

   The set this may touch is exactly {!is_public}: a definition with external
   linkage, declared in the header, named by [--custard_entry] or
   [--custard_entry_module].  Naming a definition that way is already the only
   way a caller Custard cannot see gets in, so the public surface is a
   decision the user has made rather than one inferred here.

   It is also, and not by coincidence, the set with no specialization hint.  A
   root is named by lid, so its key has no [Mono] arguments, so [n.spec] is
   [None].  The check below is on [n.spec] and not on the flag, because the
   guarantee wanted is about the *name* -- section 30.15's hints are bounded,
   collision-suffixed and free to change when the monomorphizer's input
   changes, and nothing outside the translation unit may depend on one.

   A rename collides when two definitions want one name, or when the name
   wanted is already some other definition's.  Both are error 374 rather than
   a silent suffix: the whole point of the option is that the caller writes
   the name, so producing a name the caller did not ask for is worse than
   refusing. *)
let build_renames (p:program) : ML unit =
  let mods = Options.custard_c_no_prefix () in
  renames := SMap.create 0;
  if Nil? mods then () else begin
    (* Every C name in the unit as it stands, so that a rename cannot land on
       one.  Types and constructors included: they have no linkage, but a
       [struct] tag and a function sharing a name in one header is at best
       confusing and at worst -- for a typedef -- a redeclaration error. *)
    let taken : SMap.t string = SMap.create 50 in
    p |> List.iter (fun d ->
      let n = name_of_decl d in
      SMap.add taken (escape_kw (sanitize (mangled_name n)))
                     (string_of_name n));
    let claimed : SMap.t string = SMap.create 20 in
    let used_mod : SMap.t bool = SMap.create 5 in
    (* Section 32.9.  A declaration is renamed when it is part of the unit's
       interface.  For a definition that is external linkage, which is
       {!is_public}.  A *type* has no linkage at all, so there is nothing for
       that test to mean -- but the header carries the unit's whole type
       language (see the note above [hdr]), and a consumer that includes the
       header and cannot spell the type of what it just called does not have
       an API.  So a type of a named module is renamed too, and so are its
       constructors, whose enum tags are equally part of what the header
       exports.  [struct_tag] derives from [c_name], so the struct tags
       follow.  A specialization is excluded here as everywhere. *)
    let renamable (d:decl) : ML (option name) =
      match d with
      | DLet l -> if is_public l then Some l.dl_name else None
      | DType t -> Some t.dt_name
      | _ -> None in
    let ctors_of (d:decl) : ML (list name) =
      match d with
      | DType ({ dt_body = TVariant cs }) -> cs |> List.map fst
      | _ -> [] in
    p |> List.collect (fun d ->
      match renamable d with
      | Some n -> (n, d) :: (ctors_of d |> List.map (fun c -> (c, d)))
      | None -> [])
    |> List.iter (fun (dn, _) ->
      match () with
      | _ when None? dn.spec ->
        let m = String.concat "." dn.ns in
        if List.existsb (fun x -> x = m) mods then begin
          SMap.add used_mod m true;
          let tgt = escape_kw (sanitize dn.id) in
          let src = string_of_name dn in
          (match SMap.try_find claimed tgt with
           | Some other ->
             E.raise_error0 E.Error_CustardExportCollision [
               text ("Custard: --custard_c_no_prefix would name both " ^
                     other ^ " and " ^ src ^ " `" ^ tgt ^
                     "' in the generated C.");
               text "Two definitions cannot share one external name."; ]
           | None -> ());
          (match SMap.try_find taken tgt with
           | Some other when other <> src ->
             E.raise_error0 E.Error_CustardExportCollision [
               text ("Custard: --custard_c_no_prefix would name " ^ src ^
                     " `" ^ tgt ^ "', which is already the name of " ^
                     other ^ ".");
               text "Rename one of them, or drop the option for this \
module."; ]
           | _ -> ());
          SMap.add claimed tgt src;
          SMap.add !renames src tgt
        end
      | _ -> ());
    (* A module named but contributing nothing is almost always a typo or a
       forgotten --custard_entry_module, and silence there costs a round. *)
    mods |> List.iter (fun m ->
      if None? (SMap.try_find used_mod m) then
        E.log_issue0 E.Warning_CustardNoPublicDefinitions [
          text ("Custard: --custard_c_no_prefix " ^ m ^ " renamed nothing.");
          text "The option applies to definitions with external linkage. \
Name the module with --custard_entry_module, or its definitions with \
--custard_entry, so that they are part of this unit's interface."; ])
  end

(* Section 35.1.  A public definition whose signature mentions a
   specialization.

   Round 40's reporter drove the real CBOR API off the generated header from
   C++ with no help but three typedefs, and two of the three name types that
   {!build_renames} renamed for them.  The third could not be written that
   way:

     typedef CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__cbor_raw
             cbor_det_array_iterator_t;

   [--custard_c_no_prefix CBOR.Pulse.Raw.Iterator] does not help, and
   correctly says so with warning 375 -- the type on the interface is not
   that module's declaration but a monomorphized instance of it, and
   {!build_renames} excludes specializations deliberately.  The exclusion is
   right: section 30.15's hints are depth-bounded, clipped to 48 characters
   and collision-suffixed, so they are exactly the names that may change when
   the monomorphizer's input does.

   What was wrong is that nothing said so.  A consumer reads the header, sees
   a name, writes it down, and finds out later.  The condition is decidable
   here -- a public prototype is in the header, and a [TApp] in it whose name
   has a [spec] is a generated name the consumer has to spell -- so it is a
   diagnostic rather than a rename.  Renaming was considered and declined on
   the same report's advice: the name a consumer wants is an abbreviation
   *they* chose, and Custard cannot know it.

   Reported once per type rather than once per definition that exposes it,
   naming one such definition, because the consumer's problem is the type.
   Only types the unit actually declares are reported: an abbreviation that
   was unfolded leaves no name in the header to depend on. *)
let check_interface_names (p:program) : ML unit =
  let rec spec_names (c:cty) : ML (list name) =
    match c with
    | TArrow (a, _, b) -> spec_names a @ spec_names b
    | TTuple cs -> cs |> List.collect spec_names
    | TBuf c | TRef c | TInline c -> spec_names c
    | TApp (n, args) ->
      (if Some? n.spec then [n] else []) @ (args |> List.collect spec_names)
    | _ -> [] in
  let declared : SMap.t bool = SMap.create 50 in
  p |> List.iter (function
    | DType t -> SMap.add declared (string_of_name t.dt_name) true
    | _ -> ());
  let seen : SMap.t bool = SMap.create 10 in
  p |> List.iter (function
    | DLet l when is_public l ->
      let sig_ctys = (l.dl_binders |> List.map (fun b -> b.b_ty)) @ [l.dl_ret] in
      sig_ctys |> List.collect spec_names |> List.iter (fun n ->
        let s = string_of_name n in
        if Some? (SMap.try_find declared s) && None? (SMap.try_find seen s)
        then begin
          SMap.add seen s true;
          E.log_issue0 E.Warning_CustardGeneratedNameInInterface [
            text ("Custard: the type `" ^ c_name n ^
                  "' is part of this unit's interface -- " ^
                  string_of_name l.dl_name ^
                  " has it in its signature -- but its name is generated.");
            text "It is a specialization, so the name carries a hint built from the monomorphizer's input and may change when that input does. --custard_c_no_prefix does not rename specializations.";
            text "A consumer that must spell it should typedef it once, in its own header, rather than depend on this name throughout."; ]
        end)
    | _ -> ())

(* [base] is the stem of the output file: the source includes [base.h], and
   the include guard is derived from it.  Returns the header and the source,
   in that order. *)
(* Section 31.2.  Breadth-first from the roots, recording who first reached
   each declaration, so that walking back up gives a shortest chain.  A
   constructor is reached as its own type, which is how {!Simplify.dce}
   resolves it too. *)
let record_parents (p:program) : ML unit =
  let defs : SMap.t decl = SMap.create 50 in
  let own : SMap.t string = SMap.create 50 in
  let _ = p |> List.iter (fun d ->
    SMap.add defs (string_of_name (name_of_decl d)) d;
    match d with
    | DType t ->
      (match t.dt_body with
       | TVariant cs ->
         cs |> List.iter (fun (cn, _) ->
                 SMap.add own (string_of_name cn) (string_of_name t.dt_name))
       | _ -> ())
    | _ -> ()) in
  let resolve (n:string) : ML string =
    match SMap.try_find own n with Some o -> o | None -> n in
  let seen : SMap.t bool = SMap.create 50 in
  let rec bfs (front:list string) : ML unit =
    match front with
    | [] -> ()
    | _ ->
      let next = front |> List.collect (fun n ->
        match SMap.try_find defs n with
        | None -> []
        | Some d ->
          Simplify.decl_deps d |> List.collect (fun c ->
            let c = resolve c in
            if c = n || Some? (SMap.try_find seen c) then []
            else (SMap.add seen c true; SMap.add parents c n; [c]))) in
      bfs next in
  let rec ty_names (t:cty) (acc:list string) : ML (list string) =
    match t with
    | TApp (n, args) ->
      List.fold_right ty_names args (string_of_name n :: acc)
    | TArrow (a, _, b) -> ty_names a (ty_names b acc)
    | TBuf e | TRef e | TInline e -> ty_names e acc
    | TTuple ts -> List.fold_right ty_names ts acc
    | _ -> acc in
  let _ = p |> List.iter (fun d ->
    match d with
    | DExternal x ->
      ty_names x.dx_ty [] |> List.iter (fun tn ->
        if None? (SMap.try_find frozen_by tn)
        then (SMap.add frozen_by tn (string_of_name x.dx_name);
              match x.dx_target with
              | Some t -> SMap.add frozen_by_target tn t
              | None -> ()))
    | _ -> ()) in
  let roots = p |> List.collect (fun d ->
    if decl_flags d |> List.existsb (fun f -> Root? f || Entrypoint? f)
    then (let n = string_of_name (name_of_decl d) in SMap.add seen n true; [n])
    else []) in
  bfs roots

let print_program (base:string) (cu:unit_info) (p:program) : ML (string & string) =
  (* Section 42.2.  An imported declaration is in [p] so that the tables below
     see its shape, and out of every list that is emitted: the unit that
     compiled it has a header, and that header is included instead.  Writing a
     declaration of our own for it is what section 14.10 is the record of. *)
  let init_name = init_name cu in
  record_parents p;
  let tt = SMap.create 50 in
  let ct = SMap.create 50 in
  let xt = SMap.create 20 in
  let kt = SMap.create 50 in
  let vt = SMap.create 50 in
  let at = SMap.create 50 in
  p |> List.iter (fun d ->
    match d with
    | DType t ->
      SMap.add tt (string_of_name t.dt_name) t;
      (* Section 33.4. *)
      t.dt_flags |> List.iter (fun f ->
        match f with
        | Existential (c, fld) ->
          SMap.add existentials (string_of_name t.dt_name) (c, fld)
        | _ -> ());
      (match t.dt_body with
       | TVariant cs ->
         cs |> List.iter (fun (c, fs) -> SMap.add ct (string_of_name c) (t, fs))
       | _ -> ())
    | DExternal x ->
      SMap.add xt (string_of_name x.dx_name)
        (match x.dx_target with
         | Some "" | None -> c_name x.dx_name
         | Some t -> escape_kw (sanitize t));
      (* A unit parameter of an *external* goes too, and unconditionally: the
         function on the other side is C, C has no unit value, and whatever it
         was declared as it was not declared to take one.  There is no body to
         consult, but there is nothing to consult it about -- a unit argument
         carries no information.  karamel does the same, which is why
         [EverCrypt_AutoConfig2_init()] is what both C paths must emit. *)
      let flags = arg_ctys x.dx_ty |> List.map (fun a -> not (TUnit? a)) in
      if List.existsb (fun b -> not b) flags then
        SMap.add kt (string_of_name x.dx_name) flags;
      (* Same for a unit *result*: the target function returns [void], and a
         prototype saying otherwise is a declaration that does not match the
         definition it will be linked against. *)
      if Cons? flags && TUnit? (ret_cty x.dx_ty) then
        SMap.add vt (string_of_name x.dx_name) true
      ;
      (* An external's arity is the one its declared type states; a
         parameterless one is a variable and is not called at all. *)
      let n = List.length (List.filter (fun b -> b) flags) in
      if n > 0 then SMap.add at (string_of_name x.dx_name) n
    | DLet l ->
      let used = vars_of l.dl_body in
      let flags = l.dl_binders |> List.map (fun b ->
        not (TUnit? b.b_ty) || List.existsb (fun y -> y = b.b_name) used) in
      (* Only worth recording when it changes something, and never for a
         definition whose every parameter would go: [f()] is fine, but the
         rejection of a parameterless definition below is about the IR, so the
         two must not be confused. *)
      if List.existsb (fun b -> not b) flags then SMap.add kt (string_of_name l.dl_name) flags;
      if TUnit? l.dl_ret && Cons? l.dl_binders then SMap.add vt (string_of_name l.dl_name) true
      ;
      (* A parameterless definition of arrow type is lowered to a *variable*
         of function-pointer type (section 25.3), and a call through it
         supplies every argument at once -- so its arity is the arity of its
         type, not zero.  Leaving it out of the table is what let section 26's
         [call_e] reach a C compiler: both the expansion and this check record
         definitions, and a variable of arrow type was neither. *)
      let n = List.length (List.filter (fun b -> b) flags) in
      SMap.add at (string_of_name l.dl_name)
        (if Cons? l.dl_binders then n else List.length (arg_ctys l.dl_ret))
    | _ -> ());
  types := tt; ctors := ct; externs := xt; keeps := kt; void_fns := vt;
  build_renames p;
  check_interface_names p;
  arities := at;

  (* Only the standard library, and only the parts that are used unavoidably:
     fixed-width integers, malloc/free/abort, memmove, and bool. *)
  let banner = "/* Generated by F* Custard extraction. Do not edit. */\n" in
  let guard = "__" ^ String.uppercase (sanitize base) ^ "_H" in
  let header =
    banner ^
    "#ifndef " ^ guard ^ "\n\
     #define " ^ guard ^ "\n\
     \n\
     #include <stdint.h>\n\
     #include <stdlib.h>\n\
     #include <stdbool.h>\n\
     #include <string.h>\n\
     \n\
     /* The sole inhabited erased value (section 5.1).  A distinct typedef \
     rather\n\
        than void, so that it can be stored in a variable and returned like \
     any\n\
        other value.  Guarded because two generated headers may meet in one\n\
        translation unit (section 42.2): this is a fixed name for a fixed \
     type,\n\
        so two spellings of it are the same spelling. */\n\
     #ifndef CUSTARD_UNIT_DEFINED\n\
     #define CUSTARD_UNIT_DEFINED\n\
     typedef uint8_t custard_unit;\n\
     #endif\n" in

  let includes =
    (* Section 42.2: the linked units' headers, first, since this unit's
       declarations may mention their types. *)
    (cu.cu_headers |> List.map (fun h -> "#include \"" ^ h ^ "\"")) @
    (p |> List.collect (fun d ->
      match d with
      | DExternal ({ dx_header = Some h }) -> ["#include \"" ^ h ^ "\""]
      | DType ty ->
        ty.dt_flags |> List.collect (fun f ->
          match f with
          | Extern (_, Some h) -> ["#include \"" ^ h ^ "\""]
          | _ -> [])
      | _ -> []) ) in
  let includes = dedup includes in

  let exts = p |> List.collect (fun d ->
    if not (local d) then [] else
    match d with
    | DExternal x -> (match extern_decl x with Some s -> [s] | None -> [])
    | DExn _ ->
      current := "an exception declaration";
      reject "an exception declaration" ["C has no exceptions."]
    | _ -> []) in

  (* Every struct's name exists before any type is defined, so that a type
     that reaches itself, or another one later in the file, through a pointer
     needs no analysis here.  A field held *by value* does need one, and
     [sort_types] is it: the SCC pass's order is over all dependencies, so a
     group made cyclic by pointers is one SCC and the order inside it is
     arbitrary. *)
  let fwds = p |> List.collect (fun d ->
    if not (local d) then [] else
    match d with
    | DType t ->
      current := string_of_name t.dt_name;
      (match type_fwd t with Some s -> [s] | None -> [])
    | _ -> []) in

  let tys = sort_types (p |> List.collect (fun d ->
                          match d with
                          | DType t when local d -> [t] | _ -> []))
            |> List.collect (fun t ->
    current := string_of_name t.dt_name;
    (match type_decl t with Some s -> [s] | None -> [])) in

  (* Every function is declared before any is defined, so that a recursive
     group needs no analysis: the SCC pass has already grouped them, but C
     wants a prototype, not a group. *)
  let proto_of (l:dlet) : ML string =
    current := string_of_name l.dl_name;
    reset_scope ();
    kept_binders l |> List.iter (fun b -> let _ = bind_var b.b_name in ());
    signature l ^ ";\n" in

  (* A parameterless definition is a C variable.  Its *definition* stays in
     the source either way; the header declares it [extern], which is the one
     spelling that does not also define it in every unit that includes it. *)
  let protos = p |> List.collect (fun d ->
    if not (local d) then [] else
    match d with
    | DLet l when Nil? l.dl_binders -> [storage l ^ global_decl l]
    | DLet l when Cons? l.dl_binders ->
      if is_public l then []
      else [prologue_of l ^ storage l ^ inline_of l ^ proto_of l]
    | _ -> []) in

  let pub_decls = p |> List.collect (fun d ->
    if not (local d) then [] else
    match d with
    | DLet l when is_public l && Nil? l.dl_binders ->
      current := string_of_name l.dl_name;
      ["extern " ^ decl_of l.dl_ret (c_name l.dl_name) ^ ";\n"]
    | DLet l when is_public l -> [prologue_of l ^ inline_of l ^ proto_of l]
    | _ -> []) in

  let defs = p |> List.collect (fun d ->
    if not (local d) then [] else
    match d with
    | DLet l when Nil? l.dl_binders -> []
    | DLet l -> [comment_of l ^ prologue_of l ^ storage l ^ inline_of l ^
                 let_decl l ^ epilogue_of l]
    | _ -> []) in

  (* In declaration order, which the SCC pass has already made a topological
     one: a global whose initializer reads another global sees it set. *)
  let inits = global_inits_of p |> List.map global_init in
  (* A program with no globals has nothing to initialize, and an empty
     function that [main] calls anyway is two lines of noise plus a block
     that says nothing.  It is also part of this file's interface, so it is
     emitted whenever there is anything to do and omitted otherwise -- a
     caller that has to know which is a caller that can read the header. *)
  (* The re-entry guard is emitted only under [--custard_unit].  There it is
     load-bearing: [--custard_link] order is the user's and need not be a
     topological one, so an initializer may be reached twice.  In whole-program
     mode there is exactly one caller and the branch would be noise in output
     meant to be read. *)
  let init_guard =
    match cu.cu_name with
    | None   -> ""
    | Some _ -> "  static bool custard_initialized = false;\n" ^
                "  if (custard_initialized) return;\n" ^
                "  custard_initialized = true;\n" in
  let init_fn = match inits with
                | [] -> ""
                | _ -> "void " ^ init_name ^ "(void) {\n" ^ init_guard ^
                       String.concat "" inits ^ "}\n" in
  let init_proto = match inits with
                   | [] -> ""
                   | _ -> "void " ^ init_name ^ "(void);\n" in

  (* Custard compiles standalone programs (section 4.4).  An entry point
     returning a machine integer is the process exit status, which is what a C
     [main] returns; anything else is run for its effect. *)
  let mains = p |> List.collect (fun d ->
    if not (local d) then [] else
    match d with
    | DLet l when l.dl_flags |> List.existsb Entrypoint? ->
      current := string_of_name l.dl_name;
      let args = String.concat ", "
                   (kept_binders l |> List.map (fun _ -> unit_value)) in
      let call = c_name l.dl_name ^ "(" ^ args ^ ")" in
      (* Section 42.3.  Every linked unit's globals are set up before this
         one's, in [--custard_link] order; their prototypes come from the
         headers included above. *)
      let calls = (cu.cu_inits |> List.map (fun i -> "  " ^ i ^ "();\n")) @
                  (match inits with [] -> [] | _ -> ["  " ^ init_name ^ "();\n"]) in
      let pre = "int main(void) {\n" ^ String.concat "" calls in
      (match l.dl_ret with
       | TInt _ -> [pre ^ "  return (int)" ^ call ^ ";\n}\n"]
       | TUnit -> [pre ^ "  " ^ call ^ ";\n  return 0;\n}\n"]
       | _ -> [pre ^ "  (void)" ^ call ^ ";\n  return 0;\n}\n"])
    | _ -> []) in

  (* The header carries the unit's whole type language rather than only the
     types a public signature mentions.  A [struct] or a [typedef] has no
     linkage, so there is nothing to collide and nothing to hide from the
     linker, and the reachability analysis that would trim it buys an
     incomplete header and a class of "field has incomplete type" errors --
     a bad trade for a file whose entire purpose is to be usable. *)
  (* Section 32.4.  After the includes, never around them: a system or an
     external header brings its own linkage decisions, and wrapping one is how
     a C++ consumer gets an unresolvable [std::] symbol.  Unconditional, since
     the guard is a no-op for the C compiler that reads the same file. *)
  let cpp_open =
    "#ifdef __cplusplus\nextern \"C\" {\n#endif\n\n" in
  let cpp_close =
    "\n#ifdef __cplusplus\n}\n#endif\n" in

  let hdr =
    header ^ "\n" ^
  (match includes with [] -> "" | _ -> String.concat "\n" includes ^ "\n\n") ^
  cpp_open ^
  String.concat "" fwds ^ (match fwds with [] -> "" | _ -> "\n") ^
  String.concat "" tys ^ (match tys with [] -> "" | _ -> "\n") ^
  String.concat "" pub_decls ^ (match pub_decls with [] -> "" | _ -> "\n") ^
  init_proto ^ (match inits with [] -> "" | _ -> "\n") ^
  cpp_close ^
  "#endif\n" in

  (* The source includes its own header, so the header is *checked* against
     the definitions rather than merely shipped alongside them. *)
  let body =
    banner ^
    "#include \"" ^ base ^ ".h\"\n\n" ^
  String.concat "" exts ^ (match exts with [] -> "" | _ -> "\n") ^
  String.concat "" protos ^ (match protos with [] -> "" | _ -> "\n") ^
  String.concat "\n" defs ^ "\n" ^ (match inits with [] -> "" | _ -> init_fn) ^
    (match mains with [] -> "" | _ -> "\n" ^ String.concat "\n" mains) in
  hdr, body
