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
module HashTable = FStarC.HashTable
module SI = FStarC.SmallInt
module E      = FStarC.Errors
module String = FStarC.String
module Options = FStarC.Options
module Cherry = FStarC.Custard.Cherry
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
let parents : HashTable.t string string = HashTable.create 50

(* Section 31.3.  An external whose signature mentions this type.  On the
   OCaml path that is *why* the type was left polymorphic, by §5.0.1 rule 4,
   and naming it is the difference between "the pass did not reach this,
   please report a bug" and "this declaration is realized outside the program,
   so the pass was not allowed to clone it".

   Section 100: on a C backend rule 4 no longer fires, so the table no longer
   explains a *freeze* there -- but it still names the declaration that put an
   unrepresentable type in front of the backend, which is the thing a reader
   has to go and change.  The name is kept because the OCaml path still uses
   it in the original sense. *)
let frozen_by : HashTable.t string string = HashTable.create 20
(* Section 32.5.  Whether the external that froze a type is a [custard_extern]
   -- a C symbol the program named -- or a hand-written OCaml realization.
   The advice differs, and asserting the wrong one sends a reader to look for
   an .ml file that does not exist. *)
let frozen_by_target : HashTable.t string string = HashTable.create 20

(* Section 33.4.  Type name -> the constructor and [Type0] field that make it
   an existential, from the {!Existential} flag the extractor sets.  Kept as
   its own table rather than read off {!types} for the ordinary reason: a
   rejection has to be able to explain itself before the printer's tables
   exist, and this one is filled from the program at the same time they are. *)
let existentials : HashTable.t string (string & string) = HashTable.create 20

(* Section 72.1.  The declarations that were rooted, so that a rejection can
   tell "nothing reached this" from "nothing reached this *yet*".  An empty
   {!reached_through} says only that the BFS never assigned a parent, which is
   also true of a declaration the walk did not visit; being a root is the fact
   that actually changes the advice, and it is not derivable from [parents]. *)
let root_decls : HashTable.t string bool = HashTable.create 50

let reached_through (n:string) : ML (list string) =
  let rec up (n:string) (fuel:int) (acc:list string) : ML (list string) =
    if fuel <= 0 then List.rev acc
    else match HashTable.try_find parents n with
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
      (match HashTable.try_find existentials n with
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
(* An integer literal: one token, so no operator can bind into it and no
   position that calls {!group} needs it parenthesized.  Section 59.4 --
   once a literal stops carrying a cast, the pair {!group} would add around
   it is the only punctuation left, and [(1) * sizeof(T)] is not what the
   cast removal was for.

   Section 61.2: a *number*, and not an identifier, which is what this said
   at first.  A name is one **preprocessing** token, which is not the same
   as one token: it is one token only until it is expanded, and the names
   this backend does not write are exactly the extern ones.  With
   [#define EXT_FLAG 0 || 1] in a header Custard never sees, [!EXT_FLAG] is
   [!0 || 1], which is silently true.  Section 59.5 already makes this
   exception for the sibling question -- an extern keeps its casts because
   it may be a macro -- and the parenthesis is the same question, which did
   not get the same answer.  Nothing here can tell an extern's name from
   one of Custard's own, and a pair of parens around a name costs nothing.

   Still deliberately syntactic: a suffixed hex literal is one token, while
   [-1], [a.b] and [a + b] are not and keep their pair. *)
let is_atom (s:string) : ML bool =
  s <> "" &&
  BU.is_digit (String.get s 0) &&
  List.for_all (fun c -> BU.is_letter_or_digit c || c = '_')
               (String.list_of_string s)

let group (s:string) : ML string =
  if is_group s || is_atom s then s else "(" ^ s ^ ")"

(* [!e] binds tighter than any operator, so the operand has to be a group;
   one that already is keeps its own parens rather than gaining a second. *)
let negate (s:string) : ML string =
  "!" ^ group s

(* Section 116.  The same escape the OCaml printer makes injective in section
   115, and for the same reason: appending an underscore is an escape only if
   it lands where nothing else does, and a record with fields [switch] and
   [switch_] declared two members called [switch_].  The trailing underscores
   are stripped before the keyword test, which shifts the whole family by one
   and keeps it distinct; a name that is not a keyword with underscores after
   it is untouched, which is very nearly all of them.

   Every C name in this backend goes through here -- {!c_name} for a
   definition, {!c_var} for a field, a local and a union member -- so the
   declaration and the use agree by construction. *)
let escape_kw (s:string) : ML string =
  let rec strip (t:string) : ML string =
    let n = String.length t in
    if n > 0 && String.substring t (n - 1) 1 = "_"
    then strip (String.substring t 0 (n - 1))
    else t in
  if List.existsb (fun k -> k = strip s) c_keywords then s ^ "_" else s

(* Section 32.4.  [--custard_c_no_prefix] renames a public definition to its
   unqualified identifier.  The map is keyed by {!string_of_name} and is
   consulted by every printer, because a rename has to reach the definition,
   the prototype and every call site in the file alike: this is one C name
   for one IR name, not a second name for the same thing. *)
let renames : ref (HashTable.t string string) = mk_ref (HashTable.create 0)

(* Section 68.  The declarations marked [@@ CMacro ], mapped to the spelling
   the preprocessor sees.  Consulted by {!c_name}, so that every reference to
   one is the macro's name without any call site having to know: a [#define]
   has no linkage and no separate declaration, so the name at the use is the
   only name there is.  Built after {!build_renames}, since the macro name is
   the uppercase of whatever the rename settled on. *)
let macros : ref (HashTable.t string string) = mk_ref (HashTable.create 0)

let c_name (n:name) : ML string =
  match HashTable.try_find !macros (string_of_name n) with
  | Some s -> s
  | None ->
  match HashTable.try_find !renames (string_of_name n) with
  | Some s -> s
  | None -> escape_kw (sanitize (mangled_name n))
let c_var (x:string) : ML string = escape_kw (sanitize x)

(* Section 117.2.  The one declaration whose emitted C symbol is not spelled
   from its F* name.  An [@@custard_extern "..."] target is taken verbatim
   (section 45.1), so a table built by walking the program and spelling each
   declaration with [c_name] records, for an external, a name the generated
   file does not contain -- and leaves the name it *does* contain free for
   whatever allocates into that table next. *)
let extern_target (d:decl) : ML (option string) =
  match d with
  | DExternal x -> (match x.dx_target with
                    | Some "" | None -> None
                    | Some t -> Some t)
  | _ -> None

(* Section 121.3.  How a declaration is spelled in the generated C, as one
   total function.

   Three defects in a row -- sections 117.2 and 117.3 -- were the same shape:
   a name allocated against a set that did not contain everything the file
   would really contain.  Each fix added another case to a seeding loop that
   derived the spelling independently of the code that prints it, which is
   correct only for as long as someone remembers to add the next one.  So the
   seeding, the collision check and the external's own prototype all read this
   function instead, and a new kind of spelling has one place to change.

   [build_renames] first installs explicit names, then consults [c_name]
   while applying prefix removal.  The one name this cannot answer for is
   the generated initializer, which is minted from the unit and
   not from any declaration; [init_name] is its single source in the same
   sense, and both seeding sites pass it explicitly. *)
let emitted_name (d:decl) : ML string =
  match extern_target d with
  | Some t -> t
  | None -> c_name (name_of_decl d)

(* Section 114.  The member of a tagged union, and the path through it.

   A member was named after the fully qualified constructor, which after
   monomorphization carries the specialization suffix: a consumer reading an
   [either] out of a parser wrote

     m._x0.val.FStar_Pervasives_Inl__slice_tuple2_evercddl_uint_evercddl_ui.v

   and warning 377 tells that same consumer the suffix may change when the
   monomorphizer's input does.  The advice the warning gives -- name it once
   in a [typedef] -- works for a type and not for a *member*, which no C
   construct can abstract over.  So the name had to be one a consumer can
   depend on, or the surface was unusable by the warning's own standard.

   It can be the bare constructor name, because the member is already scoped
   by the union: the only names in scope are the arms of this one variant,
   whose constructors are distinct by construction.  The suffix was
   disambiguating against a namespace the member is not in.  Nothing is lost,
   since the member cannot be referenced except through a value whose *type*
   name still carries the full specialization.

   Section 113.  A constructor carrying exactly one field is the member
   itself, with no anonymous struct around it.  The wrapper never
   disambiguated anything either -- inside the union the arm is already
   unique -- and it cost a level on the single most common shape in generated
   parser output, [option], of which one public EverParse header has 53 in
   74.  A constructor with two or more fields keeps the struct, which is what
   a struct is for.

   Together these turn [o.val.FStar_Pervasives_Native_Some__evercddl_uint.v]
   into [o.val.Some]. *)
let arm_name (cn:name) : ML string = c_var cn.id

let arm_flat (fs : list (string & cty)) : bool =
  match fs with
  | [_] -> true
  | _ -> false

(* The selector reaching field [f] of constructor [cn], whose fields are [fs],
   from a value of the variant. *)
let arm_sel (cn:name) (fs : list (string & cty)) (f:string) : ML string =
  ".val." ^ arm_name cn ^ (if arm_flat fs then "" else "." ^ c_var f)

(* An enum tag.  Uppercased so that it cannot collide with a value or a type
   name derived from the same lid. *)
(* Through {!renames}, so that a constructor of a --custard_c_no_prefix module
   gets the unqualified tag its type and its functions got.  Uppercasing is
   what keeps it from colliding with a value or type name of the same lid, and
   {!build_renames} checks the un-uppercased form, so a rename that is legal
   there is legal here. *)
let c_tag (n:name) : ML string =
  String.uppercase (match HashTable.try_find !renames (string_of_name n) with
                    | Some s -> s
                    | None -> sanitize (mangled_name n))

(* -------------------------------------------------------------------- *)
(* The declaration tables                                               *)
(* -------------------------------------------------------------------- *)

(* Printing a pattern or a constructor application needs the layout of the
   type involved, which is not on the node.  Both tables are constant for a
   whole program, so they are globals rather than a threaded environment. *)
let types : ref (HashTable.t string dtype) = mk_ref (HashTable.create 0)
(* constructor name -> (its type, its field list) *)
let ctors : ref (HashTable.t string (dtype & list (string & cty))) = mk_ref (HashTable.create 0)
(* external name -> the symbol to call it by *)
let externs : ref (HashTable.t string string) = mk_ref (HashTable.create 0)
(* Section 51.6.  [@@custard_c_ifdef] external -> its preprocessor condition *)
let ifdefs : ref (HashTable.t string string) = mk_ref (HashTable.create 0)

let ifdef_of_flags (fs:list flag) : ML (option string) =
  match List.tryFind IfDef? fs with
  | Some (IfDef c) -> Some c
  | _ -> None

(* Which parameters of a definition survive into C.  A [unit] parameter the
   body never mentions carries no information -- it is F*'s way of writing a
   thunk, and C has no laziness to preserve -- so it is dropped from the
   signature and from every call site.  The flags are computed once, in
   [print_program], because the call site has to make the same decision as the
   definition. *)
let keeps : ref (HashTable.t string (list bool)) = mk_ref (HashTable.create 0)

(* Which definitions return [unit], and are therefore emitted as C [void].
   Consulted at the call site, where a [void] call is a statement and cannot be
   an operand. *)
let void_fns : ref (HashTable.t string bool) = mk_ref (HashTable.create 0)

(* How many arguments each named definition takes, after the dropped
   parameters of [keeps] are removed.  Only used to refuse a call that does
   not match: C has neither partial application nor a way to apply a call's
   result without saying so, and both come out as a plain call with the wrong
   number of operands -- valid IR, and C that does not compile (section 25). *)
let arities : ref (HashTable.t string int) = mk_ref (HashTable.create 0)

(* Whether the definition currently being printed returns [void]. *)
let void_ret : ref bool = mk_ref false

(* Cherry: tail calls that become a jump, as OCaml's would, since ML code
   loops by recursion and C does not promise to eliminate the call
   (cherry.md, "Tail calls").  Each entry is a definition the C function
   being printed can jump to -- itself, and the other members of its tail
   group ({!tail_groups}) -- with the label to jump to and the C variables
   its kept parameters live in.  [tail_used] lists the labels jumped to. *)
let tail_targets : ref (list (string & string & list (binder & string))) = mk_ref []
(* Cherry: whether the other tail calls of the definition being printed may
   be marked [CHERRY_MUSTTAIL] -- not when it allocates on the stack, since an
   argument could point into the frame the call discards. *)
let musttail_ok : ref bool = mk_ref false
let tail_used : ref (list string) = mk_ref []

(* Cherry: a set of definitions that call each other in tail position, and
   are printed as one C function so that those calls are jumps
   (cherry.md, "Tail calls").  [tg_fn] is that function, taking the index of
   the member to start in; each member stays a C function of its own, which
   stores its arguments in [tg_args] and calls [tg_fn]. *)
type tail_group = {
  tg_fn: string;
  tg_args: string;
  tg_members: list dlet;
}
(* Each member's name, to its index in its group and the group. *)
let tail_groups : ref (HashTable.t string (int & tail_group)) = mk_ref (HashTable.create 0)
(* The parameters some self tail call passes unchanged.  Such a call writes
   nothing to them, so a parameter whose only use is that one is unused as far
   as C can tell, and gets voided like one the body never mentions. *)
let tail_kept : ref (list string) = mk_ref []

let rec filter_by (#a:Type) (flags:list bool) (xs:list a) : list a =
  match flags, xs with
  | b :: flags, x :: xs -> (if b then [x] else []) @ filter_by flags xs
  | _ -> xs

let find_type (n:name) : ML (option dtype) = HashTable.try_find !types (string_of_name n)

(* Section 69.  The template pieces of an external type's target, if it has a
   target and that target mentions any argument.  Read off the declaration
   rather than kept in a table: it is the same string [Extract] parsed, and a
   second copy of it is a second thing to keep in step. *)
let extern_template_of (n:name) : ML (option (list tmpl_piece)) =
  match find_type n with
  | Some { dt_body = TAbstract; dt_flags = fs } -> extern_template_of_flags fs
  | _ -> None
(* Section 70.2.  A binding at this type aliases rather than copies, because
   its values are handles ([@@custard_c_reference]).  Read off the declaration
   for the same reason as {!extern_template_of}. *)
let binds_by_ref (t:cty) : ML bool =
  match t with
  | TApp (n, _) ->
    (match find_type n with
     | Some { dt_flags = fs } -> fs |> List.existsb CReference?
     | _ -> false)
  | _ -> false

let find_ctor (n:name) : ML (option (dtype & list (string & cty))) =
  HashTable.try_find !ctors (string_of_name n)

(* Cherry's exceptions (cherry.md, "Exceptions"): each is a cell with the
   runtime's header, whose fields are [f0], [f1], ... *)
let exn_ctors : ref (HashTable.t string (list (string & cty))) = mk_ref (HashTable.create 0)
let find_exn (n:name) : ML (option (list (string & cty))) =
  HashTable.try_find !exn_ctors (string_of_name n)
let exn_struct (n:name) : ML string = "struct " ^ c_name n ^ "_exn_s"
let exn_info (n:name) : ML string = c_name n ^ "_exn_info"
let exn_new (n:name) : ML string = "cherry_exn_new_" ^ c_name n
let exn_field (v:string) (n:name) (f:string) : ML string =
  "((" ^ exn_struct n ^ " *)" ^ v ^ ")->" ^ f

(* The result type of the definition being printed, which leaving it with an
   exception pending returns a dummy of; [None] in a global's initializer. *)
let cur_ret : ref (option cty) = mk_ref None

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
(* Cherry (cherry.md)                                                   *)
(* -------------------------------------------------------------------- *)

(* Under [--codegen Cherry] a *boxed* type -- one that contains
   itself by value -- is a pointer to a reference-counted cell, and a
   *non-plain* type is one whose values own references.  Both sets come from
   {!FStarC.Custard.Cherry} and are empty for every other backend. *)
let boxed_tbl : ref (HashTable.t string bool) = mk_ref (HashTable.create 0)
let nonplain_tbl : ref (HashTable.t string bool) = mk_ref (HashTable.create 0)

let is_boxed_name (n:name) : ML bool = HashTable.mem !boxed_tbl (string_of_name n)
let is_boxed (d:dtype) : ML bool = is_boxed_name d.dt_name
let is_boxed_ty (t:cty) : ML bool =
  match t with TApp (n, _) -> is_boxed_name n | _ -> false
let is_nonplain_ty (t:cty) : ML bool =
  match t with
  | TApp (n, _) -> HashTable.mem !nonplain_tbl (string_of_name n)
  (* The key {!Cherry.nonplain_types} files every function type under. *)
  | TArrow _ -> HashTable.mem !nonplain_tbl "->"
  | TExn -> HashTable.mem !nonplain_tbl "Prims.exn"
  | TRef (RGc, _) -> HashTable.mem !nonplain_tbl Cherry.ref_key
  | TAny -> HashTable.mem !nonplain_tbl Cherry.any_key
  | _ -> false

(* The cell of constructor [cn] of the boxed type [d], and field [f] of it
   read off the pointer [v]. *)
let cell_struct (d:dtype) (cn:name) : ML string =
  "struct " ^ c_name d.dt_name ^ "_" ^ arm_name cn ^ "_s"
let cell_field (v:string) (d:dtype) (cn:name) (f:string) : ML string =
  "((" ^ cell_struct d cn ^ " *)" ^ v ^ ")->" ^ c_var f
let cell_new (d:dtype) (cn:name) : ML string =
  "cherry_new_" ^ c_name d.dt_name ^ "_" ^ arm_name cn
let cell_unshare (d:dtype) (cn:name) : ML string =
  "cherry_unshare_" ^ c_name d.dt_name ^ "_" ^ arm_name cn

(* The generated function performing [op] -- [inc], [dec] or [mark] -- on a
   value of the non-plain type [t].  Taking a reference to a cell is the same
   at every type, so that one is the runtime's. *)
let is_runtime_name (n:name) : ML bool =
  List.mem (string_of_name n) Cherry.runtime_types

(* ML references (cherry.h): the value types whose cell and operations the
   unit needs, numbered; [cherry_ref_helpers] generates them. *)
let ref_tys : ref (list cty) = mk_ref []
let ref_prefix (t:cty) : ML string =
  let rec find (i:int) (l:list cty) : ML (option int) =
    match l with
    | [] -> None
    | u :: rest -> if u = t then Some i else find (i + 1) rest in
  let i = match find 0 !ref_tys with
          | Some i -> i
          | None -> ref_tys := !ref_tys @ [t]; List.length !ref_tys - 1 in
  "cherry_ref" ^ string_of_int i

(* Pulse references and arrays of counted values (cherry.h), the same way:
   the element types, numbered; [cherry_pbuf_helpers] generates them. *)
let pbuf_tys : ref (list cty) = mk_ref []
let pbuf_prefix (t:cty) : ML string =
  let rec find (i:int) (l:list cty) : ML (option int) =
    match l with
    | [] -> None
    | u :: rest -> if u = t then Some i else find (i + 1) rest in
  let i = match find 0 !pbuf_tys with
          | Some i -> i
          | None -> pbuf_tys := !pbuf_tys @ [t]; List.length !pbuf_tys - 1 in
  "cherry_pbuf" ^ string_of_int i

(* Immutable arrays (cherry.h), the same way: the element types, numbered,
   and for each the list type its [of_list] and [to_list] convert from and
   to, once one is used; [cherry_iarr_helpers] generates them. *)
let iarr_tys : ref (list cty) = mk_ref []
let iarr_lists : ref (list (int & cty)) = mk_ref []
let iarr_index (t:cty) : ML int =
  let rec find (i:int) (l:list cty) : ML (option int) =
    match l with
    | [] -> None
    | u :: rest -> if u = t then Some i else find (i + 1) rest in
  match find 0 !iarr_tys with
  | Some i -> i
  | None -> iarr_tys := !iarr_tys @ [t]; List.length !iarr_tys - 1
let iarr_prefix (t:cty) : ML string = "cherry_iarr" ^ string_of_int (iarr_index t)
let iarr_list (t:cty) (l:cty) : ML unit =
  let i = iarr_index t in
  if not (List.existsb (fun (j, _) -> j = i) !iarr_lists) then
    iarr_lists := !iarr_lists @ [(i, l)]

(* The any type (cherry.h), the same way: the value types made into one. *)
let any_tys : ref (list cty) = mk_ref []
let any_prefix (t:cty) : ML string =
  let rec find (i:int) (l:list cty) : ML (option int) =
    match l with
    | [] -> None
    | u :: rest -> if u = t then Some i else find (i + 1) rest in
  let i = match find 0 !any_tys with
          | Some i -> i
          | None -> any_tys := !any_tys @ [t]; List.length !any_tys - 1 in
  "cherry_any" ^ string_of_int i

let rc_fn (op:string) (t:cty) : ML string =
  match t with
  | TAny -> "cherry_any_" ^ op
  | TRef (RGc, v) ->
    if op = "inc" then "cherry_inc" else ref_prefix v ^ "_" ^ op
  | TApp ({ ns = ["FStar"; "ImmutableArray"; "Base"]; id = "t"; spec = None }, [v]) ->
    if op = "inc" then "cherry_inc" else iarr_prefix v ^ "_" ^ op
  | TApp (n, _) when op = "inc" && is_boxed_name n -> "cherry_inc"
  (* The runtime's own cells (ulib/c/cherry.h) have no counted fields, so the
     generic operations are the whole story. *)
  | TApp (n, _) when Options.custard_cherry () && is_runtime_name n -> "cherry_" ^ op
  | TApp (n, _) -> "cherry_" ^ op ^ "_" ^ c_name n
  | TArrow _ -> if op = "inc" then "cherry_inc" else "cherry_" ^ op ^ "_fn"
  | TExn -> if op = "inc" then "cherry_inc" else "cherry_exn_" ^ op
  | _ -> failwith "Custard: reference counting at a plain type"

(* A call of {!rc_fn}.  Marking takes the mode, which a generated marking
   function receives as [m] and passes on. *)
let rc_call (op:string) (t:cty) (x:string) : ML string =
  rc_fn op t ^ "(" ^ x ^ (if op = "mark" then ", m" else "") ^ ")"

(* Closures.  A function value is a [cherry_fn] (ulib/c/cherry.h), and the
   code that builds and calls one is generated on demand: printing a body
   files a request for each helper it uses, and {!cherry_closure_helpers}
   generates them -- and whatever those use in turn -- once every body has
   been printed. *)

(* The program's functions: their parameters and result. *)
let fn_sigs : ref (HashTable.t string (list binder & cty)) = mk_ref (HashTable.create 0)

type clo_req =
  | ReqPap   of name & int & cty  (** [f] applied to its first [k] arguments, at type [t] *)
  | ReqApply of cty & int         (** a call of a closure of this type, with [k] arguments *)
  | ReqPapc  of cty & int & int   (** a closure of arity [m] given [k < m] arguments *)

let clo_queue : ref (list clo_req) = mk_ref []
let clo_seen : ref (HashTable.t string bool) = mk_ref (HashTable.create 0)
let arrow_ids : ref (list (cty & int)) = mk_ref []

(* Under Cherry, the globals of function type, which hold closures: their
   types, since the head of an application is typed as its result. *)
let fn_globals : ref (HashTable.t string cty) = mk_ref (HashTable.create 0)
let fn_sig (n:name) : ML (option (list binder & cty)) =
  HashTable.try_find !fn_sigs (string_of_name n)

(* A function type, seen through abbreviations. *)
let rec arrow_view (t:cty) : ML (option (cty & cty)) =
  match t with
  | TArrow (a, _, b) -> Some (a, b)
  | TApp (n, []) ->
    (match find_type n with
     | Some { dt_body = TAbbrev t' } -> arrow_view t'
     | _ -> None)
  | _ -> None

(* The first [k] parameter types of [t], and what is left. *)
let rec arrow_take (k:int) (t:cty) : ML (list cty & cty) =
  if k <= 0 then ([], t) else
  match arrow_view t with
  | Some (a, b) -> let as_, r = arrow_take (k - 1) b in (a :: as_, r)
  | None -> failwith "Custard: a closure applied to more arguments than its type has"

let rec arrow_count (t:cty) : ML int =
  match arrow_view t with
  | Some (_, b) -> 1 + arrow_count b
  | None -> 0

(* How many parameters of [t] are not unit. *)
let rec nonunit_arrows (t:cty) : ML int =
  match arrow_view t with
  | Some (a, b) -> (if TUnit? a then 0 else 1) + nonunit_arrows b
  | None -> 0

(* The parameters of [t] up to and including its [c]-th that is not unit,
   with the unit ones right after it, and what is left.  A definition has no
   unit parameters (Mono's rule 1), so a closure's arity counts only the
   others, and C has none of them either. *)
let rec split_nonunit (c:int) (t:cty) : ML (list cty & cty) =
  match arrow_view t with
  | Some (a, b) when c > 0 || TUnit? a ->
    let ds, r = split_nonunit (if TUnit? a then c else c - 1) b in
    (a :: ds, r)
  | _ ->
    if c > 0 then failwith "Custard: a closure taking more arguments than its type has"
    else ([], t)

let arrow_id (t:cty) : ML string =
  match List.tryFind (fun (u, _) -> u = t) !arrow_ids with
  | Some (_, i) -> string_of_int i
  | None ->
    let i = List.length !arrow_ids in
    arrow_ids := !arrow_ids @ [(t, i)];
    string_of_int i

let clo_key (r:clo_req) : ML string =
  match r with
  | ReqPap (n, k, _) -> "pap " ^ string_of_name n ^ " " ^ string_of_int k
  | ReqApply (t, k) -> "apply " ^ arrow_id t ^ " " ^ string_of_int k
  | ReqPapc (t, k, m) -> "papc " ^ arrow_id t ^ " " ^ string_of_int k ^ " " ^ string_of_int m

let clo_request (r:clo_req) : ML unit =
  let key = clo_key r in
  if not (HashTable.mem !clo_seen key) then begin
    HashTable.add !clo_seen key true;
    clo_queue := !clo_queue @ [r]
  end

(* [lo, ..., hi]. *)
let rec range (lo hi:int) : ML (list int) =
  if lo > hi then [] else lo :: range (lo + 1) hi

let static_clo_name (n:name) : ML string = "cherry_clo_" ^ c_name n
let pap_name (n:name) (k:int) : ML string =
  "cherry_pap_" ^ c_name n ^ "_" ^ string_of_int k
let apply_name (t:cty) (k:int) : ML string =
  "cherry_apply_" ^ arrow_id t ^ "_" ^ string_of_int k
let papc_name (t:cty) (k m:int) : ML string =
  "cherry_papc_" ^ arrow_id t ^ "_" ^ string_of_int k ^ "_" ^ string_of_int m

(* An application Cherry compiles as a closure operation rather than a C
   call: a definition given fewer arguments than it takes, or anything that
   is not a definition. *)
let is_closure_app (hd:expr) (args:list expr) : ML bool =
  Options.custard_cherry () &&
  (match hd.e with
   | EQual (n, _) ->
     (match fn_sig n with
      | Some (bs, _) -> List.length args < List.length bs
      (* A global of function type holds a closure. *)
      | None -> Some? (HashTable.try_find !fn_globals (string_of_name n)))
   | _ -> true)

(* The typed variables pattern [p] binds against a scrutinee of type [t]. *)
let rec pat_var_tys (p:pat) (t:cty) : ML (list (string & cty)) =
  match p with
  | PVar x -> [(x, t)]
  | PCtor (cn, ps) ->
    (match (match find_exn cn with Some fs -> Some ((), fs) | None ->
            match find_ctor cn with Some (_, fs) -> Some ((), fs) | None -> None) with
     | Some (_, fs) ->
       List.zip (List.map snd fs) ps
       |> List.collect (fun (ft, q) -> pat_var_tys q ft)
     | None -> [])
  | PRecord (tn, fps) ->
    (match find_type tn with
     | Some ({ dt_body = TRecord fs }) ->
       fps |> List.collect (fun (f, q) ->
         match List.tryFind (fun (g, _) -> g = f) fs with
         | Some (_, ft) -> pat_var_tys q ft
         | None -> [])
     | _ -> [])
  | _ -> []

(* -------------------------------------------------------------------- *)
(* Types                                                                *)
(* -------------------------------------------------------------------- *)

(* Section 95.  [FStar.SizeT.t] is the target's own [size_t] unless
   [--custard_sizet_width 32] says otherwise, in which case it is
   [uint32_t] everywhere -- the type, the literal suffixes, and every cast,
   since a cast prints its target through this function.  Narrowing is
   correct exactly when the program assumes [FStar.SizeT.fits_u32]; F\* does
   not check that and neither does this. *)
let sizet_narrow () : ML bool = Options.custard_sizet_32 ()

let int_type (sw : signedness & iwidth) : ML string =
  let s, w = sw in
  match w with
  | WSizet -> if sizet_narrow () then "uint32_t" else "size_t"
  (* Section 119.  [<stdint.h>] has no [uint128_t]: [__int128] is a GCC/Clang
     extension, and its own spelling is the only one there is. *)
  | W128 ->
    (match s with Unsigned -> "unsigned __int128" | Signed -> "__int128")
  | _ ->
    (match s with Unsigned -> "uint" | Signed -> "int") ^
    (match w with W8 -> "8" | W16 -> "16" | W32 -> "32"
                | W64 -> "64" | W128 | WSizet -> "") ^ "_t"

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
    (* Section 100.  Rule 4 freezes only on the OCaml path now, so this
       explanation is true only there.  On a C backend a type that is still
       polymorphic was not held back by an external, and saying so would send
       a reader to change a signature that is not the problem. *)
    match (match n with
           | _ when Options.codegen () <> Some Options.OCaml -> None
           | None -> None
           | Some n -> HashTable.try_find frozen_by (string_of_name n)) with
    | Some ext ->
      let where =
        match (match n with
               | None -> None
               | Some n -> HashTable.try_find frozen_by_target (string_of_name n)) with
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
      (* Section 72.1.  A *root* is the one case where a surviving type
         variable is neither a bug nor a configuration problem.  Specialization
         is driven by call sites, and a root has none by definition -- so there
         is nothing to instantiate this variable against, and no setting makes
         one appear.  Error 364 has said exactly this for a monomorphized
         binder since section 19; saying "please report a Custard bug" for the
         type-variable form sent six of Kuiper's modules to the issue tracker
         for a correct refusal. *)
      if Some? (HashTable.try_find root_decls !current)
      then ["This declaration is a root, and a root has no call site.  \
             Specialization takes its type arguments from callers, so a root \
             that is still polymorphic has nothing to be specialized against \
             -- which is a fact about what was asked for, not a Custard bug.";
            "--custard_entry_module roots every definition in a module, \
             including polymorphic helpers that the program only ever calls \
             at concrete types.  Those are skipped now (section 72.1); this \
             one was named directly, so it was taken at its word.";
            "Root a concrete caller of it instead -- --custard_entry on the \
             definition that applies it -- or, if it is meant to be called \
             from outside the program, give it a monomorphic signature."]
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
  | "Prims.string" ->
    Some (if Options.custard_cherry () then "cherry_string" else "const char *")
  | "Prims.int" when Options.custard_cherry () -> Some "cherry_int"
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

(* Under Cherry the runtime compares [Prims.string] and [Prims.int] by
   contents; [content_eq t a b] is the C test that [a] and [b] are equal,
   when [t] is one of the two. *)
let is_int_ty (t:cty) : ML bool =
  match t with
  | TApp (n, []) ->
    None? n.spec && String.concat "." (n.ns @ [n.id]) = "Prims.int"
  | _ -> false

let content_eq (t:cty) (a b:string) : ML (option string) =
  if is_string_ty t then
    Some (if Options.custard_cherry ()
          then "cherry_str_eq(" ^ a ^ ", " ^ b ^ ")"
          else "strcmp(" ^ a ^ ", " ^ b ^ ") == 0")
  else if Options.custard_cherry () && is_int_ty t then
    Some ("cherry_int_eq(" ^ a ^ ", " ^ b ^ ")")
  else None

(* C declarations are not "type, then name": the [*] of a pointer and the
   [(...)] of a function bind to the *declarator*, so the name has to be built
   from the inside out.  [decl_of t x] is the declaration of [x] at type [t],
   and [x = ""] gives the abstract declarator -- the form a cast or a compound
   literal wants.  Building the two together is what lets a returned pointer
   ([uint32_t *f(void)]) and a stored function ([size_t ( *hashf)(size_t)]) come
   out right without special cases at each use. *)
(* Cherry: an upper bound on the number of 8-byte registers a value of type
   [t] occupies when passed or returned, or [None] when it may not fit in two
   and so may be passed or returned in memory.  Over-counting is safe: this
   only decides whether a tail call can be marked [musttail] (cherry.md, "Tail
   calls"), and a call that is not marked is merely an ordinary call. *)
let rec reg_words (fuel:int) (t:cty) : ML (option int) =
  let sum (ts:list cty) : ML (option int) =
    List.fold_left (fun acc t ->
      match acc, reg_words (fuel - 1) t with
      | Some a, Some b -> Some (a + b)
      | _ -> None) (Some 0) ts in
  let small (r:option int) : option int =
    match r with Some n when n <= 2 -> Some n | _ -> None in
  if fuel <= 0 then None else
  match t with
  | TUnit | TFloat _ | TArrow _ | TRef _ | TBuf _ | TExn -> Some 1
  | TInt (_, W128) -> Some 2
  | TInt _ -> Some 1
  | TAny -> Some 2
  | TTuple ts -> small (sum ts)
  | TApp ({ ns = ["FStar"; "ImmutableArray"; "Base"]; id = "t"; spec = None }, [_]) -> Some 1
  | TApp (n, _) when is_boxed_name n -> Some 1
  | TApp (n, []) when Some? (builtin_type n) -> Some 1
  | TApp (n, []) ->
    (match find_type n with
     | Some d when is_enum d -> Some 1
     | Some { dt_body = TAbbrev c } -> reg_words (fuel - 1) c
     | Some { dt_body = TRecord fs } -> small (sum (List.map snd fs))
     | Some ({ dt_body = TVariant [(_, fs)] }) -> small (sum (List.map snd fs))
     | Some { dt_body = TVariant cs } ->
       small (List.fold_left (fun acc (_, fs) ->
                match acc, sum (List.map snd fs) with
                | Some a, Some b -> Some (if a >= 1 + b then a else 1 + b)
                | _ -> None) (Some 1) cs)
     | _ -> None)
  | _ -> None

(* Whether values of type [t] are C scalars (integers and pointers) rather
   than structs. *)
let rec scalar_ty (fuel:int) (t:cty) : ML bool =
  if fuel <= 0 then false else
  match t with
  | TUnit | TFloat _ | TArrow _ | TRef _ | TBuf _ | TExn -> true
  | TInt (_, W128) -> false
  | TInt _ -> true
  | TApp ({ ns = ["FStar"; "ImmutableArray"; "Base"]; id = "t"; spec = None }, [_]) -> true
  | TApp (n, _) when is_boxed_name n -> true
  | TApp (n, []) when Some? (builtin_type n) -> true
  | TApp (n, []) ->
    (match find_type n with
     | Some d when is_enum d -> true
     | Some { dt_body = TAbbrev c } -> scalar_ty (fuel - 1) c
     | _ -> false)
  | _ -> false

(* Whether a call taking arguments of types [args] and returning [ret] can be
   a guaranteed tail call wherever its signature matches the caller's: every
   argument in registers, so the callee needs no stack slots the caller lacks,
   and the result in registers, since one returned in memory is copied after
   the call.  The result must moreover be a scalar: GCC 15 cannot keep the
   mark on a call returning a struct in a function that is then inlined into
   another marked call, and reports an error at [-O2].  Six is the integer registers of the x86-64 System V convention,
   the smallest of the targets [CHERRY_MUSTTAIL] is enabled on. *)
let musttail_sig_ok (args:list cty) (ret:option cty) : ML bool =
  (match ret with
   | None -> true
   | Some r -> scalar_ty 8 r) &&
  (match List.fold_left (fun acc t ->
           match acc, reg_words 8 t with
           | Some a, Some b when b <= 2 -> Some (a + b)
           | _ -> None) (Some 0) args with
   | Some n -> n <= 6
   | None -> false)

let rec decl_of (t:cty) (x:string) : ML string =
  match t with
  (* Every ML reference is the one runtime type; the cells differ, and the
     generated operations on each know which one theirs is. *)
  | TRef (RGc, _) when Options.custard_cherry () ->
    "cherry_ref" ^ (if x = "" then "" else " " ^ x)
  | TRef (RGc, _) ->
    reject "a garbage-collected reference (FStar.All.ref or FStarC.Effect.ref)"
      ["C has no garbage collector: use a Pulse reference, which is freed \
        explicitly, or --codegen Cherry, which counts references."]
  | TBuf e | TRef (_, e) -> decl_of e ("*" ^ x)
  (* A function cannot be stored, only a pointer to one, so a [TArrow] in a
     data position becomes a function pointer.  Custard has no closures --
     [EFun] in a value position is rejected below -- so the value is always a
     top-level definition, and its name is exactly this pointer. *)
  | TArrow _ when Options.custard_cherry () ->
    "cherry_fn" ^ (if x = "" then "" else " " ^ x)
  | TArrow _ ->
    let rec spine (t:cty) (acc:list cty) : ML (list cty & cty) =
      match t with
      | TArrow (a, _, b) -> spine b (a :: acc)
      | _ -> (List.rev acc, t) in
    let args, ret = spine t [] in
    (* Section 53.1.  This type has to spell what [signature] emits, and
       [signature] makes two changes an arrow does not: a [unit] result is
       [void], and a [unit] parameter is dropped.  Making the same two changes
       here is what lets a function be *passed* as well as called; leaving
       them out gave a pointer-to-function type returning [custard_unit]
       against a [void]-returning definition, in one translation unit, with
       no diagnostic. *)
    let args = args |> List.filter (fun a -> not (TUnit? a)) in
    let inner = "(*" ^ x ^ ")(" ^
                (match args with
                 | [] -> "void"
                 | _ -> String.concat ", " (args |> List.map (fun a -> decl_of a ""))) ^ ")" in
    if TUnit? ret then "void " ^ inner else decl_of ret inner
  | _ -> base_ty t ^ (if x = "" then "" else " " ^ x)

and base_ty (t:cty) : ML string =
  match t with
  (* Section 49.1.  [Simplify.inline_fields] removes every [TInline] and no
     backend ever sees one, so reaching here is a broken invariant rather than
     a program Custard cannot express -- hence a [failwith] and not an error
     368, which would blame the user for a bug of ours. *)
  | TInline _ ->
    failwith "Custard: an inline-field marker reached the C backend"
  | TUnit -> "custard_unit"
  | TInt sw -> int_type sw
  | TFloat Float32 -> "float"
  | TFloat Float64 -> "double"
  (* Sections 66 and 98.  Not [_Float16]/[__bf16]: those are not portable C.
     The name is the consumer's to define -- on a target with the formats in
     hardware it is a native type or a device intrinsic, and Custard emits the
     name either way. *)
  | TFloat Float16 -> "custard_f16"
  | TFloat BFloat16 -> "custard_bf16"
  (* Section 69.  A non-type template argument, spelled by its value.  As with
     a [#define] (section 68) the integer form is bare: a template-id is a
     constant expression already, and the cast Custard adds elsewhere would
     only be noise inside the angle brackets. *)
  (* No width suffix: a non-type template parameter has a declared type and
     the argument is converted to it, so [16ULL] would be noise where the
     consumer wrote, and reads, [16]. *)
  | TConst (CInt (v, b, _)) -> c_int_lit_to_string v b
  | TConst (CBool b) -> if b then "true" else "false"
  | TConst c ->
    E.raise_error0 E.Error_CustardBadTemplateArg [
      text "Custard: this external type is applied to a constant that cannot \
            be a template argument.";
      text "A non-type template parameter may be an integer or a bool.  A \
            float, a character or a string is not one, and neither is unit." ]
  (* Section 69.  An applied external type whose target is a template: the
     arguments go into the target's placeholders and become a C++ template-id.
     This is the one applied type C prints, and it is not an exception to
     uniform compilation (section 5.0) so much as an admission that the
     *target's* type language has parameters even though C's does not, and
     that a consumer writing against [wmma::fragment] or [std::bitset] has to
     be able to say so. *)
  | TApp (n, args) when Some? (extern_template_of n) ->
    let ps = (match extern_template_of n with Some ps -> ps | None -> []) in
    String.concat "" (ps |> List.map (fun p ->
      match p with
      | TP_lit s -> s
      | TP_arg i ->
        match snd (List.splitAt i args) with
        | a :: _ -> base_ty a
        | [] ->
          E.raise_error0 E.Error_CustardBadTemplateArg [
            text ("Custard: the target of the external type " ^
                  string_of_name n ^ " mentions argument " ^ show i ^
                  ", but the type has only " ^ show (List.length args) ^
                  " argument(s).");
            text "The placeholders in a [@@custard_extern] string count the \
                  declaration's binders from zero, all of them, in source \
                  order." ]))
  | TApp ({ ns = ["FStar"; "ImmutableArray"; "Base"]; id = "t"; spec = None }, [_]) when Options.custard_cherry () ->
    "cherry_iarray"
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
  (* Cherry: [FStar.Dyn.dyn], a value with the type information that
     releases it (cherry.md, "The any type"). *)
  | TAny when Options.custard_cherry () -> "cherry_any"
  | TAny ->
    reject "a value whose representation is unknown (TAny)"
      ["Run with --custard_warn_any to see where the representation was lost \
        (section 5.9)."]
  | TExn when Options.custard_cherry () -> "cherry_exn"
  | TExn ->
    reject "an exception type"
      ["C has no exceptions."]
  | TBuf _ | TRef (_, _) | TArrow _ -> decl_of t ""

(* The abstract declarator: a type as a cast or a compound literal spells it. *)
let ty (t:cty) : ML string = decl_of t ""

(* Cherry: how the C of a call in tail position of the definition being
   printed starts -- the name of the function it calls, or for a closure the
   prefix of every apply helper -- when the call can be a guaranteed tail call: a definition,
   given all its arguments, or a closure through its apply helper, whose C
   signature passes everything in registers and returns what the caller
   returns.  [None] for anything else, which stays an ordinary call. *)
let musttail_head (hd:expr) (args:list expr) (ret:cty) : ML (option string) =
  if not !musttail_ok then None else
  let caller_ret = match !cur_ret with Some t -> decl_of t "" | None -> "" in
  let nonunit (ts:list cty) = List.filter (fun t -> not (TUnit? t)) ts in
  if is_closure_app hd args then
    (match hd.e with
     | EQual (n, _) when Some? (fn_sig n) -> None
     | _ ->
       if !void_ret || TUnit? ret || decl_of ret "" <> caller_ret then None
       else if musttail_sig_ok (TArrow (TUnit, E_Pure, TUnit) ::
                                nonunit (List.map (fun (a:expr) -> a.ty) args)) (Some ret)
       then Some "cherry_apply_"
       else None)
  else
    match hd.e with
    | EQual (n, _) ->
      let f = string_of_name n in
      if Some? (HashTable.try_find !externs f) then None else
      (match fn_sig n with
       | None -> None
       | Some (bs, fret) ->
         let tys = List.map (fun (b:binder) -> b.b_ty) bs in
         let tys = match HashTable.try_find !keeps f with
                   | Some flags -> filter_by flags tys
                   | None -> nonunit tys in
         let void = Some? (HashTable.try_find !void_fns f) in
         if void <> !void_ret then None
         else if not void && decl_of fret "" <> caller_ret then None
         else if musttail_sig_ok tys (if void then None else Some fret)
         then Some (c_name n ^ "(")
         else None)
    | _ -> None

(* Cherry: the target of a call in tail position that is a jump rather than a
   call ({!tail_targets}): one the definition being printed can jump to,
   given all its kept arguments. *)
let tail_target (n:name) (args:list expr)
  : ML (option (string & string & list (binder & string))) =
  let f = string_of_name n in
  match !tail_targets |> List.tryFind (fun (g, _, _) -> g = f) with
  | Some (_, label, bs) ->
    let args = match HashTable.try_find !keeps f with
               | Some flags -> filter_by flags args
               | None -> args in
    if List.length args = List.length bs then Some (f, label, bs) else None
  | None -> None

(* -------------------------------------------------------------------- *)
(* Structural equality (section 107)                                    *)
(* -------------------------------------------------------------------- *)

(* C's [==] is defined on arithmetic types and on pointers, and on nothing
   else.  F*'s is defined at every type with decidable equality, which
   includes every inductive one -- so [Known = x] on a two-constructor
   datatype, which is an ordinary thing to write, reached the C compiler as
   [(VariantEq_kind){ .tag = VARIANTEQ_KNOWN } == x] and was rejected.  It is
   not a rare shape: a record, a tuple and an [option] are all struct types
   here, and all four spellings were emitted.

   A datatype's equality *is* structural, and the structure is known -- the
   layout is the one this file just chose -- so the comparison is generated
   rather than refused: one [static bool T__eq(T, T)] per type compared, tag
   first and then the payload of that tag, recursing into fields that are
   themselves aggregates.  [check_finite] has already established that no
   struct contains itself by value, so the recursion terminates; a field
   reached through a pointer compares as a pointer, which is what F* means by
   equality there as well, since such a type carries no [hasEq] and cannot be
   the argument of a [=] in the first place.

   An external type is left with [==]: it has no body to read, and its target
   may well be a scalar typedef or a C++ class with an [operator==] of its
   own.  An enum is left with [==] too, that being the representation it got.

   The functions are collected while the bodies are printed and emitted
   afterwards, above them, behind prototypes -- the same arrangement the
   program's own definitions use, and for the same reason. *)
let eq_queue : ref (list (string & dtype & string & list string)) = mk_ref []
let eq_seen : ref (HashTable.t string string) = mk_ref (HashTable.create 20)

(* Issue 4715.  The fields a generated comparison has descended through,
   outermost first, so that a type with no comparison found deep inside a
   record can say which record and which field led there.  A queued helper
   carries the declaration and path that first asked for it, since it is
   drained after the declaration that asked has been printed. *)
let eq_path : ref (list string) = mk_ref []

(* Section 116.  Every C name the program itself defines, as the file will
   spell it -- filled after {!build_renames}, since a rename changes what that
   spelling is.  A generated name is *allocated* against this rather than
   assumed free: [T__eq] is a perfectly ordinary F* identifier, and a program
   with its own [pair__eq] got two definitions of it, one of them with the
   wrong type.  The two sides could not both be right by construction, because
   only one of them knew the whole set of names in the file. *)
let taken_names : ref (HashTable.t string bool) = mk_ref (HashTable.create 50)

(* [base], or the first [base_1], [base_2], ... that nothing else has taken.
   Registered on the way out, so two generated names cannot collide either. *)
let alloc_name (base:string) : ML string =
  let rec go (cand:string) (n:int) : ML string =
    if None? (HashTable.try_find !taken_names cand) then cand
    else go (base ^ "_" ^ string_of_int n) (n + 1) in
  let f = go base 1 in
  HashTable.add !taken_names f true;
  f

let rec mentions_any (t:cty) : ML bool =
  match t with
  | TAny -> true
  | TArrow (a, _, b) -> mentions_any a || mentions_any b
  | TApp (_, ts) | TTuple ts -> List.existsb mentions_any ts
  | TBuf c | TRef (_, c) | TInline c -> mentions_any c
  | _ -> false

let with_eq_step (#a:Type) (step:string) (f:unit -> ML a) : ML a =
  let saved = !eq_path in
  eq_path := saved @ [step];
  let r = f () in
  eq_path := saved;
  r

let rec eq_target (t:cty) : ML (option dtype) =
  match t with
  | TApp ({ ns = ["FStar"; "ImmutableArray"; "Base"]; id = "t" }, _) ->
    reject "an equality test on an immutable array"
      ["Cherry does not compare immutable arrays yet."]
  (* Issue 4715.  Under Cherry a [TAny] is a [dyn], a box around a value of
     any type, and nothing knows how to compare two of them: C's [==] on the
     box does not compile.  [dyn] is not an eqtype, so only --lax or an
     assumed [hasEq] gets here. *)
  | TAny when Options.custard_cherry () ->
    E.raise_error0 E.Error_CustardNoCRepresentation
      ([text ("Custard: an equality test at FStar.Dyn.dyn, in " ^ !current ^ ".");
        text "Cherry cannot compare two dyn values: dyn is not an eqtype, \
              so the test is only reachable under --lax or an assumed hasEq."]
       @ (match !eq_path with
          | [] -> []
          | ps -> [text ("The dyn is reached by comparing " ^
                         String.concat ", then " ps ^ ".")])
       @ chain_msg ())
  | TApp (n, []) when None? (builtin_type n) ->
    (match find_type n with
     | Some d when List.existsb Extern? d.dt_flags -> None
     | Some d when is_boxed_ty t -> Some d
     | Some d ->
       (match d.dt_body with
        | TAbbrev u ->
          with_eq_step ("the abbreviation " ^ string_of_name d.dt_name)
            (fun () -> eq_target u)
        | TRecord _ -> Some d
        | TVariant _ -> if is_enum d then None else Some d
        | TAbstract -> None)
     | None -> None)
  | _ -> None

(* The helper for [t], registering it to be emitted the first time it is
   asked for. *)
let eq_fn_of (t:cty) : ML (option string) =
  match eq_target t with
  | None -> None
  | Some d ->
    (* Section 116.  Memoized on the *type*, not on the name it settled on:
       the allocation above hands out a different name each time it is asked,
       so asking twice for the same type has to return the first answer. *)
    let k = string_of_name d.dt_name in
    (match HashTable.try_find !eq_seen k with
     | Some f -> Some f
     | None ->
       let f = alloc_name (c_name d.dt_name ^ "__eq") in
       HashTable.add !eq_seen k f;
       eq_queue := !eq_queue @ [(f, d, !current, !eq_path)];
       Some f)

let eq_proto (f:string) (d:dtype) : ML string =
  let n = c_name d.dt_name in
  "static bool " ^ f ^ "(" ^ n ^ " a, " ^ n ^ " b);\n"

let eq_def (f:string) (d:dtype) : ML string =
  let n = c_name d.dt_name in
  let fn = string_of_name d.dt_name in
  let hd = "static bool " ^ f ^ "(" ^ n ^ " a, " ^ n ^ " b) {\n" in
  (* Section 44.2 again: [const char *] compares by contents.  [step] names
     the field for a rejection further down (issue 4715). *)
  let cmp (step:string) (a:string) (b:string) (t:cty) : ML string =
    match content_eq t a b with
    | Some c -> c
    | None -> match with_eq_step step (fun () -> eq_fn_of t) with
         | Some g -> g ^ "(" ^ a ^ ", " ^ b ^ ")"
         | None -> "(" ^ a ^ " == " ^ b ^ ")" in
  let field (cn:option name) (g:string) : string =
    "field " ^ g ^
    (match cn with Some c -> " of constructor " ^ c.id | None -> "") ^
    " of " ^ fn in
  let all (cn:option name) (pa:string) (pb:string) (fs : list (string & cty)) : ML string =
    match fs with
    | [] -> "true"
    | _ -> String.concat " && " (fs |> List.map (fun (g, t) ->
             cmp (field cn g) (pa ^ "." ^ c_var g) (pb ^ "." ^ c_var g) t)) in
  (* Nothing to read: the parameters are named, so they have to be used. *)
  let trivial = "  (void)a; (void)b;\n  return true;\n}\n" in
  let direct (cn:option name) (fs : list (string & cty)) : ML string =
    if Nil? fs then hd ^ trivial
    else hd ^ "  return " ^ all cn "a" "b" fs ^ ";\n}\n" in
  match d.dt_body with
  (* Cherry: a cell.  The same pointer, or the same scalar, is equal to
     itself; otherwise both have to be cells with the same tag.  The last
     field of this very type is compared by going round again rather than
     by a call, so that two long lists compare in constant stack. *)
  | TVariant cs when is_boxed d ->
    let is_self (t:cty) : ML bool =
      match t with TApp (m, []) -> c_name m = n | _ -> false in
    hd ^ "  for (;;) {\n" ^
    "    if (a == b) return true;\n" ^
    "    if (cherry_is_scalar(a) || cherry_is_scalar(b) || a->tag != b->tag) return false;\n" ^
    "    switch (a->tag) {\n" ^
    String.concat "" (cs |> List.collect (fun (cn, fs) ->
      if Nil? fs then [] else
      let cell = cell_struct d cn in
      let next = fs |> List.filter (fun (_, t) -> is_self t) |> List.rev |> List.map fst in
      let others = (match next with
                    | f :: _ -> fs |> List.filter (fun (g, _) -> g <> f)
                    | [] -> fs) in
      ["      case " ^ c_tag cn ^ ": {\n" ^
       "        " ^ cell ^ " *x = (" ^ cell ^ " *)a, *y = (" ^ cell ^ " *)b;\n" ^
       (if Nil? others then ""
        else "        if (!(" ^ String.concat " && " (others |> List.map (fun (g, t) ->
               cmp (field (Some cn) g) ("x->" ^ c_var g) ("y->" ^ c_var g) t)) ^ ")) return false;\n") ^
       (match next with
        | f :: _ -> "        a = x->" ^ c_var f ^ "; b = y->" ^ c_var f ^ ";\n        break;\n"
        | [] -> "        return true;\n") ^
       "      }\n"])) ^
    "      default: return false;\n    }\n  }\n}\n"
  | TRecord fs -> direct None fs
  | TVariant cs when single_ctor d ->
    let cn, fs = List.hd cs in direct (Some cn) fs
  | TVariant cs ->
    hd ^ "  if (a.tag != b.tag) return false;\n" ^
    "  switch (a.tag) {\n" ^
    String.concat "" (cs |> List.map (fun (cn, fs) ->
      "    case " ^ c_tag cn ^ ": return " ^
      (if Nil? fs then "true"
       else if arm_flat fs
       then cmp (field (Some cn) (fst (List.hd fs)))
                ("a.val." ^ arm_name cn) ("b.val." ^ arm_name cn)
                (snd (List.hd fs))
       else all (Some cn) ("a.val." ^ arm_name cn)
                ("b.val." ^ arm_name cn) fs) ^ ";\n")) ^
    (* Every tag is a case, so this is unreachable -- and C still wants a
       [return] on the path that falls out of the switch. *)
    "  }\n  return true;\n}\n"
  | _ -> hd ^ trivial

(* Drain the queue, which grows while it is drained: a generated comparison
   may be the first thing to ask for the one on a field's type. *)
let eq_decls () : ML (list string & list string) =
  let protos : ref (list string) = mk_ref [] in
  let defs : ref (list string) = mk_ref [] in
  let rec go (fuel:int) : ML unit =
    if fuel <= 0 then failwith "Custard: generated equalities do not settle"
    else match !eq_queue with
    | [] -> ()
    | (f, d, origin, path) :: rest ->
      eq_queue := rest;
      protos := !protos @ [eq_proto f d];
      let saved_current, saved_path = !current, !eq_path in
      current := origin;
      eq_path := path;
      defs := !defs @ [eq_def f d];
      current := saved_current;
      eq_path := saved_path;
      go (fuel - 1) in
  go 10000;
  (!protos, !defs)

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
let int_suffix (sw : signedness & iwidth) : ML string =
  let s, w = sw in
  let wide = (match w with W64 | W128 -> true
                         | WSizet -> not (sizet_narrow ()) | _ -> false) in
  match s with
  | Unsigned -> if wide then "ULL" else "U"
  | Signed -> if wide then "LL" else ""

(* [-9223372036854775808LL] is not a literal: it is unary minus applied to
   [9223372036854775808LL], whose magnitude is one past [LLONG_MAX].  Every
   signed width has this one value, and only at 64 bits is there no wider type
   to fall back on -- so it is written the way [<stdint.h>] writes [INT64_MIN]. *)
let int_literal (sw : signedness & iwidth) (v:int) (b:int_base) : ML string =
  let sg, w = sw in
  let wide = (match w with W64 -> true
                         | WSizet -> not (sizet_narrow ()) | _ -> false) in
  (* Section 119.  C has no 128-bit literal and no suffix that produces one,
     so a 128-bit constant is built: the low 64 bits as a literal, and as many
     high ones as it has shifted in above them.  Written out rather than
     computed from the halves at run time because an initializer needs a
     constant expression, and this is one.

     Always assembled at [unsigned __int128], even for a signed width, and
     cast afterwards.  Two reasons, and they are the reasons the [LLONG_MIN]
     case below exists: the most negative value has no positive counterpart,
     so a magnitude built at the signed type would overflow it for exactly
     the value that needs it most; and a magnitude that has bit 127 set is
     not a signed value at all.  Negation at an unsigned type wraps by
     definition (6.2.5), which is the computation wanted. *)
  if w = W128 then
    let neg = v < 0 in
    let a = if neg then -v else v in
    let lo = a % 18446744073709551616 in
    let hi = a / 18446744073709551616 in
    let u = "(unsigned __int128)" in
    if hi = 0 && not neg
    then "((" ^ int_type sw ^ ")" ^ c_int_lit_to_string lo b ^ "ULL)"
    else
      let mag =
        if hi = 0 then "(" ^ u ^ c_int_lit_to_string lo b ^ "ULL)"
        else "((" ^ u ^ c_int_lit_to_string hi b ^ "ULL << 64) | " ^
             u ^ c_int_lit_to_string lo b ^ "ULL)" in
      let e = if neg then "(-" ^ mag ^ ")" else mag in
      (if Signed? sg then "((" ^ int_type sw ^ ")" ^ e ^ ")" else e)
  else
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
      (* C string escapes are octal; three digits always, so that a digit
         after one is not read as part of it. *)
      let oct (b:int) : ML string =
        "\\" ^ show (b / 64) ^ show ((b / 8) % 8) ^ show (b % 8) in
      (* An F* string is a sequence of code points, and its C spelling is
         their UTF-8 encoding, one escape per byte. *)
      if i < 32 || i = 127 then oct i
      else if i < 127 then BU.string_of_char c
      else if i < 0x800 then oct (0xC0 + i / 64) ^ oct (0x80 + i % 64)
      else if i < 0x10000 then
        oct (0xE0 + i / 4096) ^ oct (0x80 + (i / 64) % 64) ^ oct (0x80 + i % 64)
      else
        oct (0xF0 + i / 262144) ^ oct (0x80 + (i / 4096) % 64) ^
        oct (0x80 + (i / 64) % 64) ^ oct (0x80 + i % 64)
  in
  String.concat "" (List.map esc (String.list_of_string s))

(* Cherry's debug mode (cherry.h, CHERRY_DEBUG): the message a failed check
   prints, as a C string literal naming the declaration it is in. *)
let debug_what (what:string) : ML string =
  "\"" ^ escape (what ^ " in " ^ !current) ^ "\""

(* -------------------------------------------------------------------- *)
(* Section 66: the 16-bit formats                                       *)
(* -------------------------------------------------------------------- *)

(* The parameters of the two narrow formats: fraction bits stored, and the
   exponent range.  binary16 is IEEE 754's, bfloat16 has binary32's exponent
   with binary32's fraction truncated to 7 stored bits. *)
let narrow_params (fw:fwidth) : ML (int & int & int) =
  match fw with
  | Float16   -> (10, -14, 15)
  | BFloat16  -> (7, -126, 127)
  | _ -> failwith "Custard: narrow_params at a wide float width"

let rec pow_int (b:int) (n:nat) : Tot int (decreases n) =
  if n = 0 then 1 else b * pow_int b (n - 1)

(* [floor (log2 (num/den))] for a strictly positive rational, by comparison
   alone: the value is exact, so this is too, and no float is involved. *)
let ilog2_rat (num:int) (den:int) : ML int =
  (* Scale until num/den lands in [1,2). *)
  let rec go (e:int) (n:int) (d:int) (fuel:nat) : ML int =
    if fuel = 0 then e
    else if n >= d * 2 then go (e + 1) n (d * 2) (fuel - 1)
    else if n < d then go (e - 1) (n * 2) d (fuel - 1)
    else e in
  go 0 num den 4096

(* Round [num/den] to the nearest integer, ties to even.  Both arguments are
   strictly positive. *)
let round_ne (num:int) (den:int) : ML int =
  let q = num / den in
  let r = num - q * den in
  if r * 2 > den then q + 1
  else if r * 2 < den then q
  else if q % 2 = 1 then q + 1 else q

(* The literal's exact value, correctly rounded to [fw], as a bit pattern.
   The value is [mantissa * 10^exponent], which is a rational with an exact
   integer numerator and denominator, so every step below is integer
   arithmetic and the single rounding is {!round_ne}'s. *)
let narrow_float_bits (fw:fwidth) (v:float_lit) : ML int =
  let (p, emin, emax) = narrow_params fw in
  let ebits = if Float16? fw then 5 else 8 in
  let sign_bit (neg:bool) : int = if neg then pow_int 2 (p + ebits) else 0 in
  (* Section 125.5.  Both formats here are encoded by hand, so the special
     values are encoded by hand too: a saturated exponent, with a zero
     significand for an infinity and the leading fraction bit set -- a quiet
     NaN -- for a NaN. *)
  match v with
  | FLInf neg -> sign_bit neg + (pow_int 2 ebits - 1) * pow_int 2 p
  | FLNan -> (pow_int 2 ebits - 1) * pow_int 2 p + pow_int 2 (p - 1)
  | FLNum (neg, mag) ->
  let m = Real.mantissa mag in
  let e10 = Real.exponent mag in
  let (num, den) =
    if e10 >= 0 then (m * pow_int 10 e10, 1)
    else (m, pow_int 10 (- e10)) in
  let sign = sign_bit neg in
  if num = 0 then sign
  else begin
    let e = ilog2_rat num den in
    (* Scale so that rounding to an integer leaves [p] fraction bits.  Below
       [emin] the exponent is pinned and the result is subnormal, which is
       gradual underflow and not a special case in the arithmetic. *)
    let e = if e < emin then emin else e in
    let sh = p - e in
    let (n2, d2) =
      if sh >= 0 then (num * pow_int 2 sh, den)
      else (num, den * pow_int 2 (- sh)) in
    let q = round_ne n2 d2 in
    (* Rounding may have carried the significand up a binade. *)
    let (q, e) = if q >= pow_int 2 (p + 1) then (q / 2, e + 1) else (q, e) in
    let bias = pow_int 2 (ebits - 1) - 1 in
    if e > emax then sign + (pow_int 2 ebits - 1) * pow_int 2 p   (* infinity *)
    else if q < pow_int 2 p then sign + q                          (* subnormal *)
    else sign + (e + bias) * pow_int 2 p + (q - pow_int 2 p)
  end

(* A compound literal, which at file scope has static storage duration and is
   a valid initializer -- see the comment at {!constant}. *)
let narrow_float_lit' (fw:fwidth) (v:float_lit) (sfx:string) : ML string =
  let b = narrow_float_bits fw v in
  "CUSTARD_" ^ (if Float16? fw then "F16" else "BF16") ^ sfx ^ "(" ^ show b ^ "U)"

let narrow_float_lit (fw:fwidth) (v:float_lit) : ML string =
  narrow_float_lit' fw v "_LIT"

(* Initializer position; see the two macros' comment in the support header. *)
let narrow_float_init (fw:fwidth) (v:float_lit) : ML string =
  narrow_float_lit' fw v "_INIT"

(* Section 98.  The two 16-bit floating-point formats are the consumer's:
   Custard emits calls into a vocabulary it does not implement, and the
   header naming that vocabulary arrives here through [@@custard_c_header].
   The block used to carry the whole vocabulary as a comment, which put forty
   lines of reference material in every file that touched a narrow float.
   The reference belongs in the reference manual, so what is left is the
   check and a pointer to it.  Emitted into whichever of the two files
   mentions a narrow float, and into the header only if the header does. *)
let narrow_support : string =
  String.concat "\n" [
    "";
    "#ifndef CUSTARD_FLOAT16_DEFINED";
    "#error \"Custard: this program uses binary16 or bfloat16, which Custard \
     does not implement.  Supply custard_f16/custard_bf16 and their \
     operations in a @@custard_c_header and define CUSTARD_FLOAT16_DEFINED; \
     section 98 of doc/ref/custard.md lists the vocabulary.\"";
    "#endif";
    "";
  ]

(* Whether a rendered file mentions the narrow-float vocabulary.  A textual
   test rather than a flag set while rendering, because the question is about
   one of the two files and a flag cannot say which -- and because every way
   of reaching those formats spells one of these four prefixes, so the test
   is exact rather than approximate. *)
let mentions_narrow (s:string) : bool =
  BU.contains s "custard_f16" || BU.contains s "custard_bf16" ||
  BU.contains s "CUSTARD_F16_" || BU.contains s "CUSTARD_BF16_"

(* Section 5.1.  The sole inhabited erased value: a distinct typedef rather
   than void, so that it can be stored in a variable and returned like any
   other value.  Guarded because two generated headers may meet in one
   translation unit (section 42.2): this is a fixed name for a fixed type, so
   two spellings of it are the same spelling.  Emitted only where it is used,
   which for a whole program is usually nowhere -- the layout pass erases
   unit fields, a unit-returning function is [void], and the unit arguments
   of section 32.6 are dropped -- so the typedef was boilerplate in every
   header and a use in none of them. *)
let unit_support : string =
  "#ifndef CUSTARD_UNIT_DEFINED\n\
   #define CUSTARD_UNIT_DEFINED\n\
   typedef uint8_t custard_unit;\n\
   #endif\n"

let mentions_unit (s:string) : bool = BU.contains s "custard_unit"

(* Section 125.5.  A NaN and an infinity are [<math.h>]'s [NAN] and
   [INFINITY], which is the only portable spelling of either: C has no
   floating-point constant syntax for them, so a literal cannot be written and
   a [0.0/0.0] would be a constraint violation in a constant expression.

   They get macro names of their own rather than being emitted bare, for the
   same reason section 123 gives: placement is decided by asking whether a
   rendered file mentions the names, and [NAN] is a token short and ordinary
   enough that a generated identifier could contain it.  [CUSTARD_NAN] cannot
   be anything but this.

   [NAN] and [INFINITY] are of type [float], which is the narrower of the two
   and converts to [double] exactly, so one spelling serves both widths. *)
let float_special_support : string =
  "#ifndef CUSTARD_FLOAT_SPECIAL_DEFINED\n\
   #define CUSTARD_FLOAT_SPECIAL_DEFINED\n\
   #include <math.h>\n\
   #define CUSTARD_NAN NAN\n\
   #define CUSTARD_INF INFINITY\n\
   #endif\n"

let mentions_float_special (s:string) : bool =
  BU.contains s "CUSTARD_NAN" || BU.contains s "CUSTARD_INF"

(* Under Cherry a string literal is a static, immortal cell
   ([CHERRY_STRING_LIT]), one per distinct literal, defined above the
   functions. *)
let string_lits : ref (HashTable.t string string) = mk_ref (HashTable.create 0)
let string_lit_defs : ref (list string) = mk_ref []

let string_lit (s:string) : ML string =
  match HashTable.try_find !string_lits s with
  | Some n -> n
  | None ->
    let n = alloc_name "cherry_lit" in
    HashTable.add !string_lits s n;
    string_lit_defs := !string_lit_defs @
      ["CHERRY_STRING_LIT(" ^ n ^ ", \"" ^ escape s ^ "\");\n"];
    n

(* Cherry: an integer literal that is not a small integer on every target is
   a static persistent cell ([CHERRY_INT_LIT] in cherry.h), one per value, so
   evaluating it allocates nothing.  One that is small where small integers
   have 63 bits is [CHERRY_INT_WIDE], which is that small integer there. *)
let int_lits : ref (HashTable.t string string) = mk_ref (HashTable.create 0)

let rec limbs (m:int) : ML (list string) =
  if m = 0 then [] else (show (m % 4294967296) ^ "u") :: limbs (m / 4294967296)

let int_lit (v:int) : ML string =
  let n =
    match HashTable.try_find !int_lits (show v) with
    | Some n -> n
    | None ->
      let n = alloc_name "cherry_intlit" in
      HashTable.add !int_lits (show v) n;
      let ds = limbs (if v < 0 then - v else v) in
      string_lit_defs := !string_lit_defs @
        ["CHERRY_INT_LIT(" ^ n ^ ", " ^ (if v < 0 then "1" else "0") ^ ", " ^
         show (List.length ds) ^ ", " ^ String.concat ", " ds ^ ");\n"];
      n in
  if v < 4611686018427387904 && v >= - 4611686018427387904
  then "CHERRY_INT_WIDE(INT64_C(" ^ show v ^ "), " ^ n ^ ")"
  else "((cherry_int)&" ^ n ^ ")"

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
       the suffix of the width it is meant to have, and the cast only narrows.

       Section 119's 128-bit literal is the exception: it is not a literal but
       an expression assembled out of two of them, and it carries its own
       casts because it has to -- so a cast here would only be a second one. *)
    if snd sw = W128 then int_literal sw v b
    else "((" ^ int_type sw ^ ")" ^ int_literal sw v b ^ ")"
  | CInt (v, _, None) when Options.custard_cherry () ->
    if v < 1073741824 && v > -1073741824
    then "CHERRY_INT_SMALL(" ^ show v ^ ")"
    else int_lit v
  | CString s when Options.custard_cherry () -> "((cherry_string)&" ^ string_lit s ^ ")"
  | CInt (v, b, None) ->
    reject ("the unbounded integer literal " ^ int_lit_to_string v b)
      ["Prims.int has no C representation; use a machine integer type."]
  (* Section 39.  The literal, with the suffix that gives it the width it is
     meant to have: an unsuffixed C float literal is a [double], so [Float32]
     arithmetic would be done at double precision and rounded once at the end.
     No cast, because a cast cannot supply the literal's own type and the
     suffix already does. *)
  (* Section 125.5.  The special values are macros, so there is no suffix to
     add: [CUSTARD_NANf] would be an identifier. *)
  | CFloat (FLNan, fw) when Float32? fw || Float64? fw -> "CUSTARD_NAN"
  | CFloat (FLInf neg, fw) when Float32? fw || Float64? fw ->
    if neg then "(-CUSTARD_INF)" else "CUSTARD_INF"
  | CFloat (v, Float32) -> float_lit_to_string v ^ "f"
  | CFloat (v, Float64) -> float_lit_to_string v
  (* Section 66.  At the narrow widths the type is a struct, so there is no
     literal to suffix: what is emitted is the *bit pattern*, in a compound
     literal.  Two reasons, and neither is style.

     Statically initializable.  [custard_f16_of_f32(0.5f)] is a function call,
     so an object with static storage duration could not be initialized with
     it at all; a bit pattern can be, through [CUSTARD_F16_INIT] -- the
     braced spelling {!narrow_float_init} emits, since the compound literal
     this case produces is itself not a constant expression.

     One rounding.  Encoding the literal's exact value directly to binary16 is
     correctly rounded by construction, where routing it through [float] would
     round twice -- decimal to binary32, then binary32 to binary16 -- and
     double rounding is visibly wrong at a format this narrow.  1.00048828125
     is the midpoint between 1 and the next binary16, and is exact in
     binary32; [1.000488281250001] is above it, so the correct answer is the
     next value up, 0x3C01.  Via binary32 it rounds first to the midpoint and
     then ties-to-even down to 1.0, giving 0x3C00. *)
  | CFloat (v, fw) -> narrow_float_lit fw v
  | CChar c -> "((uint32_t)" ^ show (BU.int_of_char c) ^ ")"
  | CString s -> "\"" ^ escape s ^ "\""

(* Section 59.  The same literal, for a position where C already converts it
   to the type it is meant to have: the initializer of a declaration of that
   type, an assignment to it, a [return], a field of a compound literal, the
   element written into a fresh array.  In every one of those the conversion
   is *assignment* conversion (6.5.16.1), which is exactly what the cast in
   {!constant} was doing, so spelling the cast as well says it twice.

   The suffix is a separate question and cannot always go with the cast:
   C gives a decimal literal the first *signed* type it fits in (6.4.4.1),
   so a value too large for that has no type and a conforming compiler must
   diagnose it -- which is why {!constant} carries the suffix in the first
   place.  A value C guarantees an [int] holds can drop it; anything else
   keeps it and loses only the cast.

   The bound is the standard's, not the platform's.  [INT_MAX] is only
   guaranteed to be 32767 (5.2.4.2.1), and while no target Custard emits for
   has a 16-bit [int], a printer that is right by construction is worth more
   here than four extra characters on a literal above 32767 -- and the
   literals this is about, lengths and indices and small tags, are almost all
   below it. *)
let converted_int (target:cty) (e_ty:cty) (c:Custard.Syntax.constant) : ML (option string) =
  match c with
  | CInt (v, b, Some sw) when target = e_ty && e_ty = TInt sw ->
    if -32767 <= v && v <= 32767
    then Some (c_int_lit_to_string v b)
    else Some (int_literal sw v b)
  (* Section 43: a character is a code point, and {!constant} gives it its
     type with a cast because there is no suffix that would.  In a
     converting position it needs neither, and no test on [e_ty] is right
     here -- the char type is *realized* (an abstract [TApp] a rule spells
     as [uint32_t]), not a [TInt], so matching on [TInt] would never fire
     and matching on the [TApp] would hard-code one rule's name.  That the
     position converts to the value's own type is the whole condition. *)
  | CChar c when target = e_ty && BU.int_of_char c <= 32767 ->
    Some (show (BU.int_of_char c))
  | _ -> None

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

(* Section 66.  At the two narrow widths the operand type is a struct, so
   there is no C operator to emit and the operation is a call into the support
   header instead.  This is the reason [Float16] and [BFloat16] are separate
   [fwidth] constructors rather than a width field: the *shape* of the emitted
   code differs, not just a type name.

   The names are the header's, and the vocabulary is exactly {!Builtins.float_op}'s
   -- anything outside it never becomes an [EOp] in the first place. *)
let narrow_ty (fw:fwidth) : bool = Float16? fw || BFloat16? fw

let narrow_pfx (fw:fwidth) : ML string =
  if Float16? fw then "custard_f16_" else "custard_bf16_"

let narrow_fw (o:prim_op) : option fwidth =
  match o.po_ty with
  | Some (PFloat Float16)  -> Some Float16
  | Some (PFloat BFloat16) -> Some BFloat16
  | _ -> None

let narrow_call (o:prim_op) : ML (option string) =
  match narrow_fw o with
  | None -> None
  | Some fw ->
    let pfx = if Float16? fw then "custard_f16_" else "custard_bf16_" in
    (match o.po_op with
     | Add | AddW   -> Some (pfx ^ "add")
     | Sub | SubW   -> Some (pfx ^ "sub")
     | Mult | MultW -> Some (pfx ^ "mul")
     | Div | DivW   -> Some (pfx ^ "div")
     | Eq  -> Some (pfx ^ "eq")
     | Neq -> Some (pfx ^ "neq")
     | Lt  -> Some (pfx ^ "lt")
     | Lte -> Some (pfx ^ "lte")
     | Gt  -> Some (pfx ^ "gt")
     | Gte -> Some (pfx ^ "gte")
     | _ -> None)

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
    let narrow = (match w with W8 -> true | W16 -> true | _ -> false) in
    if modular && narrow then "((" ^ int_type sw ^ ")" ^ s ^ ")" else s
  | Some (PFloat _) | None -> s

(* Section 115.  The cast {!truncate} adds is applied to the *result*, and at
   a width narrower than [int] that is too late.  Both operands of
   [U16.mul_mod] promote to [int] under 6.3.1.1, the multiplication is a
   *signed* one, and 65535 * 65535 overflows it -- undefined behaviour, which
   the cast that follows never sees.  A UBSan build says so; an optimizing
   one is entitled to assume it cannot happen.

   The fix is to do the arithmetic somewhere it is defined.  [unsigned int]
   is its own promotion, so casting the operands to it makes the operation
   unsigned, and unsigned arithmetic wraps by definition (6.2.5); the
   truncation back to the declared width then computes the same value modulo
   2^w that the F* operator does.

   Only the wrapping operators, and only where the promoted type is signed --
   an unsigned width at or above [int]'s is already unsigned, and a *signed*
   narrow width cannot overflow [int] at all (127 * 127 and 32767 * 32767
   both fit), so neither has anything to gain.  A shift is included: the left
   operand is the one whose promoted type the result takes, and casting the
   count as well is harmless. *)
let widen_operands (o:prim_op) : ML (option string) =
  let wrapping =
    match o.po_op with
    | AddW | SubW | MultW | BShiftL -> true
    | _ -> false in
  match o.po_ty with
  | Some (PInt (Unsigned, w)) when wrapping ->
    (match w with W8 | W16 -> Some "(unsigned int)" | _ -> None)
  | _ -> None

(* -------------------------------------------------------------------- *)
(* Expressions                                                          *)
(* -------------------------------------------------------------------- *)

(* Where the value of an expression goes once it has been computed. *)
type dest =
  | D_Return
  | D_Assign of string
  | D_Ignore

(* Binding strength of the emitted C, not of the source IR. Binary operators
   keep their existing enclosing parentheses in this first ladder. *)
type c_precedence =
  | CPostfix
  | CUnary
  | COpaque

type c_expression = {
  c_text: string;
  c_prec: c_precedence
}

let c_postfix (s:string) : c_expression = { c_text = s; c_prec = CPostfix }
let c_unary (s:string) : c_expression = { c_text = s; c_prec = CUnary }
let c_opaque (s:string) : c_expression = { c_text = s; c_prec = COpaque }

let postfix_text (d:c_expression) : string =
  match d.c_prec with
  | CPostfix -> d.c_text
  | CUnary | COpaque -> "(" ^ d.c_text ^ ")"

(* C's block scoping and the IR's do not line up: an [ELet] scopes its variable
   over its body only, while the statements this backend emits for a chain of
   them all land in one C block, and a loop's condition lands in the same block
   as the loop's body.  Two disjoint IR scopes can therefore collide in C --
   which is a compile error, not a wrong answer, but a confusing one.

   Rather than bracing everything (which would bury the output in nesting),
   the backend keeps its own scope: a name is emitted as written unless the
   enclosing *function* has already used it, in which case it takes a
   subscript.  So the generated C reads like the source, and a subscript in it
   means something real.  Global names are reserved too: a parameter must
   not shadow a function that [rename_let] has given that same spelling. *)
(* Each entry is the C expression a variable resolves to, and whether it is a
   one-cell stack allocation the backend has collapsed into a variable (see
   [ELet] below): a use that wants the cell reads or assigns it, a use that
   wants the pointer takes its address. *)
let scope : ref (list (string & (c_expression & bool))) = mk_ref []
let declared : ref (HashTable.t string bool) = mk_ref (HashTable.create 0)

let reset_scope () : ML unit =
  scope := []; declared := HashTable.create 20

let bind_gen (x:string) (cell:bool) : ML string =
  let base = c_var x in
  let rec pick (i:int) : ML string =
    let cand = if i = 0 then base else base ^ "_" ^ show i in
    if Some? (HashTable.try_find !declared cand) ||
       Some? (HashTable.try_find !taken_names cand)
    then pick (i + 1) else cand in
  let nm = pick 0 in
  HashTable.add !declared nm true;
  scope := (x, (c_postfix nm, cell)) :: !scope;
  nm

(* A pattern binding does not need a variable of its own: the value it names is
   already reachable, as a projection out of the scrutinee, and both are
   immutable.  Binding the *path* instead of declaring a copy is what turns
   [{ size_t sz_1 = s.sz; t = sz_1; }] into [t = s.sz;]. *)
let bind_var (x:string) : ML string = bind_gen x false

(* A one-cell stack allocation, collapsed into an ordinary variable. *)
let bind_cell (x:string) : ML string = bind_gen x true

let bind_alias (x:string) (path:c_expression) : ML unit =
  scope := (x, (path, false)) :: !scope

(* Section 19.3.  A name that no binder in the enclosing function introduced
   is a defect in the IR, not something to print and hope for.  The karamel
   backend catches it because its terms are De Bruijn and the conversion has
   to find an index; this backend prints names as names, and so used to emit
   the broken call silently -- an argument the callee does not take, naming a
   variable the caller does not have, which surfaces as a heap of unrelated
   gcc diagnostics about the function *after* it in the file.

   Every binder reaches [bind_var], [bind_cell] or [bind_alias] before its
   scope is printed, and [reset_scope] runs per definition, so a miss here is
   real.  Top-level names are [EQual] and never come through this. *)
let lookup_var_doc (x:string) : ML c_expression =
  match !scope |> List.tryFind (fun (y, _) -> y = x) with
  | Some (_, (nm, _)) -> nm
  | None ->
    reject_ir ("the unbound variable " ^ x)
      ["No binder in this definition introduces it.";
       "This is a compiler bug: please report it, with the definition named above."]

let lookup_var (x:string) : ML string = (lookup_var_doc x).c_text

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
  HashTable.add !declared nm true;
  nm

(* Section 121.2.  Everything in this module that outlives a single call and
   does not outlive a program, written down once.

   This backend keeps its tables in process-global mutable variables, which is
   fine as long as one process prints one program -- [Driver.run] is called
   once per process and calls [print_program] once.  What was not fine was
   that [print_program] reset thirteen of the twenty-two by hand and left nine
   alone, so "what is per-program" was an ad-hoc subset spelled out in the
   prologue of a 390-line function and nowhere else.  Being able to *read* the
   answer is the point; making a second program in one process work is a
   consequence.

   A table filled by a builder ([renames], [macros], [types] and friends) is
   assigned wholesale later in [print_program], so clearing it here is
   redundant -- and listed anyway, because the value of this function is that
   it is exhaustive.  The per-definition state at the end is reset again per
   definition, for the same reason. *)
let reset_program_state () : ML unit =
  current := "<toplevel>";
  HashTable.clear parents;
  HashTable.clear frozen_by;
  HashTable.clear frozen_by_target;
  HashTable.clear existentials;
  HashTable.clear root_decls;
  renames := HashTable.create 0;
  macros := HashTable.create 0;
  types := HashTable.create 0;
  ctors := HashTable.create 0;
  externs := HashTable.create 0;
  ifdefs := HashTable.create 0;
  keeps := HashTable.create 0;
  void_fns := HashTable.create 0;
  arities := HashTable.create 0;
  fn_sigs := HashTable.create 0;
  fn_globals := HashTable.create 0;
  ref_tys := [];
  iarr_tys := [];
  pbuf_tys := [];
  iarr_lists := [];
  any_tys := [];
  clo_queue := [];
  clo_seen := HashTable.create 0;
  arrow_ids := [];
  void_ret := false;
  eq_queue := [];
  eq_path := [];
  eq_seen := HashTable.create 20;
  string_lits := HashTable.create 20;
  string_lit_defs := [];
  int_lits := HashTable.create 20;
  boxed_tbl := HashTable.create 0;
  nonplain_tbl := HashTable.create 0;
  taken_names := HashTable.create 50;
  tail_groups := HashTable.create 0;
  scope := [];
  declared := HashTable.create 0;
  ctr := 0

(* Statement-shaped: a form that C has no expression for.  These are the
   forms [c_expr] has to hoist and [emit] compiles directly. *)
let is_stmt (e:expr) : bool =
  match e.e with
  | ELet _ | EMatch _ | EIf _ | ESeq _ | EWhile _ | EAbort _ | EUnreachable _ -> true
  (* An allocation needs an initializing loop, and the three that return no
     value need a statement to be a statement. *)
  | EOp ({ po_op = BufCreate _ }, _) | EOp ({ po_op = BufWrite }, _)
  | EOp ({ po_op = BufBlit }, _) | EOp ({ po_op = BufFree }, _)
  | EOp ({ po_op = RcInc }, _) | EOp ({ po_op = RcDec }, _)
  | EOp ({ po_op = RefSet }, _)
  | EOp ({ po_op = Reset _ }, _) | EOp ({ po_op = ResetFree }, _)
  | EOp ({ po_op = Update _ }, _)
  | EOp ({ po_op = ExnRaise }, _) | EOp ({ po_op = ExnExit }, _) -> true
  | EOp ({ po_op = PBuf f }, _) -> f <> "read" && f <> "alloc"
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
  | EConst _ | EQual _ | EAny | EAbort _ | EUnreachable _ -> []
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
  | EConst _ | EQual _ | EAny | EAbort _ | EUnreachable _ -> false
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
  (* Cherry: a field of a counted value is read out, because the value it is
     read from may be released before the field is used. *)
  | EProj (a, _, _) -> is_stable a && not (is_nonplain_ty a.ty)
  | _ -> false

(* Section 70.2.  An expression that names an object, so that a reference can
   be bound to it.  A call is excluded and has to be: [T &x = f();] does not
   bind a non-const reference to a temporary, and the whole point of the
   reference is that it aliases something that outlives the binding. *)
let rec is_lvalue (e:expr) : ML bool =
  match e.e with
  | EVar _ | EQual _ -> true
  | EOp ({ po_op = BufRead }, [_; _]) -> true
  | EProj (a, _, _) -> is_lvalue a
  | _ -> false

(* No calls, no writes, no loops: an expression that can be moved anywhere
   without changing what the program does. *)
let rec is_pure (e:expr) : ML bool =
  let all (es:list expr) : ML bool = List.for_all is_pure es in
  match e.e with
  | EConst _ | EVar _ | EQual _ | EAny -> true
  | EApp _ | EFun _ | EWhile _ | EAbort _ | EUnreachable _ | ERaise _ | ETry _ -> false
  | EOp ({ po_op = BufRead }, es) -> all es
  | EOp ({ po_op = BufCreate _ }, _) | EOp ({ po_op = BufWrite }, _)
  | EOp ({ po_op = BufFree }, _) | EOp ({ po_op = BufBlit }, _)
  | EOp ({ po_op = RcInc }, _) | EOp ({ po_op = RcDec }, _)
  | EOp ({ po_op = RefNew }, _) | EOp ({ po_op = RefGet }, _) | EOp ({ po_op = RefSet }, _)
  | EOp ({ po_op = Reset _ }, _) | EOp ({ po_op = Reuse _ }, _) | EOp ({ po_op = ResetFree }, _)
  | EOp ({ po_op = Update _ }, _)
  | EOp ({ po_op = IArr _ }, _) | EOp ({ po_op = Dyn _ }, _) | EOp ({ po_op = PBuf _ }, _)
  | EOp ({ po_op = ExnRaise }, _) | EOp ({ po_op = ExnPending }, _)
  | EOp ({ po_op = ExnTake }, _) | EOp ({ po_op = ExnExit }, _) -> false
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
  | EConst _ | EQual _ | EAny | EAbort _ | EUnreachable _ -> true
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
    | EConst _ | EVar _ | EQual _ | EAny | EAbort _ | EUnreachable _ -> e.e
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
(* Section 94.  The number of cells past which a repeated non-zero fill is
   written as a loop rather than as an initializer list.  A round number and
   not a measured one: the list is one token per cell, so the point is only to
   keep a large array from turning into a large amount of text, and anything
   in this neighbourhood does that. *)
let init_list_max : int = 64

let is_one (e:expr) : bool =
  match e.e with EConst (CInt (1, _, _)) -> true | _ -> false

(* A constructor's field names, paired with the printed arguments.  A length
   mismatch would be an extractor bug; keeping the prefix produces a C error
   at the literal rather than a crash here. *)
let rec zip_fields (fs : list (string & cty)) (vs : list string) : list (string & string) =
  match fs, vs with
  | (f, _) :: fs, v :: vs -> (f, v) :: zip_fields fs vs
  | _ -> []

(* An abstract type with no C representation can carry raw macro tokens, such
   as [float] in a type-taking macro.  Those are not runtime expressions. *)
let rec is_foreign_token (t:cty) : ML bool =
  match t with
  | TApp (n, _) when None? (builtin_type n) ->
    (match find_type n with
     | Some d when List.existsb Extern? d.dt_flags -> false
     | Some { dt_body = TAbstract } -> true
     | Some { dt_body = TAbbrev t } -> is_foreign_token t
     | _ -> false)
  | _ -> false

let rec c_expr (out:ref string) (ind:string) (e:expr) : ML string =
  (c_expr_doc out ind e).c_text

and c_expr_doc (out:ref string) (ind:string) (e:expr) : ML c_expression =
  if is_stmt e then hoist out ind e
  else match e.e with
  | EConst c ->
    (match c with
     | CFloat _ -> c_opaque (constant c)
     | _ -> c_postfix (constant c))
  (* Every other use of a collapsed cell wants the pointer -- passing it to a
     function expecting a [ref], say -- and C can produce one on demand. *)
  | EVar x ->
    if is_cell x then c_unary ("&" ^ lookup_var x) else lookup_var_doc x
  | EAny ->
    (* What an uninitialized stack slot holds.  A zero of the right type is a
       legal value of it and is what C would give a static. *)
    c_postfix ("(" ^ ty e.ty ^ "){0}")
  (* A definition as a value is its static closure. *)
  | EQual (n, _) when Options.custard_cherry () && Some? (fn_sig n) ->
    clo_request (ReqPap (n, 0, e.ty));
    c_postfix ("((cherry_fn)&" ^ static_clo_name n ^ ")")
  | EQual (n, _) when Some? (HashTable.try_find !ifdefs (string_of_name n)) ->
    E.raise_error0 E.Error_CustardBadIfDef [
      text ("Custard: " ^ string_of_name n ^ " is a [@@custard_c_ifdef] flag, \
             used as a value in " ^ !current ^ ".");
      text "Its value is a preprocessor condition, which C has only in [#if]: \
            the only use allowed is as the whole condition of an [if].  Write \
            [if flag then ... else ...] and compute anything else inside the \
            branches." ]
  | EQual (n, _) ->
    (match HashTable.try_find !externs (string_of_name n) with
     (* A foreign name may expand to an expression rather than one C token. *)
     | Some t -> if is_foreign_token e.ty then c_opaque t else c_postfix (group t)
     | None -> c_postfix (c_name n))
  | EApp (hd, args) when is_closure_app hd args ->
    let k = List.length args in
    let eargs = args in
    let args = args |> List.filter (fun (a:expr) -> not (TUnit? a.ty))
                    |> List.map (fun (a:expr) -> c_rvalue out ind a.ty a) in
    (match hd.e with
     | EQual (n, _) when Some? (fn_sig n) ->
       clo_request (ReqPap (n, k, e.ty));
       c_postfix (pap_name n k ^ "(" ^ String.concat ", " args ^ ")")
     | _ ->
       let f = c_expr out ind hd in
       let ht =
         match hd.e with
         | EQual (n, _) ->
           (match HashTable.try_find !fn_globals (string_of_name n) with
            | Some t -> t
            | None -> hd.ty)
         | _ -> hd.ty in
       (* The arrow's domains these arguments fill: an argument for a unit
           parameter may have been dropped already. *)
       let rec consume (t:cty) (xs:list cty) : ML int =
         match xs, arrow_view t with
         | [], _ -> 0
         | x :: rest, Some (d, b) ->
           if TUnit? d && not (TUnit? x) then 1 + consume b xs
           else if TUnit? x && not (TUnit? d) then consume t rest
           else 1 + consume b rest
         | x :: rest, None -> if TUnit? x then consume t rest else List.length xs in
       let k = consume ht (List.map (fun (a:expr) -> a.ty) eargs) in
       clo_request (ReqApply (ht, k));
       c_postfix (apply_name ht k ^ "(" ^ String.concat ", " (f :: args) ^ ")"))
  | EApp (hd, args) ->
    (* Drop the arguments that correspond to dropped parameters.  ANF has made
       every operand pure, so nothing is lost by not evaluating them. *)
    (* Section 53.1.  Through a *variable* of function-pointer type there is
       no name to look up, but there is no need for one: the parameter is
       dropped exactly when its type is [unit], so the argument is dropped
       exactly when its type is, and both ends read the same arrow. *)
    let args =
      match hd.e with
      | EQual (n, _) ->
        (match HashTable.try_find !keeps (string_of_name n) with
         | Some flags -> filter_by flags args
         | None -> args)
      | _ -> args |> List.filter (fun (a:expr) -> not (TUnit? a.ty)) in
    (* Before printing, because a mismatch here is not something the C
       compiler will describe in terms the reader can act on: it reports "too
       few arguments" against a generated prototype. *)
    (match hd.e with
     | EQual (n, _) ->
       (match HashTable.try_find !arities (string_of_name n) with
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
    (* Section 59.5.  An argument is converted to the parameter type as if by
       assignment, so a literal argument's cast is redundant -- but only
       where a prototype says what that type is.  For a call this backend
       generates one, and for a call through a function pointer the pointer's
       type is the prototype.  **An extern is the exception and keeps its
       casts**: its declaration is in a header this backend does not write,
       and it may not be a function at all.  Kuiper's shared-memory
       primitives are macros, where nothing is converted because nothing is
       passed -- the token is substituted, and [sizeof] or a concatenation
       inside the macro would see a different thing. *)
    let cast_free_args =
      match hd.e with
      | EQual (n, _) -> None? (HashTable.try_find !externs (string_of_name n))
      | _ -> true in
    (* The head names the function, which is not the same as using it as a
       value: under Cherry that is a closure. *)
    let head =
      match hd.e with
      | EQual (n, _) ->
        (match HashTable.try_find !externs (string_of_name n) with
         | Some t -> t
         | None -> c_name n)
      | _ -> postfix_text (c_expr_doc out ind hd) in
    let call = head ^ "(" ^
               String.concat ", "
                 (args |> List.map (fun (a:expr) ->
                    if cast_free_args then c_rvalue out ind a.ty a
                    else c_expr out ind a)) ^ ")" in
    (* Section 57.1.  An extern returning a pointer is cast to its declared
       type at the call site.  In C the cast is a no-op -- a [void *] converts
       to any object pointer implicitly, which is why this was invisible --
       but **CUDA is C++**, where that conversion is a hard error, and
       Kuiper's shared-memory primitive is exactly the shape: a macro
       expanding to a [void] pointer, assigned to a [uint8_t] pointer.
       Custard cannot know a macro's own C type and has to trust the
       declaration -- but it *knows* the declared type, so it can spell it,
       and karamel already does.  The generated header emits
       [extern "C"] guards, so a C++ consumer is an intended use.

       Only a pointer result and only an extern: a cast on an ordinary call
       is noise, and Custard's own definitions are already spelled with the
       type the call site expects.  Both pointer spellings -- [TBuf] and
       [TRef], which print alike -- since covering one and not the other is
       the mistake these rounds keep turning up. *)
    let call =
      match hd.e with
      | EQual (n, _) when Some? (HashTable.try_find !externs (string_of_name n))
                          && None? (HashTable.try_find !void_fns (string_of_name n)) ->
        (* Group the expansion, not the head: function-like macros must still
           be invoked, and a pointer cast must cover their whole result. *)
        if is_foreign_token e.ty then c_opaque call else
        let call = "(" ^ call ^ ")" in
        if TBuf? e.ty || TRef? e.ty
        then c_unary ("(" ^ ty e.ty ^ ")" ^ call)
        else c_postfix call
      | _ -> c_postfix call in
    (* A [void] call is a statement, not an operand.  It runs here and stands
       for the unit value, which is what the caller was going to do with it. *)
    (match hd.e with
     | EQual (n, _) when Some? (HashTable.try_find !void_fns (string_of_name n)) ->
       out := !out ^ ind ^ call.c_text ^ ";\n"; c_postfix unit_value
     | _ -> call)
  (* Both nodes are a C cast, but for opposite reasons: a conversion is what
     the cast *does*, and a coercion is a reinterpretation the C type system
     needs told about and the generated code does not act on. *)
  (* Section 59.  A cast converts whatever it is given, so a literal
     operand's own cast is subsumed by this one. *)
  | ECast (e1, t) ->
    (match e1.ty, t with
     | TInt a, TInt b when a = b -> c_expr_doc out ind e1
     (* Cherry: [Prims.int] is a tagged pointer, not a number. *)
     (* Through the 64-bit conversions, or the 128-bit ones for a 128-bit
        integer, which would otherwise be truncated. *)
     | _, TInt (sg, w) when Options.custard_cherry () && is_int_ty e1.ty ->
       let bits = if w = W128 then "128(" else "64(" in
       c_unary ("(" ^ ty t ^ ")cherry_int_to_" ^ (if Signed? sg then "i" else "u") ^ bits ^
       c_expr out ind e1 ^ ")")
     | TInt (sg, w), _ when Options.custard_cherry () && is_int_ty t ->
       let bits = if w = W128 then "128" else "64" in
       c_postfix ((if Signed? sg then "cherry_int_of_i" ^ bits ^ "((" ^ (if w = W128 then "cherry_i128" else "int64_t") ^ ")"
        else "cherry_int_of_u" ^ bits ^ "((" ^ (if w = W128 then "cherry_u128" else "uint64_t") ^ ")") ^
       c_rvalue out ind e1.ty e1 ^ ")")
     (* Section 66.  A struct is not castable, so a conversion at a narrow
        width is a call.  Both directions, and between the two narrow formats
        via [float], which is exact for either of them and so rounds once --
        the only rounding is the final encode. *)
     | _, TFloat fw when narrow_ty fw ->
       c_opaque (narrow_pfx fw ^ (match e1.ty with
                        | TInt (_, _) -> "of_i64((int64_t)"
                        | TFloat Float64 -> "of_f64("
                        | _ -> "of_f32(") ^
       c_rvalue out ind e1.ty e1 ^ ")")
     | TFloat fw, _ when narrow_ty fw ->
       c_unary ("(" ^ ty t ^ ")" ^ narrow_pfx fw ^ "to_f32(" ^ c_expr out ind e1 ^ ")")
     | _ -> c_unary ("(" ^ ty t ^ ")" ^ c_rvalue out ind e1.ty e1))
  | ECoerce (e1, t) ->
    if e1.ty = t then c_expr_doc out ind e1
    (* Under Cherry a [TAny] is a [dyn], whose value carries its type
       information: only [Dyn] nodes make or read one, and a cast cannot. *)
    else if Options.custard_cherry () && (mentions_any e1.ty || mentions_any t)
    then reject ("a coercion from " ^ show e1.ty ^ " to " ^ show t)
           ["Under Cherry the unknown representation is FStar.Dyn.dyn, \
             which only mkdyn and undyn convert to and from."]
    else c_unary ("(" ^ ty t ^ ")" ^ c_expr out ind e1)
  | EProj (e1, _, f) ->
    c_postfix (proj (postfix_text (c_expr_doc out ind e1)) e1.ty f)
  | EDiscrim (e1, cn) ->
    (match find_ctor cn with
     | Some (d, _) -> c_postfix (if single_ctor d then "true"
                      else "(" ^ tag_of (postfix_text (c_expr_doc out ind e1)) d ^ " == " ^ c_tag cn ^ ")")
     | None -> reject ("the constructor " ^ string_of_name cn)
                 ["It belongs to no type declaration in the program."])
  | ECtor (cn, args) -> c_postfix (ctor_lit out ind e.ty cn args)
  | ERecord (_, fs) ->
    c_postfix ("(" ^ ty e.ty ^ "){ " ^
    String.concat ", " (fs |> List.map (fun (f, v) ->
      "." ^ c_var f ^ " = " ^ c_rvalue out ind v.ty v)) ^ " }")
  | EOp ({ po_op = RefNew }, [v]) ->
    let v' = c_rvalue out ind v.ty v in
    c_postfix (rc_fn "new" e.ty ^ "(" ^ v' ^ ")")
  | EOp ({ po_op = RefGet }, [r]) ->
    c_postfix (rc_fn "get" r.ty ^ "(" ^ c_expr out ind r ^ ")")
  | EOp ({ po_op = ExnPending }, []) -> c_opaque "CHERRY_EXN_PENDING()"
  | EOp ({ po_op = ExnTake }, []) -> c_postfix "cherry_exn_take()"
  | EOp ({ po_op = Dyn f }, [a]) ->
    let t = if f = "mk" then a.ty else e.ty in
    c_postfix (any_prefix t ^ "_" ^ f ^ "(" ^ c_rvalue out ind a.ty a ^ ")")
  | EOp ({ po_op = PBuf f }, args) ->
    c_postfix (pbuf_call out ind f args)
  | EOp ({ po_op = IArr f }, args) ->
    let elt (t:cty) : ML cty =
      match t with
      | TApp ({ ns = ["FStar"; "ImmutableArray"; "Base"]; id = "t" }, [v]) -> v
      | _ -> failwith "Cherry: an immutable array operation on something else" in
    let vals = args |> List.map (fun a -> c_rvalue out ind a.ty a) in
    let call (p:string) : string = p ^ "_" ^ f ^ "(" ^ String.concat ", " vals ^ ")" in
    c_postfix (match f, args with
     | "length", _ -> "cherry_iarray_length(" ^ String.concat ", " vals ^ ")"
     | "of_list", [l] -> let v = elt e.ty in iarr_list v l.ty; call (iarr_prefix v)
     | "to_list", [a] -> let v = elt a.ty in iarr_list v e.ty; call (iarr_prefix v)
     | _, a :: _ -> call (iarr_prefix (elt a.ty))
     | _ -> failwith "Cherry: an immutable array operation without operands")
  | EOp ({ po_op = Reuse (old, cn) }, w :: args) ->
    c_postfix (match find_ctor old, find_ctor cn with
     | Some (d0, _), Some (d, _) ->
       let w' = c_expr out ind w in
       let vals = args |> List.map (fun a -> c_rvalue out ind a.ty a) in
       "cherry_reuse_" ^ c_name d.dt_name ^ "_" ^ arm_name cn ^ "(" ^
       String.concat ", " (w' :: ("sizeof(" ^ cell_struct d0 old ^ ")") :: vals) ^ ")"
     | _ -> failwith "Cherry: reuse of an unknown constructor")
  | EOp ({ po_op = BufRead }, [b; i]) ->
    c_subscript out ind b i
  | EOp ({ po_op = BufSub }, [b; i]) ->
    c_postfix ("(" ^ c_expr out ind b ^ " + " ^ c_rvalue out ind i.ty i ^ ")")
  | EOp ({ po_op = BufNull }, []) -> c_unary ("(" ^ ty e.ty ^ ")NULL")
  | EOp ({ po_op = BufIsNull }, [b]) -> c_postfix ("(" ^ c_expr out ind b ^ " == NULL)")
  (* Section 71.  The object a [BufLit] declared is [const], so a pointer to
     it is a [const T *] and the array type Pulse gives back is a [T *].
     Writing through the result would be undefined, and what rules that out
     is the post-condition of [array_of_static_array], which hands out a
     fractional permission and never a full one.

     Spelled out rather than left implicit because C would not merely warn
     here, it would refuse: assigning a [const T *] to a [T *] discards a
     qualifier, and a C++ consumer -- section 70.2 puts one in reach -- makes
     that a hard error. *)
  | EOp ({ po_op = BufUnconst }, [b]) ->
    c_unary ("(" ^ ty e.ty ^ ")" ^ c_expr out ind b)
  (* Section 120.  A comment around an expression.  The standalone form has
     no expression to wrap, and a [()] is not one either: it is emitted for
     its effect into [out] and the value is the unit constant, exactly as an
     impure unit-typed node in an expression position is anywhere else. *)
  | EOp ({ po_op = Commented (before, "") }, [{ e = EConst CUnit }]) ->
    out := !out ^ ind ^ "/* " ^ before ^ " */\n";
    c_postfix unit_value
  | EOp ({ po_op = Commented (before, after) }, [b]) ->
    let body = c_rvalue_doc out ind e.ty b in
    { body with c_text = "/* " ^ before ^ " */ " ^ body.c_text ^ " /* " ^ after ^ " */" }
  (* Section 71.  A braced initializer is not an expression in C: it may only
     appear where an object is being declared, which for Custard means the
     body of a global.  {!global_decl} takes it there, so reaching here means
     the value escaped into a computation. *)
  | EOp ({ po_op = BufLit }, _) ->
    E.raise_error0 E.Error_CustardBadStaticArray [
      text ("Custard: " ^ !current ^ " uses a static array where C needs an \
             expression.");
      text "A Pulse.Lib.GlobalArray.static_array is a braced initializer, and \
            C accepts one of those only in a declaration -- so it can be the \
            body of a top-level definition and nothing else.";
      text "Bind it to a top-level definition and use that name here."]
  (* Section 44.2.  The same comparison in expression position.  [strcmp] is
     declared by the <string.h> the header already includes. *)
  | EOp (o, [a; b]) when (Eq? o.po_op || Neq? o.po_op) && is_string_ty a.ty &&
                         not (Options.custard_cherry ()) ->
    c_postfix ("(strcmp(" ^ c_expr out ind a ^ ", " ^ c_expr out ind b ^ ") " ^
    (if Eq? o.po_op then "==" else "!=") ^ " 0)")
  (* Cherry: the runtime compares by contents. *)
  | EOp (o, [a; b]) when (Eq? o.po_op || Neq? o.po_op) &&
                         Some? (content_eq a.ty "" "") ->
    let c = (match content_eq a.ty (c_expr out ind a) (c_expr out ind b) with
             | Some c -> c | None -> "") in
    c_postfix ("(" ^ (if Neq? o.po_op then "!(" ^ c ^ ")" else c) ^ ")")
  (* Section 107.  The same question at every other type C cannot compare
     with [==]: a struct, which is what a record, a tuple and every inductive
     with a payload are here.  Only for the polymorphic [=]: an operator at a
     machine type compares at that type whatever its operands' IR types say,
     which under Cherry may be [TAny] (issue 4715). *)
  | EOp (o, [a; b]) when (Eq? o.po_op || Neq? o.po_op) && None? o.po_ty &&
                         Some? (eq_fn_of a.ty) ->
    let g = (match eq_fn_of a.ty with Some g -> g | None -> "") in
    c_postfix ("(" ^ (if Neq? o.po_op then "!" else "") ^
    g ^ "(" ^ c_expr out ind a ^ ", " ^ c_expr out ind b ^ "))")
  (* Section 59.3.  A binary operator's two operands have the same IR type,
     so a literal operand's cast is telling C what the *other* operand
     already says: if that type outranks [int] the literal converts to it
     under the usual arithmetic conversions, and if it does not, both sides
     promote to [int] exactly as they did with the casts -- which is why
     {!truncate} is here and is unchanged.

     The condition is that the *other* operand is not itself a literal.
     Two literals would leave nothing carrying the type, and the operator
     would be evaluated at [int]; that is the one case where dropping the
     casts could change a result. *)
  (* Section 66.  Before the infix case, which would otherwise emit [+] on a
     struct.  No {!truncate}: that is about C's integer promotions, and these
     are neither integers nor promoted. *)
  | EOp (o, [a; b]) when Some? (narrow_call o) ->
    c_opaque (Some?.v (narrow_call o) ^ "(" ^ c_rvalue out ind a.ty a ^ ", " ^
                                    c_rvalue out ind b.ty b ^ ")")
  (* Section 115.  [&&] and [||] do not evaluate their right operand unless
     the left one fails to decide, and that is not a convenience: F* code
     relies on it, as [x <> 0 && 100 / x > 5] does.  Every other operand
     position may have its statements hoisted ahead of the expression,
     because every other operand is evaluated -- but hoisting *this* one
     evaluates it unconditionally, and the division whose guard was just
     written runs anyway.  The IR is no help: by the time it arrives the
     guard is an [EIf], and an [EIf] in an operand is exactly what {!hoist}
     is for.

     So the right operand is printed into a buffer of its own.  If nothing
     lands there, the operand is an expression and the plain infix form is
     both correct and what a reader expects.  If something does, the operator
     becomes what it always meant: a temporary holding the left operand, and
     a branch that overwrites it with the right one only on the path where C
     would have evaluated it.

     Bitwise [And]/[Or] at a width ({!at_int_width}) are a different
     operator, evaluate both operands, and fall through to the case below. *)
  | EOp (o, [a; b]) when (And? o.po_op || Or? o.po_op) && not (at_int_width o) ->
    let av = c_expr out ind a in
    let bout = mk_ref "" in
    let bv = c_expr bout (ind ^ "  ") b in
    if !bout = "" then
      c_postfix ("(" ^ av ^ " " ^ Some?.v (infix_op o) ^ " " ^ bv ^ ")")
    else begin
      let x = fresh "sc" in
      out := !out ^ ind ^ decl_of e.ty x ^ " = " ^ av ^ ";\n" ^
             ind ^ "if (" ^ (if Or? o.po_op then "!" else "") ^ x ^ ") {\n" ^
             !bout ^
             ind ^ "  " ^ x ^ " = " ^ bv ^ ";\n" ^
             ind ^ "}\n";
      c_postfix x
    end
  | EOp (o, [a; b]) when Some? (infix_op o) ->
    (* Section 61.1.  A shift is the exception, and it is the one binary
       operator whose operands genuinely do *not* share an IR type --
       [U64.shift_left] takes a [U32.t] amount.  6.5.7 promotes the two
       operands *separately* and gives the result the promoted type of the
       **left** one, so the usual arithmetic conversions never run and the
       right operand says nothing about the result.  A literal left
       operand's cast is then the only thing carrying the width, and
       without it [40 << n] is computed at [int] however wide the target
       is: at 64 bits a wrong value, at 32 bits undefined behaviour, and
       under [-Wall -Wextra] not a single diagnostic.  {!truncate} does not
       cover it, because it re-casts only at [Int8]/[Int16], where both
       operands promote to [int] anyway.

       The right operand keeps the benefit: its type provably cannot reach
       the result. *)
    let shift = BShiftL? o.po_op || BShiftR? o.po_op in
    let av = if shift || EConst? b.e then c_expr out ind a
             else c_rvalue out ind a.ty a in
    let bv = if (not shift) && EConst? a.e then c_expr out ind b
             else c_rvalue out ind b.ty b in
    (* Section 115.  After the two operands are printed and before they meet
       the operator, so that the operation itself happens at a type it is
       defined at. *)
    let wrap (s:string) : ML string =
      match widen_operands o with
      | Some c -> c ^ group s
      | None -> s in
    c_postfix (truncate o ("(" ^ wrap av ^ " " ^ Some?.v (infix_op o) ^ " " ^ wrap bv ^ ")"))
  (* Section 61.2.  Through {!group}, like the [!] of a condition: this site
     printed its operand bare, so a macro extern was unparenthesized here
     whatever {!is_atom} said.  That half is older than section 59 -- the two
     [!] sites simply disagreed, and only the condition one was written to
     the rule that {!negate}'s comment states. *)
  | EOp (o, [a]) when Some? (prefix_op o) ->
    c_postfix (truncate o ("(" ^ Some?.v (prefix_op o) ^ group (c_expr out ind a) ^ ")"))
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
and hoist (out:ref string) (ind:string) (e:expr) : ML c_expression =
  if TUnit? e.ty then (out := !out ^ emit ind D_Ignore e; c_postfix unit_value) else
  let x = fresh "t" in
  let body = emit ind (D_Assign x) e in
  (* If the whole thing came out as a single assignment to the temporary, and
     evaluating it does nothing, then the temporary was only ever going to hold
     the right-hand side: use that instead.  This is what turns a record
     projection -- which reaches the backend as a one-branch match -- back into
     the projection it was. *)
  match String.split ['\n'] body with
  | [l; ""] when is_pure e && starts_with l (ind ^ x ^ " = ") ->
    c_opaque (String.substring l (String.length ind + String.length x + 3)
                     (String.length l - String.length ind - String.length x - 4))
  | _ -> out := !out ^ ind ^ decl_of e.ty x ^ ";\n" ^ body; c_postfix x

(* The C spelling of field [f] of a value of type [t].  A single-constructor
   variant is a plain struct, so its fields are reached directly; a record's
   always are. *)
and proj (v:string) (t:cty) (f:string) : ML string =
  match t with
  | TApp (n, _) ->
    (match find_type n with
     | Some d when is_boxed d && TVariant? d.dt_body ->
       let cs = (match d.dt_body with TVariant cs -> cs | _ -> []) in
       (match cs |> List.tryFind (fun (_, fs) ->
                      fs |> List.existsb (fun (g, _) -> g = f)) with
        | Some (cn, _) ->
          (* F* has checked that the value was built by [cn]; debug mode
             checks it again (cherry.h). *)
          let v = if List.length cs > 1
                  then "CHERRY_TAGGED(" ^ v ^ ", " ^ c_tag cn ^ ", " ^
                       debug_what ("projector " ^ f ^ " on another constructor") ^ ")"
                  else v in
          cell_field v d cn f
        | None -> reject ("the field " ^ f) ["No constructor declares it."])
     | Some d when single_ctor d -> v ^ "." ^ c_var f
     | Some ({ dt_body = TRecord _ }) -> v ^ "." ^ c_var f
     | Some ({ dt_body = TAbbrev c }) -> proj v c f
     | Some d ->
       (* A projector on a multi-constructor variant: F* only generates one
          when the field is unambiguous, so the case is determined by the
          field name. *)
       (match d.dt_body with
        | TVariant cs ->
          (match cs |> List.tryFind (fun (_, fs) ->
                         fs |> List.existsb (fun (g, _) -> g = f)) with
           | Some (cn, cfs) ->
             let v = if Options.custard_cherry ()
                     then "CHERRY_TAGGED_U(" ^ v ^ ", " ^ c_tag cn ^ ", " ^
                          debug_what ("projector " ^ f ^ " on another constructor") ^ ")"
                     else v in
             v ^ arm_sel cn cfs f
           | None -> reject ("the field " ^ f) ["No constructor declares it."])
        | _ -> reject ("the field " ^ f) [])
     | None -> reject ("a projection out of " ^ string_of_name n)
                 ["The type has no declaration in the program."])
  | _ -> reject ("the field " ^ f) ["Its owner is not a declared type."]

and tag_of (v:string) (d:dtype) : ML string =
  if is_boxed d then "cherry_tag(" ^ v ^ ")"
  else if is_enum d then v else v ^ ".tag"

(* A constructor application.  Three shapes, and each is the natural C for the
   layout its type got: an enum constant, a struct literal, a tagged union
   literal. *)
(* An expression in a position that converts it to [target]: only an
   integer literal is printed differently there, and only by losing a cast
   {!converted_int} explains is redundant.  Everything else goes through
   {!c_expr} unchanged. *)
and c_rvalue (out:ref string) (ind:string) (target:cty) (e:expr) : ML string =
  (c_rvalue_doc out ind target e).c_text

and c_rvalue_doc (out:ref string) (ind:string) (target:cty) (e:expr) : ML c_expression =
  match e.e with
  | EConst c ->
    (match converted_int target e.ty c with
     | Some s -> c_opaque s
     | None -> c_expr_doc out ind e)
  | _ -> c_expr_doc out ind e

and c_subscript (out:ref string) (ind:string) (b:expr) (i:expr) : ML c_expression =
  match b.e with
  | EVar y when is_cell y -> lookup_var_doc y
  | _ ->
    let base = postfix_text (c_expr_doc out ind b) in
    c_postfix (base ^ "[" ^ c_rvalue out ind i.ty i ^ "]")

(* Cherry: a call of a Pulse container helper ([PBuf]).  The first operand
   is the container, except in an allocation. *)
and pbuf_call (out:ref string) (ind:string) (f:string) (args:list expr) : ML string =
  let a = (match args with a :: _ -> a | [] -> failwith "Cherry: a Pulse container operation without operands") in
  let t = if f = "alloc" then a.ty else
          (match a.ty with
           | TRef (RManual, u) | TBuf u -> u
           | _ -> failwith "Cherry: a Pulse container operation on something else") in
  let vals = args |> List.map (fun a -> c_rvalue out ind a.ty a) in
  pbuf_prefix t ^ "_" ^ f ^ "(" ^ String.concat ", " vals ^ ")"

and ctor_lit (out:ref string) (ind:string) (t:cty) (cn:name) (args:list expr) : ML string =
  match find_exn cn with
  | Some _ ->
    exn_new cn ^ "(" ^ String.concat ", " (args |> List.map (fun a -> c_rvalue out ind a.ty a)) ^ ")"
  | None ->
  match find_ctor cn with
  | None -> reject ("the constructor " ^ string_of_name cn)
              ["It belongs to no type declaration in the program."]
  | Some (d, fields) ->
    let vals = args |> List.map (fun a -> c_rvalue out ind a.ty a) in
    let named = zip_fields fields vals in
    if is_boxed d then
      (if Nil? fields then "CHERRY_SCALAR(" ^ c_tag cn ^ ")"
       else cell_new d cn ^ "(" ^ String.concat ", " vals ^ ")")
    else if is_enum d then c_tag cn
    else if single_ctor d then
      "(" ^ c_name d.dt_name ^ "){ " ^
      String.concat ", " (named |> List.map (fun (f, v) -> "." ^ c_var f ^ " = " ^ v)) ^ " }"
    else if Nil? fields then
      "(" ^ c_name d.dt_name ^ "){ .tag = " ^ c_tag cn ^ " }"
    else
      "(" ^ c_name d.dt_name ^ "){ .tag = " ^ c_tag cn ^ ", .val = { ." ^
      arm_name cn ^ " = " ^
      (if arm_flat fields then snd (List.hd named)
       else "{ " ^
            String.concat ", " (named |> List.map (fun (f, v) ->
              "." ^ c_var f ^ " = " ^ v)) ^ " }") ^
      " } }"

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
    if s = unit_value then "" else ind ^ "(void)" ^ group s ^ ";\n"
  | D_Return -> ind ^ "return " ^ s ^ ";\n"
  | D_Assign x -> ind ^ x ^ " = " ^ s ^ ";\n"
  (* The value is computed for its effect; the cast silences the warning that
     it is unused.  A unit constant computes nothing, so it needs neither. *)
  | D_Ignore ->
    if s = unit_value then "" else ind ^ "(void)" ^ group s ^ ";\n"

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
    bind_alias x (c_postfix unit_value);
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
    bind_alias x (lookup_var_doc y);
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
    let path = c_expr_doc out ind e1 in
    let saved = !scope in
    bind_alias x path;
    let s2 = emit ind d e2 in
    scope := saved;
    !out ^ s2

  (* Section 19.8: written, never read.  The writes go with the cell. *)
  | ELet (x, TRef (RManual, t), { e = EOp ({ po_op = BufCreate LStack }, [init; len]) }, e2)
  | ELet (x, TBuf t, { e = EOp ({ po_op = BufCreate LStack }, [init; len]) }, e2)
      when is_one len && is_droppable init && cell_dead x e2 ->
    emit ind d (drop_writes x e2)

  | ELet (x, TRef (RManual, t), { e = EOp ({ po_op = BufCreate LStack }, [init; len]) }, e2)
  | ELet (x, TBuf t, { e = EOp ({ po_op = BufCreate LStack }, [init; len]) }, e2)
      when is_one len ->
    let out = mk_ref "" in
    let iv = c_rvalue out ind t init in
    let saved = !scope in
    let nm = bind_cell x in
    let s2 = emit ind d e2 in
    scope := saved;
    (* Section 94.5.  A cell whose fill is [EAny] is a declaration and nothing
       else: the arbitrary value the fill asks for is the one the slot has
       before anything is written to it.  Pulse only hands out [pts_to_uninit]
       for these, so a read is not reachable until a write has happened. *)
    !out ^ ind ^ decl_of t nm ^
    (if EAny? init.e then "" else " = " ^ iv) ^ ";\n" ^ s2

  (* Section 97.  [let mut a = alloc v n] used to declare a pointer, allocate
     into a second name, and assign one to the other.  The second name is not
     worth a variable: an array *is* an address, so the binding and the
     storage are one declaration and [a] can name the storage directly.
     Every use decays, which is what [a] was being assigned to a pointer for
     in the first place.

     The one-cell [LStack] cases above have already run, and this must not
     take them: their binding is a *cell* and a use of it takes an address,
     which is a different thing from an array that is one.  A heap allocation
     is in scope, though -- it declares its own pointer and had the same
     spare variable in front of it. *)
  | ELet (x, TBuf t, { e = EOp ({ po_op = BufCreate lt }, [init; len]) }, e2)
      when not (LStack? lt && is_one len) ->
    let saved = !scope in
    (* Bound before the allocation is emitted, so that the name is chosen
       against the names already used; emitted under the *outer* scope, since
       the IR scopes [x] over [e2] only and [init] or [len] may mention a
       different variable that C spells the same way. *)
    let nm = bind_var x in
    let s1 =
      let saved' = !scope in
      scope := saved;
      let s = emit_alloc ind D_Ignore (Some nm) lt (TBuf t) init len in
      scope := saved'; s in
    let s2 = emit ind d e2 in
    scope := saved;
    s1 ^ s2

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
            let v = c_rvalue out ind t e1 in
            let x = bind_var x in
            (* Section 70.2.  A handle type binds by reference, so that the
               alias the F* model describes is the alias the C++ has.  Only
               from an lvalue: there is nothing to alias otherwise, and the
               value case is a fresh object, which is a copy of nothing. *)
            let x = if binds_by_ref t && is_lvalue e1 then "&" ^ x else x in
            !out ^ ind ^ decl_of t x ^ " = " ^ v ^ ";\n") in
    let s2 = emit ind d e2 in
    scope := saved;
    s1 ^ s2

  | ESeq (e1, e2) -> emit ind D_Ignore e1 ^ emit ind d e2

  | EApp ({ e = EQual (n, _) }, args)
      when D_Return? d && Some? (tail_target n args) ->
    let (f, label, bs) = Some?.v (tail_target n args) in
    let args = match HashTable.try_find !keeps f with
               | Some flags -> filter_by flags args
               | None -> args in
    let out = mk_ref "" in
    let vals = List.map2 (fun ((b:binder), (x:string)) (a:expr) ->
                 (b, x, c_rvalue out ind b.b_ty a)) bs args in
    (* Every argument is read before any parameter is written. *)
    let moves = vals |> List.filter (fun (_, x, v) -> v <> x) in
    vals |> List.iter (fun (_, x, v) ->
      if v = x then tail_kept := v :: !tail_kept);
    let tmps = moves |> List.map (fun ((b:binder), x, v) ->
      let t = fresh "tail" in
      (x, t, ind ^ "  " ^ decl_of b.b_ty t ^ " = " ^ v ^ ";\n")) in
    if not (List.existsb (fun l -> l = label) !tail_used) then
      tail_used := label :: !tail_used;
    !out ^ ind ^ "{\n" ^
    String.concat "" (tmps |> List.map (fun (_, _, s) -> s)) ^
    String.concat "" (tmps |> List.map (fun (x, t, _) ->
      ind ^ "  " ^ x ^ " = " ^ t ^ ";\n")) ^
    ind ^ "  goto " ^ label ^ ";\n" ^ ind ^ "}\n"

  (* Section 51.6.  A test of a [@@custard_c_ifdef] flag is a test the
     preprocessor makes.  Each arm keeps a block of its own, as it would
     under a C [if], so that a name it declares cannot collide with one the
     code after it declares.

     Only one arm survives the preprocessor, so a parameter or local that the
     other arm alone reads is unused in this build, and [-Wunused-parameter]
     / [-Wunused-variable] fire on it.  Each arm therefore voids the names in
     scope that the other arm reads and it does not. *)
  | EIf ({ e = EQual (n, _) }, t, f)
      when Some? (HashTable.try_find !ifdefs (string_of_name n)) ->
    let cond = Some?.v (HashTable.try_find !ifdefs (string_of_name n)) in
    let vt = vars_of t in
    let vf = vars_of f in
    let voids (mine:list string) (other:list string) : ML string =
      let xs = other |> List.fold_left (fun acc x ->
        if List.mem x mine || List.mem x acc ||
           not (List.existsb (fun (y, _) -> y = x) !scope)
        then acc else x :: acc) [] |> List.rev in
      String.concat "" (xs |> List.collect (fun x ->
        let s = lookup_var x in
        let ident = List.for_all (fun c -> BU.is_letter_or_digit c || c = '_')
                                 (String.list_of_string s) in
        if s = unit_value then []
        else [ind' ^ "(void)" ^ (if ident then s else group s) ^ ";\n"])) in
    let tv = voids vt vf in
    let fv = voids vf vt in
    let arm (body:string) : string =
      if body = "" then "" else ind ^ "{\n" ^ body ^ ind ^ "}\n" in
    let tt = arm (tv ^ emit ind' d t) in
    let ft = arm (fv ^ emit ind' d f) in
    ind ^ "#if " ^ cond ^ "\n" ^ tt ^
    (if ft = "" then "" else ind ^ "#else\n" ^ ft) ^
    ind ^ "#endif\n"

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
     expression, so in general it goes inside the loop and the exit is a
     [break].

     Section 58: when evaluating the condition needs no statements -- [out]
     comes back empty -- what is left is a pure C expression, and the loop
     can be spelled the way it would have been written by hand.  The two
     forms are equivalent: [while (c)] tests before each iteration
     including the first, which is where the [break] already stood, and a
     condition inside the header is re-evaluated every iteration just as
     one inside the body was.  This is a printing choice and nothing
     downstream depends on it. *)
  | EWhile (c, body) ->
    let out = mk_ref "" in
    let cs = c_expr out ind' c in
    (if !out = ""
     then ind ^ "while (" ^ unparen cs ^ ") {\n"
     else ind ^ "while (true) {\n" ^ !out ^
          ind' ^ "if (" ^ negate cs ^ ") { break; }\n") ^
    emit ind' D_Ignore body ^
    ind ^ "}\n" ^
    (match d with D_Ignore -> "" | _ -> finish ind d unit_value)

  (* Control does not reach here.  [abort] is [_Noreturn], so no [return]
     has to follow it even in a value position. *)
  (* Cherry: an [EUnreachable] is a fact F* proved, which debug mode checks
     and a release build lets the C compiler rely on (cherry.h). *)
  | EUnreachable s when Options.custard_cherry () ->
    ind ^ "CHERRY_UNREACHABLE(" ^ debug_what ("unreachable code (" ^ s ^ ")") ^ ");\n"
  | EAbort s | EUnreachable s ->
    ind ^ "/* " ^ escape s ^ " */\n" ^ ind ^ "abort();\n"

  (* Section 120.  A comment in statement position.  The standalone form --
     an empty [after] on a unit operand, which is what
     [Pulse.Lib.Comment.comment] builds -- is a line of its own; the general
     form has no case here at all: it falls through to the expression path,
     which puts the comments around the operand inline -- and has to, because
     a comment after the statements of a [return] would be after the return.
     (What that costs is that a large operand is hoisted; what it buys is
     that the comment stays attached to the value it is about.) *)
  | EOp ({ po_op = Commented (before, "") }, [{ e = EConst CUnit }]) ->
    ind ^ "/* " ^ before ^ " */\n" ^ unit_result ind d
  (* And a comment on a value nothing reads.  The value goes -- that is what
     [D_Ignore] means -- but the comment does not, and [(void)(/* a */ 0 /* b
     */);] is a statement written to hold two comments.  Section 99's point
     exactly: a cast to void that computes nothing says nothing either. *)
  | EOp ({ po_op = Commented (before, after) }, [b])
      when D_Ignore? d && is_droppable b ->
    ind ^ "/* " ^ before ^ " */\n" ^ ind ^ "/* " ^ after ^ " */\n"
  | EOp ({ po_op = BufCreate lt }, [init; len]) ->
    emit_alloc ind d None lt e.ty init len

  | EOp ({ po_op = PBuf f }, args) when f <> "read" && f <> "alloc" ->
    let out = mk_ref "" in
    let c = pbuf_call out ind f args in
    !out ^ ind ^ c ^ ";\n" ^ unit_result ind d

  | EOp ({ po_op = RefSet }, [r; v]) ->
    let out = mk_ref "" in
    let r' = c_expr out ind r in
    let v' = c_rvalue out ind v.ty v in
    !out ^ ind ^ rc_fn "set" r.ty ^ "(" ^ r' ^ ", " ^ v' ^ ");\n" ^ unit_result ind d

  (* Cherry: the reset of a cell a constructor reuses (cherry.md, "Heap cell
     reuse"). *)
  | EOp ({ po_op = Reset (cn, kept) }, [a]) ->
    (match find_ctor cn with
     | Some (dt, fs) ->
       let out = mk_ref "" in
       let x = c_expr out ind a in
       let fl = List.zip fs (if List.length kept = List.length fs then kept
                             else List.map (fun _ -> false) fs) in
       let on (op:string) (want:bool) : ML string =
         String.concat "" (fl |> List.collect (fun ((f, t), k) ->
           if is_nonplain_ty t && k = want
           then [ind' ^ rc_call op t (cell_field x dt cn f) ^ ";\n"] else [])) in
       !out ^
       ind ^ "if (cherry_is_unique(" ^ x ^ ")) {\n" ^ on "dec" false ^ finish ind' d x ^
       ind ^ "} else {\n" ^ on "inc" true ^
       ind' ^ rc_call "dec" a.ty x ^ ";\n" ^ finish ind' d "NULL" ^
       ind ^ "}\n"
     | None -> failwith "Cherry: reset of an unknown constructor")
  | EOp ({ po_op = ResetFree }, [w]) ->
    let out = mk_ref "" in
    let v = c_expr out ind w in
    !out ^ ind ^ "free(" ^ v ^ ");\n" ^ unit_result ind d

  (* Cherry: a record update (cherry.md, "Record updates"). *)
  | EOp ({ po_op = Update (cn, is) }, a :: vs) ->
    (match find_ctor cn with
     | Some (dt, fs) ->
       let out = mk_ref "" in
       let x = c_expr out ind a in
       let vals = vs |> List.map (fun (v:expr) -> c_rvalue out ind v.ty v) in
       let u = fresh "u" in
       let sets = List.zip is vals |> List.map (fun (i, v) ->
         let (f, t) = List.nth fs i in
         let fld = cell_field u dt cn f in
         (if is_nonplain_ty t then ind ^ rc_call "dec" t fld ^ ";\n" else "") ^
         ind ^ fld ^ " = " ^ v ^ ";\n") in
       !out ^
       ind ^ decl_of e.ty u ^ " = " ^ cell_unshare dt cn ^ "(" ^ x ^ ");\n" ^
       String.concat "" sets ^ finish ind d u
     | None -> failwith "Cherry: update of an unknown constructor")

  (* Exceptions (cherry.md, "Exceptions"). *)
  | EOp ({ po_op = ExnRaise }, [a]) ->
    let out = mk_ref "" in
    let v = c_expr out ind a in
    !out ^ ind ^ "cherry_raise(" ^ v ^ ");\n" ^ unit_result ind d
  | EOp ({ po_op = ExnPending }, []) -> finish ind d "CHERRY_EXN_PENDING()"
  | EOp ({ po_op = ExnTake }, []) -> finish ind d "cherry_exn_take()"
  (* Leaving with an exception pending: the result is no value, and the
     caller, which tests, never reads it. *)
  | EOp ({ po_op = ExnExit }, []) ->
    (match !cur_ret with
     | None -> ind ^ "cherry_exn_uncaught();\n"
     | Some _ when !void_ret -> ind ^ "return;\n"
     | Some t -> ind ^ "{ " ^ decl_of t "cherry_dummy" ^ "; memset(&cherry_dummy, 0, sizeof cherry_dummy); return cherry_dummy; }\n")

  | EOp ({ po_op = RcInc }, [a]) | EOp ({ po_op = RcDec }, [a]) ->
    let out = mk_ref "" in
    let v = c_expr out ind a in
    let op = (match e.e with EOp ({ po_op = RcInc }, _) -> "inc" | _ -> "dec") in
    !out ^ ind ^ rc_fn op a.ty ^ "(" ^ v ^ ");\n" ^ unit_result ind d

  | EOp ({ po_op = BufWrite }, [b; i; v]) ->
    let out = mk_ref "" in
    let lhs = (c_subscript out ind b i).c_text in
    (* Section 59.  An assignment to a cell of the element type. *)
    let v = c_rvalue out ind v.ty v in
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
              | TBuf e | TRef (_, e) -> ty e
              | _ -> reject "a blit whose destination is not a pointer" [] in
    let srcv = c_expr out ind src in
    (* Section 59.  The two offsets are added to a pointer and the length is
       multiplied by a [sizeof], so in all three the other operand fixes the
       type and a literal's cast repeats it. *)
    let siv = c_rvalue out ind si.ty si in
    let dstv = c_expr out ind dst in
    let div = c_rvalue out ind di.ty di in
    let lenv = c_rvalue out ind len.ty len in
    (* [group] and not a hand-written pair: section 41.1.  The length is
       almost always already parenthesized -- a literal, a cast, a field of a
       struct -- and a second pair around it is what section 32.10's gate
       rejects. *)
    !out ^ ind ^ "memmove(" ^ dstv ^ " + " ^ div ^ ", " ^ srcv ^ " + " ^ siv ^
    ", " ^ group lenv ^ " * sizeof(" ^ elt ^ "));\n" ^ unit_result ind d

  (* Cherry: any other call in tail position is a guaranteed tail call when
     the target can make it one (cherry.md, "Tail calls"), so that mutual
     recursion, and recursion through a closure, run in constant stack as
     they do in OCaml. *)
  | EApp (hd, args) when D_Return? d && Some? (musttail_head hd args e.ty) ->
    let head = Some?.v (musttail_head hd args e.ty) in
    let out = mk_ref "" in
    let s = c_rvalue out ind e.ty e in
    if !void_ret then begin
      (* The [void] call has gone into [out] as the last statement. *)
      let o = !out in
      let call_start = ind ^ head in
      let lines = String.split ['\n'] o in
      match List.rev lines with
      | "" :: last :: rest when starts_with last call_start ->
        let call = String.substring last (String.length ind)
                     (String.length last - String.length ind - 1) in
        String.concat "\n" (List.rev rest) ^ (if Nil? rest then "" else "\n") ^
        ind ^ "CHERRY_TAILCALL_VOID(" ^ call ^ ");\n"
      | _ -> o ^ finish ind d s
    end
    else if starts_with s head then !out ^ ind ^ "CHERRY_MUSTTAIL return " ^ s ^ ";\n"
    else !out ^ finish ind d s

  | _ ->
    let out = mk_ref "" in
    (* Section 59.  [D_Return] and [D_Assign] are assignment contexts whose
       target type is [e.ty] -- the IR is typed, so a returned value has the
       function's result type and an assigned one the variable's -- and
       [D_Ignore] discards the value, where the spelling cannot matter. *)
    let s = c_rvalue out ind e.ty e in
    !out ^ finish ind d s

and unit_result (ind:string) (d:dest) : ML string =
  match d with D_Ignore -> "" | _ -> finish ind d unit_value

(* [BufCreate] is [init; len]: a run of [len] copies of [init].  A stack
   allocation is a local array -- a variable-length one when the length is not
   a constant, which C99 has and both target compilers implement -- and a heap
   allocation is [malloc].  Either way the run has to be filled, since C
   initializes neither.

   {2 Section 94: an initializer where C has one}

   Filling it with a loop is the general answer and it was the only one.  But
   an array whose length is a constant and whose fill is a constant is exactly
   what C's initializer syntax is for, and the two are not equivalent to a
   reader or to a compiler: [uint32_t buf[64] = { 0 };] is one line and lands
   in [.bss], where the loop is three lines that a compiler has to prove it
   may turn back into that.  So a stack allocation takes an initializer when
   it can, and the loop stays for everything else.

   Three conditions, each of them load-bearing.

   The length has to be a literal, because a variable-length array *may not*
   be initialized -- that is not a stylistic restriction, C forbids it -- and
   because [{ 0 }] says nothing about how long the array is.

   The element type has to be a scalar.  [{ 0 }] initializes an aggregate
   correctly, but only the first member is written explicitly and the rest are
   zeroed by the standard's own rule, which older compilers report under
   [-Wmissing-braces]; the generated code is compiled with warnings as errors
   often enough that this is not worth the argument.

   And the fill has to be a constant.  For zero that is all that is needed:
   [{ 0 }] zero-initializes the *whole* array however long it is, and the
   length never enters the text.  For any other value C has no repetition
   syntax, so the value is written out once per cell and the length is capped
   -- past the cap the loop is both shorter and clearer, and a thousand copies
   of a literal is not an improvement on three lines. *)
and emit_alloc (ind:string) (d:dest) (nm:option string)
               (lt:lifetime) (t:cty) (init:expr) (len:expr) : ML string =
  let out = mk_ref "" in
  let iv = c_rvalue out ind init.ty init in
  (* Section 59.  The bound is compared against a [size_t] counter this
     printer declares itself, so it is the same situation as an infix
     operator with one literal operand. *)
  let lv = c_rvalue out ind len.ty len in
  let elt = match t with
            | TBuf e | TRef (_, e) -> ty e
            | _ -> reject "an allocation whose result is not a pointer" [] in
  (* Section 97.  [nm] is the name the binding this allocation initializes is
     about to get.  Using it as the array's own name is what removes the
     pointer that would otherwise be declared to hold it: an array *is* an
     address, so the variable and the storage can be one declaration. *)
  let arr = match nm with Some x -> x | None -> fresh "buf" in
  let done_ (s:string) : ML string =
    match nm with Some _ -> "" | None -> finish ind d s in
  let i = fresh "i" in
  let elt_of = match t with
               | TRef (RGc, _) -> ignore (decl_of t ""); t
               | TBuf e | TRef (_, e) -> e
               | _ -> t in
  (* Section 94.5.  [EAny] is *defined* as what an uninitialized allocation is
     filled with, so a fill that is [EAny] asks for the value every cell
     already has and a declaration on its own delivers it.  Writing it out
     costs a loop to store a value chosen for being arbitrary, and it is the
     only fill that no length or element type makes any tidier: it cannot take
     an initializer list at an aggregate element type (§94.2), so the loop
     survives every peephole above.  [Reference.alloc_uninit] and
     [Array.Core.mask_alloc] are the rules that introduce it. *)
  let any_init = EAny? init.e in
  (* Same collapse as the [ELet] case above, for a one-cell stack allocation
     that is not bound to a name: the pointer the caller wanted is the address
     of the variable. *)
  if LStack? lt && is_one len then
    !out ^ ind ^ decl_of elt_of arr ^
    (if any_init then "" else " = " ^ iv) ^ ";\n" ^
    done_ ("&" ^ arr)
  else
  (* Section 94.  A scalar is what [{ 0 }] initializes without
     [-Wmissing-braces] having anything to say about it. *)
  let scalar_elt =
    match elt_of with
    | TInt _ | TFloat _ | TBuf _ | TRef (_, _) -> true
    | TApp (n, []) -> Some "bool" = builtin_type n
    | _ -> false in
  let const_len =
    match len.e with
    | EConst (CInt (n, _, _)) when n >= 0 -> Some n
    | _ -> None in
  (* Section 94.4.  Pulse will allocate a zero-length array and C has no such
     thing -- [t a[0]] is a GNU extension, not C (6.7.6.2p1).  One cell is the
     smallest conforming declaration and nothing can read it, since no index
     is in bounds of a length of zero. *)
  let dlv = if const_len = Some 0 then "1" else lv in
  (* A null pointer is a zero fill: [{ 0 }] gives a null pointer, whatever the
     implementation's null happens to be spelled as. *)
  let zero_init =
    match init.e with
    | EConst (CInt (0, _, _)) -> true
    | EConst (CBool false) -> true
    | EOp ({ po_op = BufNull }, []) -> true
    | _ -> false in
  let const_init = EConst? init.e in
  let rec repeat (n:int) (acc:list string) : list string =
    if n <= 0 then acc else repeat (n - 1) (iv :: acc) in
  match lt, const_len with
  (* [!out] has to be empty: a hoisted statement means the fill or the length
     was not the constant it has to be for any of this to apply, and prefixing
     it to a declaration would put it before the declaration it belongs to. *)
  (* A length of zero needs no fill written out and admits none: [{ }] is not
     an initializer C99 accepts either, and the cell it initializes cannot be
     read.  So it takes [{ 0 }] whatever the fill was. *)
  | LStack, Some n when scalar_elt && !out = "" &&
                        (n = 0 || zero_init ||
                         (const_init && n <= init_list_max)) ->
    ind ^ decl_of elt_of (arr ^ "[" ^ dlv ^ "]") ^ " = { " ^
    (if n = 0 || zero_init then "0"
     else String.concat ", " (repeat n [])) ^ " };\n" ^
    done_ arr
  | _ ->
  let alloc =
    match lt with
    | LStack -> ind ^ decl_of elt_of (arr ^ "[" ^ dlv ^ "]") ^ ";\n"
    | LHeap ->
      (* Section 116.  [len * sizeof(elt)] is computed in [size_t] and wraps
         silently, and when it wraps [malloc] succeeds with a small block that
         the fill loop immediately writes [len] elements into.  The [NULL]
         check below cannot see it: the allocation did not fail.  Nothing in
         the F* signature prevents it either -- [Pulse.Lib.Vec.alloc] bounds
         no length -- so a fully verified program reaches it, and the result
         is heap corruption that is silent without a sanitizer.

         karamel emits [KRML_CHECK_SIZE] here, so this was a memory-safety
         regression against the backend Custard is replacing rather than a
         cost of going direct.  The test shares the [abort ()] the null check
         already has.  A constant length needs none: the product is a constant
         expression the C compiler folds, and a comparison it can decide is
         one [-Wall] would rather not see. *)
      (* Section 128.1.  Through a [size_t] temporary, rather than comparing
         the length expression itself.  A length whose C type is narrower
         than [size_t] -- a [uint32_t], which most of them are -- makes the
         comparison decidable on a 64-bit target, and [-Wextra] reports a
         decidable comparison as [-Wtype-limits]: the DICE example is built
         with [-Werror] and its [uint8_t] buffers stopped compiling.  The
         check is not pointless, because [size_t] is 32 bits wide on a
         32-bit target and the product does overflow there; it is the *type*
         of the operand that the warning reads, and a [size_t] variable has
         the full range whatever the value assigned to it. *)
      (if Some? const_len then ""
       else let n = fresh "sz" in
            ind ^ "{ size_t " ^ n ^ " = (size_t)" ^ group dlv ^ ";\n" ^
            ind ^ "  if (" ^ n ^ " > SIZE_MAX / sizeof(" ^ elt ^
            ")) { abort(); } }\n") ^
      ind ^ elt ^ " *" ^ arr ^ " = (" ^ elt ^ " *)malloc(" ^ group dlv ^
      " * sizeof(" ^ elt ^ "));\n" ^
      ind ^ "if (" ^ arr ^ " == NULL) { abort(); }\n" in
  (* Section 101.  A length of zero admits no fill: the loop's condition is
     [_ci < 0], which is false on entry, and the cell the declaration had to
     round up to (section 94.4) cannot be indexed because no index is in
     bounds of a length of zero.  The scalar path above already dropped the
     fill for this case by writing [{ 0 }]; this is the same fact stated for
     an element type that has no initializer list. *)
  let fill =
    if const_len = Some 0 || any_init then "" else
  (* Section 59.  The counter is a [size_t] and the length is compared
     against it, so the cast is there for a length of some other integer
     type; when the length already *is* a [size_t] it says nothing. *)
  ind ^ "for (size_t " ^ i ^ " = 0; " ^ i ^ " < " ^
  (* Section 95.  Under [--custard_sizet_width 32] a [FStar.SizeT.t] length is
     a [uint32_t] and the counter is still a [size_t], so it needs the cast
     that a native-width length does not. *)
  (if len.ty = TInt (Unsigned, WSizet) && not (sizet_narrow ())
   then group lv else "(size_t)" ^ group lv) ^
  "; " ^ i ^ "++) {\n" ^
  ind ^ "  " ^ arr ^ "[" ^ i ^ "] = " ^ iv ^ ";\n" ^
  ind ^ "}\n" in
  !out ^ alloc ^ fill ^
  done_ arr

(* -------------------------------------------------------------------- *)
(* Matching                                                             *)
(* -------------------------------------------------------------------- *)

(* A pattern becomes a list of tests on the scrutinee and a list of bindings
   introduced by it, both expressed as C against a *path* -- the C expression
   that reaches the sub-value the pattern is matching.  Compiling to an
   if/else chain rather than a [switch] is what lets a nested pattern, a
   constant pattern and a variable pattern all be handled by one mechanism. *)
and pat_tests (path:c_expression) (t:cty) (p:pat)
    : ML (list string & list (string & c_expression)) =
  match p with
  | PWild -> ([], [])
  | PVar x -> ([], [(x, path)])
  (* Section 44.2.  A string pattern is a test on contents, not on address:
     [pat_tests] is handed the type of the path, so it can see the difference
     without looking at the constant. *)
  (* A Cherry integer literal that is not a small integer is a cell, so the
     test compares contents. *)
  | PConst (CInt (v, _, None))
    when Options.custard_cherry () &&
         not (v < 1073741824 && v > -1073741824) ->
    (["cherry_int_eq(" ^ path.c_text ^ ", " ^ int_lit v ^ ")"], [])
  | PConst c when Some? (content_eq t "" "") ->
    (match content_eq t path.c_text (constant c) with
     | Some c -> ([c], [])
     | None -> ([], []))
  (* Section 59.3.  The path carries the type -- [t] is it, and a path is
     never a literal -- so a constant pattern is the one-literal-operand case
     of a comparison and the cast repeats what the scrutinee already says. *)
  | PConst c ->
    (match converted_int t t c with
     | Some v -> ([path.c_text ^ " == " ^ v], [])
     | None -> ([path.c_text ^ " == " ^ constant c], []))
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
         let t1, b1 = pat_tests (c_postfix (postfix_text path ^ "." ^ c_var f)) ft q in
         (ts @ t1, bs @ b1)) ([], [])
     | _ -> reject ("the record type " ^ string_of_name tn)
              ["It belongs to no record declaration in the program."])
  | PCtor (cn, ps) when Some? (find_exn cn) ->
    let fields = Some?.v (find_exn cn) in
    let rec go (fs : list (string & cty)) (ps : list pat)
             : ML (list string & list (string & c_expression)) =
      match fs, ps with
      | (f, ft) :: fs, p :: ps ->
        let t1, b1 = pat_tests (c_postfix (exn_field (postfix_text path) cn f)) ft p in
        let t2, b2 = go fs ps in
        (t1 @ t2, b1 @ b2)
      | _ -> ([], []) in
    let ts, bs = go fields ps in
    (("cherry_exn_is(" ^ path.c_text ^ ", &" ^ exn_info cn ^ ")") :: ts, bs)
  | PCtor (cn, ps) ->
    (match find_ctor cn with
     | None -> reject ("the constructor " ^ string_of_name cn)
                 ["It belongs to no type declaration in the program."]
     | Some (d, fields) ->
       let tests = if single_ctor d then []
                   else [tag_of (postfix_text path) d ^ " == " ^ c_tag cn] in
       let sub (f:string) : ML c_expression =
         let base = postfix_text path in
         c_postfix (if is_boxed d then cell_field base d cn f
         else if single_ctor d then base ^ "." ^ c_var f
         else base ^ arm_sel cn fields f) in
       let rec go (fs : list (string & cty)) (ps : list pat)
                : ML (list string & list (string & c_expression)) =
         match fs, ps with
         | (f, ft) :: fs, p :: ps ->
           let t1, b1 = pat_tests (sub f) ft p in
           let t2, b2 = go fs ps in
           (t1 @ t2, b1 @ b2)
         | _ -> ([], []) in
       let t2, b2 = go fields ps in
       (tests @ t2, b2))

(* A foreign statement macro can hide an unmatched [if] or several statements
   on one printed line.  Always brace conditional arms, including match arms. *)
and brace (ind:string) (body:string) : ML string =
  if body = "" then " { }\n" else " {\n" ^ body ^ ind ^ "}\n"

and starts_with (s:string) (pre:string) : ML bool =
  String.length s >= String.length pre &&
  String.substring s 0 (String.length pre) = pre

and guard_rejected (#a:Type) () : ML a =
  reject "a pattern guard"
    ["Rewrite the guard as an 'if' in the branch body."]

and emit_match (ind:string) (d:dest) (scrut:expr) (brs:list branch) : ML string =
  let out = mk_ref "" in
  let sd = c_expr_doc out ind scrut in
  let sv = sd.c_text in
  (* Branches whose body only aborts are gone by now (section 5.6); what is
     left is an empty match, which cannot be entered. *)
  if Nil? brs then
    !out ^ finish ind D_Ignore sv ^
    (if Options.custard_cherry ()
     then ind ^ "CHERRY_UNREACHABLE(" ^ debug_what "empty match" ^ ");\n"
     else ind ^ "abort();\n") else
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
  let xd = if direct then sd else c_postfix x in
  let ind' = ind ^ "  " in
  (* The bindings of a branch are aliases, not declarations (see
     [bind_alias]), so a branch body is emitted with them in scope and the
     scope is restored afterwards. *)
  let branch_body (bi:string) (p:pat) (b:expr) : ML string =
    let saved = !scope in
    let _, binds = pat_tests xd scrut.ty p in
    (* Cherry: the fields a branch uses are read out of the scrutinee before
       the body runs, since the body may release it (cherry.md). *)
    let pre =
      if is_nonplain_ty scrut.ty then
        let tys = pat_var_tys p scrut.ty in
        let used = vars_of b in
        binds |> List.collect (fun (v, path) ->
          if not (List.mem v used) then [] else
          match List.tryFind (fun (w, _) -> w = v) tys with
          | Some (_, t) ->
            let nm = bind_var v in
            [bi ^ decl_of t nm ^ " = " ^ path.c_text ^ ";\n"]
          | None -> bind_alias v path; [])
      else (binds |> List.iter (fun (v, path) -> bind_alias v path); []) in
    let body = emit bi d b in
    scope := saved;
    String.concat "" pre ^ body in
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
  (* Only a destination that discards the value can receive nothing: one that
     assigns or returns it always gets a statement.  The trial emission is
     skipped there, and not only to save the work: the branch kept is
     emitted again, so trying every match's last branch is exponential in
     how deeply such matches nest. *)
  let discards =
    (match d with
     | D_Ignore -> true
     | D_Return -> !void_ret
     | _ -> false) in
  let emits_nothing (p:pat) (b:expr) : ML bool =
    discards &&
    begin
    let saved_ctr = !ctr in
    let saved_declared = HashTable.copy !declared in
    let s = branch_body ind' p b in
    ctr := saved_ctr;
    declared := saved_declared;
    s = ""
    end in
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
      let ts, bs = pat_tests xd scrut.ty p in
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
    let last (chk:list string) (p:pat) (b:expr) : ML string =
      (* Cherry's debug mode checks that it does match, before its bindings
         read the scrutinee (cherry.h, CHERRY_DEBUG). *)
      let check (bi:string) : ML string =
        if Nil? chk || not (Options.custard_cherry ()) then "" else
        bi ^ "CHERRY_ASSUME(" ^ String.concat " && " chk ^ ", " ^
        debug_what "incomplete match" ^ ");\n" in
      if first then check ind ^ branch_body ind p b
      else ind ^ "else" ^ brace ind (check ind' ^ branch_body ind' p b) in
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
      let tests, _ = pat_tests xd scrut.ty p in
      last tests p b
    | (p, g, b) :: rest ->
      if Some? g then guard_rejected ();
      let tests, _ = pat_tests xd scrut.ty p in
      (* Irrefutable, so it is the last branch that can run; anything after it
         is dead and C would warn about it. *)
      if Nil? tests then last [] p b
      else
        let after = go false rest in
        (if first then ind else ind ^ "else ") ^
        "if (" ^ String.concat " && " tests ^ ")" ^
        brace ind (branch_body ind' p b) ^
        after in
  head ^ go true kept

(* -------------------------------------------------------------------- *)
(* Declarations                                                         *)
(* -------------------------------------------------------------------- *)

(* Would a value of [t] contain a value of the type being defined?  C has no
   way to store that, and karamel's answer -- box the recursive occurrence --
   is a representation decision that belongs in the layout pass, not here. *)
let body_occurs (target:string) (b:tydef) : ML bool =
  (* Each type is visited once: a type with two fields of a third, recursive,
     one would otherwise be explored along every path through it. *)
  let seen : HashTable.t string bool = HashTable.create 20 in
  let rec occurs (t:cty) : ML bool =
    match t with
    | TApp (n, _) ->
      let k = string_of_name n in
      k = target ||
      (if HashTable.mem seen k then false else begin
         HashTable.add seen k true;
         match find_type n with
         | Some d -> body d.dt_body
         | None -> false
       end)
    | TTuple ts -> ts |> List.existsb occurs
    (* A pointer is a size; what it points to is not part of this value. *)
    | _ -> false
  and body (b:tydef) : ML bool =
    match b with
    | TAbbrev c -> occurs c
    | TRecord fs -> fs |> List.existsb (fun (_, c) -> occurs c)
    | TVariant cs ->
      cs |> List.existsb (fun (_, fs) -> fs |> List.existsb (fun (_, c) -> occurs c))
    | TAbstract -> false in
  body b

let check_finite (d:dtype) : ML unit =
  if not (is_boxed d) && body_occurs (string_of_name d.dt_name) d.dt_body then
    reject ("the recursive datatype " ^ string_of_name d.dt_name)
      (["A C struct cannot contain itself by value.";
        "Use an explicit pointer (a Pulse ref, array or box) for the \
         recursive field."]
       @
       (* Section 100.  When the type arrived through an external, the
          recursive field is not something the program can be asked to
          change -- [Prims.list] is a cons list and stays one -- so the
          declaration that put it in front of the backend is named instead.
          Before section 100 this case was reported as a frozen type, which
          named the external but not the obstruction; now both are said. *)
       (match HashTable.try_find frozen_by (string_of_name d.dt_name) with
        | Some ext ->
          ["It reaches the backend through " ^ ext ^ ", whose signature \
            mentions it.  That declaration is realized outside this program, \
            so there is no definition of it to compile and nothing here can \
            change the shape of the type it names."]
        | None -> []))

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

(* Section 47.1.  The tag enum of a tagged union is declared *beside* the
   struct, not inside it.

   In C the enumerators of an enum nested in a struct have file scope and leak
   out, so `CEXTERN_BUMP' resolves at a use site.  In C++ an unnamed enum
   nested in a class has *class* scope: the name is `CExtern_cmd::CEXTERN_BUMP'
   and the bare form does not exist.  Every tagged union Custard emitted was
   therefore unusable from C++ or CUDA -- and invisibly so, because the C tests
   are compiled as C11, where the nested form is correct.

   Hoisting is valid C11 and changes nothing about the C output's meaning or
   its layout.  [extern "C"] does not help: linkage is not scope. *)
let enum_tag (n:string) : string = n ^ "_tags"

let is_struct (d:dtype) : ML bool =
  match d.dt_body with
  | TRecord _ -> true
  | TVariant _ -> not (is_enum d)
  | TAbbrev _ | TAbstract -> false

let type_fwd (d:dtype) : ML (option string) =
  if Some? (builtin_type d.dt_name) then None else
  if is_boxed d then Some ("typedef cherry_obj *" ^ c_name d.dt_name ^ ";\n") else
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
  (* Cherry: a boxed value is a pointer. *)
  | TApp (n, _) when is_boxed_name n -> []
  | TApp ({ ns = ["FStar"; "ImmutableArray"; "Base"]; id = "t" }, _) -> []
  | TApp (n, args) -> string_of_name n :: List.collect value_deps args
  | TTuple ts -> List.collect value_deps ts
  (* A pointer is a size, and a function is a pointer: an incomplete type is
     enough to declare either. *)
  | TBuf _ | TRef (_, _) | TArrow _ -> []
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
  let index : HashTable.t string dtype = HashTable.create 64 in
  ds |> List.iter (fun d -> HashTable.add index (string_of_name d.dt_name) d);
  let out : ref (list dtype) = mk_ref [] in
  let seen : HashTable.t string bool = HashTable.create 64 in
  let busy : HashTable.t string bool = HashTable.create 64 in
  let rec visit (d:dtype) : ML unit =
    let k = string_of_name d.dt_name in
    if Some? (HashTable.try_find seen k) || Some? (HashTable.try_find busy k) then () else begin
      HashTable.add busy k true;
      body_value_deps d.dt_body |> List.iter (fun n ->
        match HashTable.try_find index n with
        | Some d' -> visit d'
        | None -> ());
      HashTable.remove busy k;
      HashTable.add seen k true;
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
  | TRecord _ when is_boxed d ->
    reject ("the recursive record " ^ string_of_name d.dt_name)
      ["Cherry boxes recursive variants only, so far."]
  (* Cherry: one cell per constructor with fields, each led by the header
     the runtime counts references in.  A constructor without fields is a
     scalar and has no cell. *)
  | TVariant cs when is_boxed d ->
    Some ("enum " ^ enum_tag n ^ " {\n" ^
          String.concat ",\n" (cs |> List.map (fun (c, _) -> "  " ^ c_tag c)) ^
          "\n};\n" ^
          String.concat "" (cs |> List.collect (fun (c, fs) ->
            if Nil? fs then [] else
            [cell_struct d c ^ " {\n  cherry_obj hdr;\n" ^
             String.concat "" (fs |> List.map (fun (f, t) ->
               "  " ^ decl_of t (c_var f) ^ ";\n")) ^
             "};\n"])))
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
      (* A tagged union.  The members are named after the constructor alone
         (section 114), and a constructor carrying one field is the member
         itself (section 113). *)
      let nonempty = cs |> List.filter (fun (_, fs) -> Cons? fs) in
      Some ("enum " ^ enum_tag n ^ " {\n" ^
            String.concat ",\n" (cs |> List.map (fun (c, _) -> "  " ^ c_tag c)) ^
            "\n};\n" ^
            open_struct () ^
            "  enum " ^ enum_tag n ^ " tag;\n" ^
            (match nonempty with
             | [] -> ""
             | _ ->
               "  union {\n" ^
               String.concat "" (nonempty |> List.map (fun (c, fs) ->
                 if arm_flat fs
                 then "    " ^ decl_of (snd (List.hd fs)) (arm_name c) ^ ";\n"
                 else
                   "    struct {\n" ^
                   String.concat "" (fs |> List.map (fun (f, t) ->
                     "      " ^ decl_of t (c_var f) ^ ";\n")) ^
                   "    } " ^ arm_name c ^ ";\n")) ^
               "  } val;\n") ^
            "};\n")

let kept_binders (l:dlet) : ML (list binder) =
  match HashTable.try_find !keeps (string_of_name l.dl_name) with
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
(* Section 76.  The operators C folds at translation time, which is every one
   Custard prints infix at an integer or boolean type.  The float widths are
   left out: a narrow one is a call ({!narrow_call}) and so not constant, and
   a wide one is only reachable through the same globals, so telling the two
   apart would buy nothing yet.

   Division and the shifts are on the list.  Both have inputs C would refuse
   to fold -- a zero divisor is a constraint violation, an over-wide shift is
   undefined -- and neither can occur: [UInt32.div] and [UInt32.shift_left]
   carry the preconditions that rule them out, so a term that reaches here has
   already been proved not to be one. *)
let const_op (o:prim_op) : ML bool =
  (match o.po_ty with Some (PFloat _) -> false | _ -> true) &&
  (match o.po_op with
   | Add | AddW | Sub | SubW | Mult | MultW | Div | DivW | Mod
   | BOr | BAnd | BXor | BShiftL | BShiftR | BNot
   | Eq | Neq | Lt | Lte | Gt | Gte | And | Or | Not -> true
   | _ -> false)

let rec static_init (x:expr) : ML (option string) =
  match x.e with
  (* Section 59.  The initializer of a declaration of this very type, which
     is the assignment context {!converted_int} is about; a bare literal is
     still a constant expression, which is what this list is selecting for. *)
  | EConst c ->
    (match converted_int x.ty x.ty c with
     | Some v -> Some v
     | None ->
       match c with
       | CInt (_, _, None) -> None
       (* Section 66.  A narrow float's expression spelling is a compound
          literal, which is not a constant expression; here the braced
          initializer is what is meant. *)
       | CFloat (v, fw) when narrow_ty fw -> Some (narrow_float_init fw v)
       | _ -> Some (constant c))
  (* Section 68.  A reference to a [@@ CMacro ] definition is a reference to
     its body, textually, before the program runs -- so it is as much a
     constant expression as the body is, and can initialize a global. *)
  | EQual (n, _) when Some? (HashTable.try_find !macros (string_of_name n)) ->
    Some (c_name n)
  | ECast (e1, t) ->
    (match e1.ty, t, static_init e1 with
     | TInt a, TInt b, Some v when a = b -> Some v
     (* Section 66.  A conversion to or from a narrow width is a call, and a
        call is not a constant expression.  The *literals* still are -- they
        are emitted as bit patterns for exactly this reason -- so this rules
        out only a static initializer that converts, which then gets the same
        diagnostic any other non-constant initializer does. *)
     | _, TFloat fw, _ when narrow_ty fw -> None
     | TFloat fw, _, _ when narrow_ty fw -> None
     | _, _, Some v -> Some ("(" ^ ty t ^ ")" ^ v)
     | _ -> None)
  | ECoerce (e1, t) ->
    (match static_init e1 with
     | Some v -> if e1.ty = t then Some v else Some ("(" ^ ty t ^ ")" ^ v)
     | None -> None)
  (* A null pointer constant, which is what an uninitialized buffer global is
     and the one aggregate-typed thing on this list. *)
  | EOp ({ po_op = BufNull }, []) -> Some ("(" ^ ty x.ty ^ ")NULL")
  (* Section 76.  Arithmetic over constants is a constant expression in C, and
     after [Simplify.const_globals] a chain of type-class constants is exactly
     that: [(7 + 1)] rather than [bar + 1].  Without this arm the substitution
     would buy nothing, since the result would still not be an initializer.

     Printed by {!c_expr}, not by a second evaluator.  Everything the width
     costs -- {!truncate} at [Int8] and [Int16], the casts section 59.3 keeps
     and drops, the separate promotion of a shift's operands -- is decided
     there, and a constant folded by the C compiler has to be the same value
     the run-time assignment would have computed.  Anything that hoists a
     statement is not an expression at all, so an [out] that came back
     non-empty is the test for that.

     [strcmp] is the one operator on this list that C emits as a call
     (section 44.2), so a string comparison is refused here rather than
     silently becoming a run-time initializer's worth of work. *)
  | EOp (o, es) when const_op o &&
                     es |> List.for_all (fun (a:expr) ->
                       Some? (static_init a) && not (is_string_ty a.ty)) ->
    let out = mk_ref "" in
    let v = c_expr out "" x in
    if !out = "" then Some v else None
  | _ -> None

let has_static_init (l:dlet) : ML bool =
  current := string_of_name l.dl_name;
  Some? (static_init l.dl_body)

(* Section 71.  A [Pulse.Lib.GlobalArray.static_array], which is an *array*
   object and not a pointer one.

   The declarator is the difference that matters.  [decl_of (TBuf t)] gives
   [t *x], which would be a pointer variable with a braced initializer -- not
   the same object and not even legal.  What is wanted is [t x[n]], an array
   of [n] elements with the elements as its initializer, so that the storage
   is the table itself and the name decays to a pointer at every use.

   [const] because {!array_of_static_array} hands out a fractional permission
   and never a full one, so no Pulse program can write through it.  It buys
   [.rodata] rather than [.data], and it turns a write that slipped past the
   proof into a compile error instead of undefined behaviour.  The pointer
   conversion back is at the [BufUnconst] above. *)
let array_decl (l:dlet) : ML (option string) =
  match l.dl_body.e, l.dl_ret with
  | EOp ({ po_op = BufLit }, elems), TBuf t ->
    let out = mk_ref "" in
    let vs = elems |> List.map (fun (x:expr) -> c_rvalue out "" t x) in
    (* A run of length zero has no C spelling: [t x[0]] is a constraint
       violation and [{ }] is not an initializer.  Nor is there anything to
       point at, so this is a refusal rather than a workaround. *)
    if Nil? elems then
      E.raise_error0 E.Error_CustardBadStaticArray [
        text ("Custard: " ^ string_of_name l.dl_name ^ " is an empty static \
               array, and C has no declaration for one.");
        text "An array object needs at least one element, and a run with no \
              elements has no address to hand out either.";
        text "Use Pulse.Lib.Array.null if what is meant is the absence of a \
              run."]
    else
      Some ("const " ^ decl_of t (c_name l.dl_name ^ "[" ^
                                  string_of_int (List.length elems) ^ "]") ^
            " = { " ^ String.concat ", " vs ^ " };\n")
  | _ -> None

(* The same object as {!array_decl}, declared rather than defined.  It has to
   repeat the [const] and the length: a declaration that disagrees with the
   definition about either is a different type, and C says so. *)
let array_extern (l:dlet) : ML (option string) =
  match l.dl_body.e, l.dl_ret with
  | EOp ({ po_op = BufLit }, elems), TBuf t when Cons? elems ->
    Some ("extern const " ^
          decl_of t (c_name l.dl_name ^ "[" ^
                     string_of_int (List.length elems) ^ "]") ^ ";\n")
  | _ -> None

let is_static_array (l:dlet) : ML bool =
  match l.dl_body.e with
  | EOp ({ po_op = BufLit }, _) -> true
  | _ -> false

let global_decl (l:dlet) : ML string =
  current := string_of_name l.dl_name;
  match array_decl l with
  | Some d -> d
  | None ->
  let d = decl_of l.dl_ret (c_name l.dl_name) in
  match static_init l.dl_body with
  | Some v -> d ^ " = " ^ v ^ ";\n"
  | None -> d ^ ";\n"

(* The declaration of a global that another file defines. *)
let global_extern (l:dlet) : ML string =
  current := string_of_name l.dl_name;
  match array_extern l with
  | Some d -> d
  | None -> "extern " ^ decl_of l.dl_ret (c_name l.dl_name) ^ ";\n"

(* Section 68.  A parameterless definition whose value C can compute at
   translation time, emitted as a [#define] rather than as a variable.

   The distinction is not cosmetic.  A variable is not a constant expression,
   so it may not initialize an object with static storage duration, may not be
   a [case] label, and is invisible to [#if] -- which are the three ordinary
   uses of a protocol constant.  karamel has always emitted these as macros
   and consumers write C against that, so a header that exports them as
   [extern] variables is a header the existing callers do not compile
   against. *)
let is_macro (l:dlet) : ML bool =
  Nil? l.dl_binders && List.existsb CMacro? l.dl_flags

(* Deliberately not {!constant}: at an integer width that adds a cast to the
   declared type, and a cast makes the result useless to [#if], which is the
   one of the three uses that cannot be worked around at the call site.  The
   suffix carries the type well enough for the other two, and it is what
   karamel emits, so a consumer's [#if] keeps working. *)
let macro_value (l:dlet) : ML (option string) =
  match l.dl_body.e with
  | EConst (CInt (v, b, Some sw)) -> Some (int_literal sw v b)
  | _ -> static_init l.dl_body

let macro_decl (l:dlet) : ML string =
  current := string_of_name l.dl_name;
  match macro_value l with
  | Some v -> "#define " ^ c_name l.dl_name ^ " (" ^ v ^ ")\n"
  | None ->
    E.raise_error0 E.Error_CustardBadMacro [
      text ("Custard: " ^ string_of_name l.dl_name ^
            " is marked [@@ CMacro ] but its value is not a constant \
             expression.");
      text "A [#define] is substituted before the program runs, so there is \
            nothing to evaluate it: only a literal, or a cast or an \
            arithmetic combination of literals, can be one.";
      text "Drop the attribute to get an ordinary variable, initialized at \
            startup like any other global." ]

(* Every global's initializer goes into the one C function [init_name], so
   only the [first] starts a new C scope: the others keep the names already
   declared, and their locals take subscripts instead of clashing. *)
let global_init (first:bool) (l:dlet) : ML string =
  current := string_of_name l.dl_name;
  void_ret := false;
  cur_ret := None;
  if first then (ctr := 0; reset_scope ()) else scope := [];
  emit "  " (D_Assign (c_name l.dl_name)) l.dl_body ^
  (* Under Cherry a global's value is made persistent once it is computed:
     nothing counts references to it again, so reading it is free. *)
  (if is_nonplain_ty l.dl_ret
   then "  " ^ rc_fn "mark" l.dl_ret ^ "(" ^ c_name l.dl_name ^ ", CHERRY_PERSIST);\n"
   else "")

(* A pointer to a stack slot could be among the arguments of a tail call,
   and the jump would reuse the slot it points to. *)
let rec stack_allocates (e:expr) : ML bool =
  match e.e with
  | EOp ({ po_op = BufCreate LStack }, _) -> true
  | _ -> exists_child stack_allocates e

let let_decl (l:dlet) : ML string =
  current := string_of_name l.dl_name;
  ctr := 0;
  void_ret := TUnit? l.dl_ret;
  cur_ret := Some l.dl_ret;
  reset_scope ();
  kept_binders l |> List.iter (fun b -> let _ = bind_var b.b_name in ());
  (* Section 53.1.  A dropped parameter is a unit one, so a body that mentions
     it wants the only value of that type; binding the name to the constant
     lets the body stand unchanged while the signature loses the parameter. *)
  l.dl_binders |> List.iter (fun b ->
    if TUnit? b.b_ty then bind_alias b.b_name (c_postfix unit_value));
  if Nil? l.dl_binders then
    reject ("the top-level value " ^ string_of_name l.dl_name)
      ["C has no way to initialize a global from a computation.";
       "Make it a function of unit."];
  let used = vars_of l.dl_body in
  (* C also warns about an unused *parameter*, and a definition's parameters
     have to be named, so the ones the body never mentions are voided
     explicitly. *)
  let ok = Options.custard_cherry () && not (stack_allocates l.dl_body) in
  tail_used := [];
  tail_kept := [];
  tail_targets :=
    (if ok then [(string_of_name l.dl_name, "custard_tail",
                  kept_binders l |> List.map (fun b -> (b, lookup_var b.b_name)))]
     else []);
  musttail_ok := ok;
  let body = emit "  " D_Return l.dl_body in
  tail_targets := [];
  musttail_ok := false;
  let voids = String.concat "" (kept_binders l |> List.collect (fun b ->
    let v = lookup_var b.b_name in
    if List.existsb (fun y -> y = b.b_name) used &&
       not (List.mem v !tail_kept) then []
    else ["  (void)" ^ v ^ ";\n"])) in
  signature l ^ " {\n" ^ voids ^
  (if Cons? !tail_used then "custard_tail:;\n" else "") ^ body ^ "}\n"

(* Cherry: the C function a tail group is printed as (cherry.md, "Tail
   calls").  Every member's parameters are its locals, named apart; it starts
   by loading the ones of the member [custard_entry] names from the group's
   argument buffer, and each member's body follows under a label, so that a
   tail call from one member to another assigns the callee's parameters and
   jumps, as a self tail call does in {!let_decl}.  The buffer is
   thread-local, and read before anything else runs, so that a member called
   again while the function runs -- not in tail position, or from another
   thread -- cannot overwrite arguments that have not been read yet. *)
let tail_group_decl (g:tail_group) : ML string =
  let l0 = List.hd g.tg_members in
  current := string_of_name l0.dl_name;
  ctr := 0;
  void_ret := TUnit? l0.dl_ret;
  cur_ret := Some l0.dl_ret;
  reset_scope ();
  (* Each member's own scope, over the one set of declared names. *)
  let members = g.tg_members |> List.mapi (fun i (l:dlet) ->
    scope := [];
    let bs = kept_binders l |> List.map (fun b -> (b, bind_var b.b_name)) in
    l.dl_binders |> List.iter (fun b ->
      if TUnit? b.b_ty then bind_alias b.b_name (c_postfix unit_value));
    (i, l, bs, !scope)) in
  let label (i:int) = "custard_tail_" ^ string_of_int i in
  let slot (i:int) (j:int) = g.tg_args ^ ".m" ^ string_of_int i ^ ".a" ^ string_of_int j in
  let n = List.length members in
  let decls = members |> List.collect (fun (_, _, bs, _) ->
    bs |> List.map (fun ((b:binder), x) -> "  " ^ decl_of b.b_ty x ^ ";\n")) in
  let cases = members |> List.map (fun (i, _, bs, _) ->
    (if i = n - 1 then "  default:" else "  case " ^ string_of_int i ^ ":") ^
    String.concat "" (bs |> List.mapi (fun j ((_:binder), x) -> " " ^ x ^ " = " ^ slot i j ^ ";")) ^
    " goto " ^ label i ^ ";\n") in
  tail_targets := members |> List.map (fun (i, (l:dlet), bs, _) ->
    (string_of_name l.dl_name, label i, bs));
  musttail_ok := true;
  tail_used := [];
  tail_kept := [];
  let bodies = members |> List.map (fun (i, (l:dlet), bs, sc) ->
    current := string_of_name l.dl_name;
    scope := sc;
    let used = vars_of l.dl_body in
    let body = emit "    " D_Return l.dl_body in
    let voids = String.concat "" (bs |> List.collect (fun ((b:binder), x) ->
      if List.existsb (fun y -> y = b.b_name) used &&
         not (List.mem x !tail_kept) then []
      else ["    (void)" ^ x ^ ";\n"])) in
    label i ^ ": {\n" ^ voids ^ body ^
    (if !void_ret then "    return;\n" else "") ^ "  }\n") in
  tail_targets := [];
  musttail_ok := false;
  let fields = members |> List.collect (fun (i, _, bs, _) ->
    if Nil? bs then [] else
    ["  struct {\n" ^
     String.concat "" (bs |> List.mapi (fun j ((b:binder), _) ->
       "    " ^ decl_of b.b_ty ("a" ^ string_of_int j) ^ ";\n")) ^
     "  } m" ^ string_of_int i ^ ";\n"]) in
  let buf = if Nil? fields then "" else
            "static CHERRY_THREAD_LOCAL union {\n" ^ String.concat "" fields ^
            "} " ^ g.tg_args ^ ";\n" in
  let hd = g.tg_fn ^ "(int custard_entry)" in
  buf ^ "static " ^ (if !void_ret then "void " ^ hd else decl_of l0.dl_ret hd) ^ " {\n" ^
  String.concat "" decls ^
  "  switch (custard_entry) {\n" ^ String.concat "" cases ^ "  }\n" ^
  String.concat "" bodies ^ "}\n"

(* Cherry: a member of a tail group, which enters the group's function. *)
let tail_member_decl (i:int) (g:tail_group) (l:dlet) : ML string =
  current := string_of_name l.dl_name;
  reset_scope ();
  let bs = kept_binders l |> List.map (fun b -> bind_var b.b_name) in
  let stores = bs |> List.mapi (fun j x ->
    "  " ^ g.tg_args ^ ".m" ^ string_of_int i ^ ".a" ^ string_of_int j ^ " = " ^ x ^ ";\n") in
  let call = g.tg_fn ^ "(" ^ string_of_int i ^ ")" in
  signature l ^ " {\n" ^ String.concat "" stores ^
  (if TUnit? l.dl_ret then "  CHERRY_TAILCALL_VOID(" ^ call ^ ");\n"
   else if musttail_sig_ok [TInt (FStarC.Const.Signed, W32)] (Some l.dl_ret)
   then "  CHERRY_MUSTTAIL return " ^ call ^ ";\n"
   else "  return " ^ call ^ ";\n") ^ "}\n"

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

(* Section 45.1.  A target that is not a C identifier can be *used* -- it goes
   into the output verbatim and the header that declares it is included -- but
   it cannot be *declared* by Custard, because a declaration needs a
   declarator and [wmma::mma_sync] is not one.  The header is what says where
   the symbol comes from, so the absence of one is the real mistake here. *)
let is_c_identifier (s:string) : ML bool =
  s <> "" &&
  not (let n = FStar.Char.int_of_char (String.get s 0) in
       n >= 0x30 && n <= 0x39) &&
  (String.list_of_string s |> List.for_all (fun c ->
     let n = FStar.Char.int_of_char c in
     (n >= 0x41 && n <= 0x5a) || (n >= 0x61 && n <= 0x7a) ||
     (n >= 0x30 && n <= 0x39) || n = 0x5f))

let extern_decl (x:dexternal) : ML (option string) =
  if Some? x.dx_header then None else
  let () = match x.dx_target with
           | Some t when not (is_c_identifier t) ->
             current := string_of_name x.dx_name;
             reject ("the external name `" ^ t ^ "'")
               ["It is not a C identifier, so Custard cannot declare it, and                  no [@@custard_c_header] says which header does.";
                "Add [@@custard_c_header \"...\"] beside the                  [@@custard_extern] naming the header that declares it."]
           | _ -> () in
  let nm = emitted_name (DExternal x) in
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

(* A generated declaration ends in a newline; quoting one inside a diagnostic
   wants the text and not the line break. *)
let trim_nl (s:string) : ML string =
  let n = String.length s in
  if n > 0 && String.substring s (n - 1) 1 = "\n"
  then String.substring s 0 (n - 1) else s

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
let no_unit : unit_info =
  { cu_name = None; cu_headers = []; cu_inits = []; cu_no_prefix = [] }

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
    (* Section 68.  A macro has no storage, so there is nothing to set; the
       body has already been checked to be a constant expression. *)
    (* Section 71.  A static array is initialized where it is declared, like
       anything else {!static_init} accepts -- it is simply not an expression,
       so it is recognized by its own shape rather than by that function. *)
    | DLet l when Nil? l.dl_binders && not (is_macro l) &&
                  not (has_static_init l) && not (is_static_array l) -> [l]
    | _ -> [])

let init_globals_name (cu:unit_info) (p:program) : ML (option string) =
  if Cons? (global_inits_of p) then Some (init_name cu) else None

let is_public (l:dlet) : ML bool =
  l.dl_flags |> List.existsb Root? &&
  not (l.dl_flags |> List.existsb Entrypoint?) &&
  not (l.dl_flags |> List.existsb Private?)

(* Cherry with [--custard_split]: the definitions are spread over several C
   files, so a definition that is not public is not [static] either -- another
   file may call it.  What has to exist once ([split_data]: the descriptors
   compared by address) is defined in the first file and declared [extern]
   for the others.  A [CInline] definition stays [static] and is put in the
   shared header instead. *)
let split_out : ref bool = mk_ref false

(* The F* module a definition comes from, generated ones included: a lifted
   lambda or a specialization keeps its parent's [ns]. *)
let module_of (n:name) : string = String.concat "." n.ns
let split_data : ref (list string) = mk_ref []

let storage (l:dlet) : ML string =
  if is_public l then ""
  else if !split_out && not (l.dl_flags |> List.existsb CInline?) then ""
  else "static "

(* A helper that only a descriptor names: in a split output, every part has
   it and only the first uses it. *)
let helper_static () : ML string =
  if !split_out then "static CHERRY_UNUSED " else "static "

(* A descriptor whose address is its identity, [static] in a single file. *)
let unique_object (decl:string) (init:string) : ML string =
  if !split_out then begin
    split_data := !split_data @ [decl ^ " = " ^ init ^ ";\n"];
    "extern " ^ decl ^ ";\n"
  end else "static " ^ decl ^ " = " ^ init ^ ";\n"

(* Section 36.3.  Decoration a plugin asked for and Custard does not read.
   [Prologue] goes on the *declaration* as well as the definition: CUDA wants
   [__global__] on both, and a qualifier that appears on one and not the other
   is a redeclaration error rather than a missing qualifier, which is the
   better failure of the two.  [Epilogue] follows the definition only, since
   there is nothing after a prototype for it to attach to. *)
let prologue_of (l:dlet) : ML string =
  String.concat "" (l.dl_flags |> List.collect
    (function Prologue s -> [s ^ "\n"] | _ -> []))

(* Section 51.6.  [#if g ... #endif] around every place the declaration is
   written: its prototype, its header declaration and its definition. *)
let guarded (l:dlet) (s:string) : ML string =
  match List.tryFind Guard? l.dl_flags with
  | Some (Guard g) -> "#if " ^ g ^ "\n" ^ s ^ "#endif\n"
  | _ -> s

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

let requested_c_name (d:decl) : ML (option string) =
  decl_flags d |> List.tryPick (function CName s -> Some s | _ -> None)

let reserved_c_name (s:string) : ML bool =
  List.existsb (fun k -> k = s) (c_keywords @ [
    "_Alignas"; "_Alignof"; "_Atomic"; "_Generic"; "_Noreturn";
    "_Static_assert"; "_Thread_local";
    "alignas"; "alignof"; "and"; "and_eq"; "asm"; "bitand"; "bitor";
    "catch"; "char16_t"; "char32_t"; "class"; "compl"; "constexpr";
    "const_cast"; "decltype"; "delete"; "dynamic_cast"; "explicit";
    "export"; "friend"; "mutable"; "namespace"; "new"; "noexcept"; "not";
    "not_eq"; "nullptr"; "operator"; "or"; "or_eq"; "private"; "protected";
    "public"; "reinterpret_cast"; "static_assert"; "static_cast"; "template";
    "this"; "thread_local"; "throw"; "try"; "typeid"; "typename"; "using";
    "virtual"; "wchar_t"; "xor"; "xor_eq" ])

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
(* Section 115.  [extra] is what the linked units were built with.  A
   consumer computes the C spelling of an imported declaration the same way
   the producer did -- from the declaration, by this function -- so with the
   producer's option absent it recomputed a *different* spelling and emitted
   a call to a symbol the header it includes does not declare.  Taking the
   producer's modules from the `.cui` makes the two agree by construction,
   and does so without asking the consumer to repeat a flag that describes
   somebody else's output. *)
let build_renames (check:bool) (extra:list string) (p:program) : ML unit =
  let mods = Options.custard_c_no_prefix () @ extra in
  renames := HashTable.create 0;
  p |> List.iter (fun d ->
    match requested_c_name d with
    | None -> ()
    | Some s ->
      let src = string_of_name (name_of_decl d) in
      if not (is_c_identifier s) || reserved_c_name s then
        E.raise_error0 E.Error_CustardExportCollision [
          text ("Custard: rename_let on " ^ src ^ " requests `" ^ s ^
                "', which is not an available C/C++ identifier.");
          text "Choose a non-reserved name using ASCII letters, digits and \
                underscores, not starting with a digit." ];
      let target = match d with
                   | DType t -> t.dt_flags |> List.tryPick
                       (function Extern (Some s, _) when s <> "" -> Some s
                               | _ -> None)
                   | _ -> extern_target d in
      (match target with
       | Some t when t <> s ->
         E.raise_error0 E.Error_CustardExportCollision [
           text ("Custard: rename_let requests `" ^ s ^ "' for " ^ src ^
                 ", but custard_extern already specifies `" ^ t ^ "'.");
           text "Use the same name, or remove one of the attributes." ]
       | _ -> ());
      HashTable.add !renames src s);
  if Nil? mods then () else begin
    (* Every C name in the unit as it stands, so that a rename cannot land on
       one.  Types and constructors included: they have no linkage, but a
       [struct] tag and a function sharing a name in one header is at best
       confusing and at worst -- for a typedef -- a redeclaration error. *)
    let taken : HashTable.t string string = HashTable.create 50 in
    p |> List.iter (fun d ->
      let n = name_of_decl d in
      HashTable.add taken (match extern_target d with
                      | Some t -> t
                      | None -> c_name n)
                     (string_of_name n));
    let claimed : HashTable.t string string = HashTable.create 20 in
    let used_mod : HashTable.t string bool = HashTable.create 5 in
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
    (* Section 102.2.  An [assume val] too.  The symbol it names is resolved
       by the linker against code this program does not contain, so the name
       is part of the unit's interface in the only sense that matters here --
       more so than a definition's, since nothing in the unit defines it and
       the whole file is a demand on the outside.  [@@custard_extern "..."]
       already says the name outright and wins: it is the target's spelling,
       taken verbatim (section 45.1), and an option about *prefixes* has
       nothing to say about a name that was never prefixed.  This is what
       lets a program whose realization is called [abort] keep an [Abort.fst]
       that a released F* can still typecheck. *)
    let renamable (d:decl) : ML (option name) =
      match d with
      | DLet l -> if is_public l then Some l.dl_name else None
      | DType t -> Some t.dt_name
      | DExternal x -> (match x.dx_target with
                        | Some "" | None -> Some x.dx_name
                        | Some _ -> None)
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
          HashTable.add used_mod m true;
          let src = string_of_name dn in
          let tgt = match HashTable.try_find !renames src with
                    | Some s -> s
                    | None -> escape_kw (sanitize dn.id) in
          (match HashTable.try_find claimed tgt with
           | Some other when check ->
             E.raise_error0 E.Error_CustardExportCollision [
               text ("Custard: --custard_c_no_prefix would name both " ^
                     other ^ " and " ^ src ^ " `" ^ tgt ^
                     "' in the generated C.");
               text "Two definitions cannot share one external name."; ]
           | _ -> ());
          (match HashTable.try_find taken tgt with
           | Some other when check && other <> src ->
             E.raise_error0 E.Error_CustardExportCollision [
               text ("Custard: --custard_c_no_prefix would name " ^ src ^
                     " `" ^ tgt ^ "', which is already the name of " ^
                     other ^ ".");
               text "Rename one of them, or drop the option for this \
module."; ]
           | _ -> ());
          HashTable.add claimed tgt src;
          HashTable.add !renames src tgt
        end
      | _ -> ());
    (* A module named but contributing nothing is almost always a typo or a
       forgotten --custard_entry_module, and silence there costs a round. *)
    mods |> List.iter (fun m ->
      if check && None? (HashTable.try_find used_mod m) then
        E.log_issue0 E.Warning_CustardNoPublicDefinitions [
          text ("Custard: --custard_c_no_prefix " ^ m ^ " renamed nothing.");
          text "The option applies to types, to assume vals, and to \
definitions with external linkage.  Name the module with \
--custard_entry_module, or its definitions with --custard_entry, so that \
they are part of this unit's interface."; ])
  end

let foreign_targets (cu:unit_info) (p:program) : ML (list (string & string)) =
  reset_program_state ();
  (* Binding adoption can change these names; validate only the final program. *)
  build_renames false cu.cu_no_prefix p;
  p |> List.collect (function
    | DExternal x -> [(string_of_name x.dx_name, emitted_name (DExternal x))]
    | _ -> [])

(* Two program names that C spells the same way.  [sanitize] is not
   injective -- [mk_comp'] and [mk_comp_] are both [mk_comp_] -- and no choice
   of escape makes it so, since whatever ['] becomes is also an identifier
   someone can write.  A definition with internal linkage has a name nothing
   outside this file can see, so when its spelling is already claimed it is
   renamed through {!renames} to the first free [name_1], [name_2], ....

   Every other declaration keeps its name: an external's target and a public
   definition are spelled by the user or a consumer, an imported declaration
   by the unit that compiled it, and a type, constructor or macro is in the
   header.  Those are claimed first, so that a static definition never takes
   one of their names, and a clash between two of them is still error 374 in
   {!check_emitted_names}.  Runs after {!build_renames} and before the names
   are seeded into {!taken_names}. *)
let rename_clashes (init_name:string) (p:program) : ML unit =
  let movable (d:decl) : ML bool =
    local d && None? (extern_target d) && None? (requested_c_name d) &&
    (match d with
     | DLet l -> not (is_public l) && not (is_macro l)
     | _ -> false) in
  let wanted : HashTable.t string bool = HashTable.create 50 in
  p |> List.iter (fun d -> HashTable.add wanted (emitted_name d) true);
  HashTable.add wanted init_name true;
  let claimed : HashTable.t string bool = HashTable.create 50 in
  HashTable.add claimed init_name true;
  p |> List.iter (fun d ->
    if not (movable d) then HashTable.add claimed (emitted_name d) true);
  p |> List.iter (fun d ->
    if movable d then begin
      let nm = emitted_name d in
      if None? (HashTable.try_find claimed nm)
      then HashTable.add claimed nm true
      else begin
        let rec fresh (i:int) : ML string =
          let cand = nm ^ "_" ^ string_of_int i in
          if Some? (HashTable.try_find wanted cand) ||
             Some? (HashTable.try_find claimed cand)
          then fresh (i + 1) else cand in
        let nm' = fresh 1 in
        HashTable.add !renames (string_of_name (name_of_decl d)) nm';
        HashTable.add claimed nm' true
      end
    end)

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
(* Section 68.  The macro spellings, computed once {!build_renames} has settled
   what each declaration is called.  Uppercased, because that is what karamel
   does (GlobalNames.ml) and the whole point of the attribute is that a
   consumer's existing C compiles against either pipeline's header.

   Uppercasing is not injective and a macro has no scope, so it can capture a
   name that was fine before; both are collisions and both are reported here
   rather than being left to the C compiler, which would see only the token
   after substitution. *)
let build_macros (p:program) : ML unit =
  macros := HashTable.create 0;
  let ms = p |> List.collect (fun d ->
    match d with
    | DLet l when is_macro l -> [(l.dl_name, requested_c_name d)]
    | _ -> []) in
  if Nil? ms then () else begin
    (* Every other C name in the unit, so that a macro landing on one is
       caught: after substitution that name is no longer spellable. *)
    let taken : HashTable.t string string = HashTable.create 50 in
    p |> List.iter (fun d ->
      let n = name_of_decl d in
      if List.existsb (fun (m, _) -> string_of_name m = string_of_name n) ms
      then ()
      else HashTable.add taken (c_name n) (string_of_name n));
    ms |> List.iter (fun (n, requested) ->
      let m = match requested with
              | Some s -> s
              | None -> String.uppercase (c_name n) in
      let clash =
        match HashTable.try_find taken m with
        | Some o -> Some o
        | None -> HashTable.try_find !macros m in
      match clash with
      | Some o ->
        E.raise_error0 E.Error_CustardExportCollision [
          text ("Custard: the macro for " ^ string_of_name n ^ " is " ^ m ^
                ", which is already the C name of " ^ o ^ ".");
          text "A [@@ CMacro ] definition is spelled in upper case unless \
                rename_let specifies its name, and the preprocessor rewrites \
                that token everywhere \
                in the translation unit -- including in the other \
                declaration, which would then be unspellable.";
          text "Rename one of the two, or drop the attribute." ]
      | None ->
        HashTable.add !macros (string_of_name n) m;
        (* The inverse direction, for the next iteration's collision test. *)
        HashTable.add !macros m (string_of_name n))
  end;
  (* The reverse entries were bookkeeping for the loop above; a lookup is by
     the F* name, so rebuild without them. *)
  let final : HashTable.t string string = HashTable.create 20 in
  p |> List.iter (fun d ->
    match d with
    | DLet l when is_macro l ->
      (match HashTable.try_find !macros (string_of_name l.dl_name) with
       | Some m -> HashTable.add final (string_of_name l.dl_name) m
       | None -> ())
    | _ -> ());
  macros := final

(* Section 70.2.  A reference binding fixes the case the attribute is about --
   a local bound from an lvalue -- and there is one place left where a copy of
   a handle can still lose a write: a parameter of a function Custard compiles
   itself, which is a by-value binding with no lvalue to alias.  An external's
   parameters are not this: the declaration is in a header Custard does not
   write, and whether it takes a reference is that header's business.

   A warning rather than an error, because a copy is sometimes what is wanted
   -- a function that only reads its argument is fine -- and because refusing
   would make the attribute unusable on any type that is also passed around.
   What it must not be is silent. *)
let check_reference_copies (p:program) : ML unit =
  p |> List.iter (function
    | DLet l ->
      l.dl_binders |> List.iter (fun b ->
        if binds_by_ref b.b_ty then
          E.log_issue0 E.Warning_CustardReferenceCopied [
            text ("Custard: " ^ string_of_name l.dl_name ^ " takes " ^
                  b.b_name ^ " at the type `" ^ base_ty b.b_ty ^
                  "', whose values are handles, and a parameter is a copy.");
            text "A write the callee makes through it is made to the copy and \
                  is lost when the call returns.  [@@custard_c_reference] \
                  binds a *local* by reference; it does not change a \
                  signature, because a reference parameter would then refuse \
                  every argument that is not an lvalue.";
            text "If the callee only reads the argument this is fine.  If it \
                  writes, pass the container and the index instead, or make \
                  the callee external." ])
    | _ -> ())

let check_interface_names (p:program) : ML unit =
  let rec spec_names (c:cty) : ML (list name) =
    match c with
    | TArrow (a, _, b) -> spec_names a @ spec_names b
    | TTuple cs -> cs |> List.collect spec_names
    | TBuf c | TRef (_, c) | TInline c -> spec_names c
    | TApp (n, args) ->
      (if Some? n.spec then [n] else []) @ (args |> List.collect spec_names)
    | _ -> [] in
  let declared : HashTable.t string bool = HashTable.create 50 in
  p |> List.iter (function
    | DType t -> HashTable.add declared (string_of_name t.dt_name) true
    | _ -> ());
  (* Section 70.1.  A generated name that the unit *also* publishes an
     abbreviation for is a different situation from one it does not: the
     stable spelling the warning is about to ask for is already in this very
     header, and telling a reader to write their own would send them past it.
     So name it instead. *)
  let aliases : HashTable.t string string = HashTable.create 20 in
  p |> List.iter (function
    | DType t ->
      (match t.dt_body with
       | TAbbrev (TApp (n, [])) when Nil? t.dt_params && None? t.dt_name.spec ->
         HashTable.add aliases (string_of_name n) (c_name t.dt_name)
       | _ -> ())
    | _ -> ());
  let seen : HashTable.t string bool = HashTable.create 10 in
  p |> List.iter (function
    | DLet l when is_public l ->
      let sig_ctys = (l.dl_binders |> List.map (fun b -> b.b_ty)) @ [l.dl_ret] in
      sig_ctys |> List.collect spec_names |> List.iter (fun n ->
        let s = string_of_name n in
        if Some? (HashTable.try_find declared s) && None? (HashTable.try_find seen s)
        then begin
          HashTable.add seen s true;
          E.log_issue0 E.Warning_CustardGeneratedNameInInterface [
            text ("Custard: the type `" ^ c_name n ^
                  "' is part of this unit's interface -- " ^
                  string_of_name l.dl_name ^
                  " has it in its signature -- but its name is generated.");
            text "It is a specialization, so the name carries a hint built from the monomorphizer's input and may change when that input does. --custard_c_no_prefix does not rename specializations.";
            (match HashTable.try_find aliases s with
             | Some alias ->
               text ("This header already publishes `" ^ alias ^
                     "' as another name for it; spell that instead.")
             | None ->
               text "A consumer that must spell it should typedef it once, in its own header, rather than depend on this name throughout."); ]
        end)
    | _ -> ())

(* Section 117.3.  Two declarations that the generated file spells the same
   way.

   The backend mints C names in several places -- [c_name] from an F* lid, an
   [@@custard_extern] target taken verbatim, a [--custard_c_no_prefix] rename,
   the [<unit>_init_globals] initializer -- and until section 117 each of them
   decided on its own whether the name it wanted was free.  {!alloc_name} and
   {!build_renames} now consult one table, which is what keeps the *generated*
   names out of each other's way; this is the other half, and it is about the
   names the program itself supplies.  {!rename_clashes} renames the static
   definitions among those; the rest cannot be renamed, so the only thing to
   do with a collision is to say so.

   Worth an error rather than leaving it to the C compiler because C does not
   always catch it.  A definition with external linkage that lands on an
   external's target produces a file that *defines* a symbol the program had
   declared foreign: gcc -Wall -Wextra says nothing, the link succeeds, the
   archive member is never pulled in, and the program silently runs the wrong
   body.  That is the whole point of the attribute inverted -- naming a symbol
   the program does not own -- so it is caught here instead. *)
let check_emitted_names (init_name:string) (p:program) : ML unit =
  let seen : HashTable.t string (string & bool) = HashTable.create 50 in
  let claim (nm:string) (who:string) (ext:bool) : ML unit =
    match HashTable.try_find seen nm with
    (* Two externals reaching one target is not this check's business: it is
       legitimate when the two agree, and section 53.3's own check below --
       which has both prototypes to compare and better advice to give -- owns
       the case where they do not. *)
    | Some (other, ext') when other <> who && not (ext && ext') ->
      E.raise_error0 E.Error_CustardExportCollision (
        [ text ("Custard: " ^ other ^ " and " ^ who ^ " are both named `" ^
                nm ^ "' in the generated C.");
          text "Two declarations cannot share one C name." ] @
        (if ext || ext' then
           [ text "A name given by [@@custard_extern] is taken verbatim and names a symbol outside this program, so a definition that lands on it would take that symbol over -- with no diagnostic from the C compiler and no link error, because the definition simply wins." ]
         else []))
    | _ -> HashTable.add seen nm (who, ext) in
  (* Only when there is one: the initializer is emitted only for a unit that
     has a global to set up, and a name nothing prints cannot collide. *)
  if Cons? (global_inits_of p) then
    claim init_name "the generated initializer" false;
  p |> List.iter (fun d ->
    let n = name_of_decl d in
    claim (emitted_name d) (string_of_name n) (Some? (extern_target d));
    match d with
    | DType { dt_body = TVariant cs } ->
      cs |> List.iter (fun (c, _) -> claim (c_tag c) (string_of_name c) false)
    | _ -> ())

(* [base] is the stem of the output file: the source includes [base.h], and
   the include guard is derived from it.  Returns the header and the source,
   in that order. *)
(* Section 31.2.  Breadth-first from the roots, recording who first reached
   each declaration, so that walking back up gives a shortest chain.  A
   constructor is reached as its own type, which is how {!Simplify.dce}
   resolves it too. *)
let record_parents (p:program) : ML unit =
  let defs : HashTable.t string decl = HashTable.create 50 in
  let own : HashTable.t string string = HashTable.create 50 in
  let _ = p |> List.iter (fun d ->
    HashTable.add defs (string_of_name (name_of_decl d)) d;
    match d with
    | DType t ->
      (match t.dt_body with
       | TVariant cs ->
         cs |> List.iter (fun (cn, _) ->
                 HashTable.add own (string_of_name cn) (string_of_name t.dt_name))
       | _ -> ())
    | _ -> ()) in
  let resolve (n:string) : ML string =
    match HashTable.try_find own n with Some o -> o | None -> n in
  let seen : HashTable.t string bool = HashTable.create 50 in
  let rec bfs (front:list string) : ML unit =
    match front with
    | [] -> ()
    | _ ->
      let next = front |> List.collect (fun n ->
        match HashTable.try_find defs n with
        | None -> []
        | Some d ->
          Simplify.decl_deps d |> List.collect (fun c ->
            let c = resolve c in
            if c = n || Some? (HashTable.try_find seen c) then []
            else (HashTable.add seen c true; HashTable.add parents c n; [c]))) in
      bfs next in
  let rec ty_names (t:cty) (acc:list string) : ML (list string) =
    match t with
    | TApp (n, args) ->
      List.fold_right ty_names args (string_of_name n :: acc)
    | TArrow (a, _, b) -> ty_names a (ty_names b acc)
    | TBuf e | TRef (_, e) | TInline e -> ty_names e acc
    | TTuple ts -> List.fold_right ty_names ts acc
    | _ -> acc in
  let _ = p |> List.iter (fun d ->
    match d with
    | DExternal x ->
      ty_names x.dx_ty [] |> List.iter (fun tn ->
        if None? (HashTable.try_find frozen_by tn)
        then (HashTable.add frozen_by tn (string_of_name x.dx_name);
              match x.dx_target with
              | Some t -> HashTable.add frozen_by_target tn t
              | None -> ()))
    | _ -> ()) in
  let roots = p |> List.collect (fun d ->
    if decl_flags d |> List.existsb (fun f -> Root? f || Entrypoint? f)
    then (let n = string_of_name (name_of_decl d) in
          HashTable.add seen n true; HashTable.add root_decls n true; [n])
    else []) in
  bfs roots

(* -------------------------------------------------------------------- *)
(* Cherry runtime support and generated helpers                         *)
(* -------------------------------------------------------------------- *)

(* The constructors, and [inc]/[dec]/[mark] for every non-plain type.  All
   [static inline]: a unit uses some of them, and C warns about an unused
   [static] function that is not [inline].  Split output is the exception
   ([fn_out]). *)
let cherry_helpers (p:program) : ML (list string & list string & list (string & string)) =
  let protos : ref (list string) = mk_ref [] in
  let defs : ref (list string) = mk_ref [] in
  let homed : ref (list (string & string)) = mk_ref [] in
  let fn (proto:string) (body:string) : ML unit =
    protos := !protos @ [proto ^ ";\n"];
    defs := !defs @ [proto ^ " {\n" ^ body ^ "}\n"] in
  (* The constructors some record update builds ([Update]). *)
  let updated : HashTable.t string bool = HashTable.create 16 in
  let rec scan (e:expr) : ML unit =
    (match e.e with
     | EOp ({ po_op = Update (cn, _) }, _) ->
       if not (HashTable.mem updated (string_of_name cn))
       then HashTable.add updated (string_of_name cn) true
     | _ -> ());
    iter_children scan e in
  p |> List.iter (fun d -> match d with DLet l -> scan l.dl_body | _ -> ());
  (* A helper reached only through a function pointer or off the hot path.
     Split output defines it once, in the file of the module [home] of a
     type this unit declares, and declares it in the files that use it;
     otherwise it is [static inline] like the rest. *)
  let fn_out (home:option string) (proto:string) (body:string) : ML unit =
    match home with
    | Some m when !split_out ->
      protos := !protos @ [proto ^ ";\n"];
      homed := (m, proto ^ " {\n" ^ body ^ "}\n") :: !homed
    | _ -> fn ("static inline " ^ proto) body in
  (* The statements performing [op] on the counted fields of one value. *)
  let on_fields (op:string) (ind:string) (fs:list (string & cty))
                (sel:string -> ML string) : ML string =
    String.concat "" (fs |> List.collect (fun (f, t) ->
      if is_nonplain_ty t then [ind ^ rc_call op t (sel f) ^ ";\n"] else [])) in
  let has_counted (fs:list (string & cty)) : ML bool =
    fs |> List.existsb (fun (_, t) -> is_nonplain_ty t) in
  p |> List.iter (fun d ->
    match d with
    (* An imported type too: its cell structs and tags are in its unit's
       header, and the helpers are [static], so each unit has its own. *)
    | DType dt when is_nonplain_ty (TApp (dt.dt_name, [])) &&
                    not (is_runtime_name dt.dt_name) ->
      current := string_of_name dt.dt_name;
      let n = c_name dt.dt_name in
      let home = if local d then Some (module_of dt.dt_name) else None in
      (match dt.dt_body with
       | TVariant cs when is_boxed dt ->
         cs |> List.iter (fun (c, fs) ->
           if Cons? fs then begin
             let cell = cell_struct dt c in
             let params = fs |> List.mapi (fun i (_, t) -> decl_of t ("a" ^ string_of_int i)) in
             fn ("static inline " ^ n ^ " " ^ cell_new dt c ^ "(" ^ String.concat ", " params ^ ")")
                ("  " ^ cell ^ " *c = (" ^ cell ^ " *)cherry_alloc(sizeof(" ^ cell ^ "), " ^
                 c_tag c ^ ");\n" ^
                 String.concat "" (fs |> List.mapi (fun i (f, _) ->
                   "  c->" ^ c_var f ^ " = a" ^ string_of_int i ^ ";\n")) ^
                 "  return (" ^ n ^ ")c;\n");
             (* Constructor [c] in the memory of a token from a cell of
                [cap] bytes, if there is one and it fits (cherry.md). *)
             fn ("static inline " ^ n ^ " cherry_reuse_" ^ n ^ "_" ^ arm_name c ^
                 "(cherry_obj *w, size_t cap, " ^ String.concat ", " params ^ ")")
                ("  " ^ cell ^ " *c;\n" ^
                 "  if (w != NULL && sizeof(" ^ cell ^ ") <= cap) {\n" ^
                 "    c = (" ^ cell ^ " *)w;\n" ^
                 "    ((cherry_obj *)c)->tag = " ^ c_tag c ^ ";\n" ^
                 "  } else {\n" ^
                 "    free(w);\n" ^
                 "    c = (" ^ cell ^ " *)cherry_alloc(sizeof(" ^ cell ^ "), " ^ c_tag c ^ ");\n" ^
                 "  }\n" ^
                 String.concat "" (fs |> List.mapi (fun i (f, _) ->
                   "  c->" ^ c_var f ^ " = a" ^ string_of_int i ^ ";\n")) ^
                 "  return (" ^ n ^ ")c;\n");
             (* A cell of [c] that this thread alone holds, for a record
                update to change: [x] itself if it is unique, and otherwise a
                copy, with its fields counted, which takes [x]'s place.  The
                copy is out of line, so that each update is only the test. *)
             if HashTable.mem updated (string_of_name c) then begin
               let copy = "cherry_copy_" ^ n ^ "_" ^ arm_name c in
               fn (helper_static () ^ n ^ " " ^ copy ^ "(" ^ n ^ " x)")
                  ("  " ^ cell ^ " *o = (" ^ cell ^ " *)x;\n" ^
                   "  " ^ cell ^ " *c = (" ^ cell ^ " *)cherry_alloc(sizeof(" ^ cell ^ "), " ^
                   c_tag c ^ ");\n" ^
                   String.concat "" (fs |> List.map (fun (f, _) ->
                     "  c->" ^ c_var f ^ " = o->" ^ c_var f ^ ";\n")) ^
                   on_fields "inc" "  " fs (fun f -> "c->" ^ c_var f) ^
                   "  " ^ rc_call "dec" (TApp (dt.dt_name, [])) "x" ^ ";\n" ^
                   "  return (" ^ n ^ ")c;\n");
               fn ("static inline " ^ n ^ " " ^ cell_unshare dt c ^ "(" ^ n ^ " x)")
                  ("  return cherry_is_unique(x) ? x : " ^ copy ^ "(x);\n")
             end
           end);
         (* The visit of a cell's fields (cherry.h, [cherry_defer]): [op] on
            each counted field, except the last one of this very type, which
            the visit goes on to itself. *)
         let is_self (t:cty) : ML bool =
           match t with TApp (m, []) -> c_name m = n | _ -> false in
         let cases (op:string) : ML string =
           "    switch (x->tag) {\n" ^
           String.concat "" (cs |> List.collect (fun (c, fs) ->
             if not (has_counted fs) then [] else
             let cell = cell_struct dt c in
             let next = fs |> List.filter (fun (_, t) -> is_self t)
                           |> List.rev |> List.map fst in
             let others = (match next with
                           | f :: _ -> fs |> List.filter (fun (g, _) -> g <> f)
                           | [] -> fs) in
             ["      case " ^ c_tag c ^ ": {\n" ^
              "        " ^ cell ^ " *c = (" ^ cell ^ " *)x;\n" ^
              on_fields op "        " others (fun f -> "c->" ^ c_var f) ^
              (match next with
               | f :: _ -> "        next = c->" ^ c_var f ^ ";\n"
               | [] -> "") ^
              "        break;\n      }\n"])) ^
           "      default: break;\n    }\n" in
         let counted = cs |> List.existsb (fun (_, fs) -> has_counted fs) in
         if not counted then begin
           fn ("static inline void cherry_dec_" ^ n ^ "(" ^ n ^ " x)")
              "  if (cherry_dec_ref(x)) free(x);\n";
           fn ("static inline void cherry_mark_" ^ n ^ "(" ^ n ^ " x, int m)")
              "  (void)cherry_mark_ref(x, m);\n"
         end else begin
           fn_out home ("void cherry_free_" ^ n ^ "(cherry_obj *x, int m)")
              ("  (void)m;\n  for (;;) {\n    " ^ n ^ " next = CHERRY_SCALAR(0);\n" ^
               cases "dec" ^
               "    free(x);\n    if (!cherry_dec_ref(next)) return;\n    x = next;\n  }\n");
           fn_out home ("void cherry_markf_" ^ n ^ "(cherry_obj *x, int m)")
              ("  for (;;) {\n    " ^ n ^ " next = CHERRY_SCALAR(0);\n" ^
               cases "mark" ^
               "    if (!cherry_mark_ref(next, m)) return;\n    x = next;\n  }\n");
           fn ("static inline void cherry_dec_" ^ n ^ "(" ^ n ^ " x)")
              ("  if (cherry_dec_ref(x)) cherry_defer(x, cherry_free_" ^ n ^ ", 0);\n");
           fn_out home ("void cherry_mark_" ^ n ^ "(" ^ n ^ " x, int m)")
              ("  if (cherry_mark_ref(x, m)) cherry_defer(x, cherry_markf_" ^ n ^ ", m);\n")
         end
       | _ ->
         let body (op:string) : ML string =
           "  (void)x;\n" ^
           (match dt.dt_body with
            | TAbbrev t -> "  " ^ rc_call op t "x" ^ ";\n"
            | TRecord fs -> on_fields op "  " fs (fun f -> "x." ^ c_var f)
            | TVariant [(_, fs)] -> on_fields op "  " fs (fun f -> "x." ^ c_var f)
            | TVariant cs ->
              "  switch (x.tag) {\n" ^
              String.concat "" (cs |> List.collect (fun (c, fs) ->
                if not (has_counted fs) then [] else
                ["    case " ^ c_tag c ^ ":\n" ^
                 on_fields op "      " fs (fun f -> "x" ^ arm_sel c fs f) ^
                 "      break;\n"])) ^
              "    default: break;\n  }\n"
            | TAbstract -> "") in
         ["inc"; "dec"] |> List.iter (fun op ->
           fn ("static inline void cherry_" ^ op ^ "_" ^ n ^ "(" ^ n ^ " x)") (body op));
         fn_out home ("void cherry_mark_" ^ n ^ "(" ^ n ^ " x, int m)")
           ("  (void)m;\n" ^ body "mark"))
    | _ -> ());
  (!protos, !defs, List.rev !homed)

(* The ML reference cells used while printing, and the operations on them
   (cherry.h): the cell structs and prototypes, and the definitions.  A
   value type that is itself a reference adds to the list as it goes. *)
let cherry_ref_helpers () : ML (list string & list string) =
  let protos = mk_ref [] in
  let defs = mk_ref [] in
  let rec go (i:int) : ML unit =
    if i >= List.length !ref_tys then () else begin
      let t = List.nth !ref_tys i in
      let p = "cherry_ref" ^ string_of_int i in
      let s = "struct " ^ p ^ "_s" in
      let counted = is_nonplain_ty t in
      let when_counted (c:string) : string = if counted then c else "" in
      let sigs = [
        "static inline cherry_ref " ^ p ^ "_new(" ^ decl_of t "v" ^ ")";
        "static inline " ^ decl_of t (p ^ "_get(cherry_ref r)");
        "static inline void " ^ p ^ "_set(cherry_ref r, " ^ decl_of t "v" ^ ")";
        "static inline void " ^ p ^ "_dec(cherry_ref r)";
        "static inline void " ^ p ^ "_mark(cherry_ref r, int m)";
        "static inline void " ^ p ^ "_free(cherry_obj *r, int m)";
        "static inline void " ^ p ^ "_markf(cherry_obj *r, int m)" ] in
      let op (o:string) (x:string) : ML string =
        if counted then "  " ^ rc_fn o t ^ "(" ^ x ^ ");\n" else "" in
      let cell = "  " ^ s ^ " *c = (" ^ s ^ " *)r;\n" in
      let bodies = [
        "  " ^ s ^ " *c = (" ^ s ^ " *)cherry_alloc(sizeof(" ^ s ^ "), 0);\n" ^
        "  c->h.lock = 0;\n  c->v = v;\n  return (cherry_ref)c;\n";
        cell ^
        "  if (cherry_ref_is_local(r)) {\n" ^ op "inc" "c->v" ^ "  return c->v;\n  }\n" ^
        "  cherry_ref_lock(r);\n  " ^ decl_of t "x" ^ " = c->v;\n" ^ op "inc" "x" ^
        "  cherry_ref_unlock(r);\n  return x;\n";
        (* The old value is read only where no other thread can write it:
           in a local cell, or under the lock. *)
        cell ^
        when_counted ("  " ^ decl_of t "old" ^ ";\n") ^
        "  if (cherry_ref_is_local(r)) {\n" ^ when_counted ("  old = c->v;\n") ^
        "  c->v = v;\n" ^ op "dec" "old" ^ "  return;\n  }\n" ^
        (if counted then "  " ^ rc_fn "mark" t ^ "(v, CHERRY_SHARE);\n" else "") ^
        "  cherry_ref_lock(r);\n" ^
        when_counted ("  old = c->v;\n") ^
        "  c->v = v;\n  cherry_ref_unlock(r);\n" ^ op "dec" "old";
        (if counted then "  if (cherry_dec_ref(r)) cherry_defer(r, " ^ p ^ "_free, 0);\n"
         else "  if (cherry_dec_ref(r)) free(r);\n");
        (if counted then "  if (cherry_mark_ref(r, m)) cherry_defer(r, " ^ p ^ "_markf, m);\n"
         else "  (void)cherry_mark_ref(r, m);\n");
        "  (void)m;\n" ^ (if counted then cell ^ op "dec" "c->v" else "") ^ "  free(r);\n";
        "  (void)r; (void)m;\n" ^
        (if counted then cell ^ "  " ^ rc_fn "mark" t ^ "(c->v, m);\n" else "") ] in
      protos := !protos @
        [s ^ " { cherry_ref_hdr h; " ^ decl_of t "v" ^ "; };\n" ^
         String.concat "" (sigs |> List.map (fun g -> g ^ ";\n"))];
      defs := !defs @ List.map2 (fun g b -> g ^ " {\n" ^ b ^ "}\n") sigs bodies;
      go (i + 1)
    end in
  go 0;
  (!protos, !defs)

(* The immutable arrays used while printing (cherry.h), one per element
   type: the cell struct, and the operations on it.  [upd] and [push] take
   the array owned and change it in place when it is unique, growing a full
   one geometrically; otherwise they copy it. *)
let cherry_exn_helpers (p:program) : ML (list string & list string) =
  let one (x:dexn) : ML (list string & list string) =
    let n = x.de_name in
    let fs = Some?.v (find_exn n) in
    let cn = c_name n in
    let st = exn_struct n in
    let params = fs |> List.map (fun (f, t) -> decl_of t f) in
    let ctor_sig = "static inline cherry_exn " ^ exn_new n ^ "(" ^
                   (if Nil? params then "void" else String.concat ", " params) ^ ")" in
    let on (op:string) : ML string =
      String.concat "" (fs |> List.collect (fun (f, t) ->
        if is_nonplain_ty t then ["  " ^ rc_call op t ("c->" ^ f) ^ ";\n"] else [])) in
    let protos =
      [st ^ " { cherry_exn_hdr hdr;" ^
       String.concat "" (fs |> List.map (fun (f, t) -> " " ^ decl_of t f ^ ";")) ^ " };\n";
       helper_static () ^ "void " ^ cn ^ "_exn_free(cherry_obj *x, int m);\n";
       helper_static () ^ "void " ^ cn ^ "_exn_markf(cherry_obj *x, int m);\n";
       unique_object ("const cherry_exn_info " ^ exn_info n)
         ("{ \"" ^ string_of_name n ^
          "\", " ^ cn ^ "_exn_free, " ^ cn ^ "_exn_markf, " ^
          (match fs with
           | (f, TApp ({ ns = ["Prims"]; id = "string" }, [])) :: _ ->
             "offsetof(" ^ st ^ ", " ^ f ^ ")"
           | _ -> "0") ^ " }");
       ctor_sig ^ ";\n"] in
    let defs =
      [helper_static () ^ "void " ^ cn ^ "_exn_free(cherry_obj *x, int m) {\n" ^
       "  " ^ st ^ " *c = (" ^ st ^ " *)x;\n  (void)c; (void)m;\n" ^ on "dec" ^ "  free(x);\n}\n";
       helper_static () ^ "void " ^ cn ^ "_exn_markf(cherry_obj *x, int m) {\n" ^
       "  " ^ st ^ " *c = (" ^ st ^ " *)x;\n  (void)c; (void)m;\n" ^ on "mark" ^ "}\n";
       ctor_sig ^ " {\n" ^
       "  " ^ st ^ " *c = (" ^ st ^ " *)cherry_alloc(sizeof(" ^ st ^ "), CHERRY_TAG_EXN);\n" ^
       "  c->hdr.info = &" ^ exn_info n ^ ";\n" ^
       String.concat "" (fs |> List.map (fun (f, _) -> "  c->" ^ f ^ " = " ^ f ^ ";\n")) ^
       "  return (cherry_exn)c;\n}\n"] in
    protos, defs in
  let rs = p |> List.collect (fun d -> match d with
                 | DExn x when Some? (find_exn x.de_name) -> [one x]
                 | _ -> []) in
  List.collect fst rs, List.collect snd rs

(* For each type a [dyn] is made of or read at: its type information, and
   [mk] and [get].  Whether the value fits in the word is the C compiler's
   to decide, as a constant condition. *)
let cherry_any_helpers () : ML (list string & list string) =
  let one (i:int) (t:cty) : ML (list string & list string) =
    let p = "cherry_any" ^ string_of_int i in
    let ct = decl_of t "" in
    let cell = "struct " ^ p ^ "_s" in
    let small = "(sizeof(" ^ ct ^ ") <= sizeof(uintptr_t))" in
    let np = is_nonplain_ty t in
    let op (o:string) (x:string) : ML string = rc_call o t x in
    let unpack = "    " ^ decl_of t "x" ^ ";\n    memcpy(&x, &v, sizeof x);\n" in
    let protos =
      [cell ^ " { cherry_obj h; " ^ decl_of t "v" ^ "; };\n";
       helper_static () ^ "void " ^ p ^ "_inc(uintptr_t v);\n";
       helper_static () ^ "void " ^ p ^ "_dec(uintptr_t v);\n";
       helper_static () ^ "void " ^ p ^ "_mark(uintptr_t v, int m);\n";
       unique_object ("const cherry_rtti " ^ p ^ "_rtti")
         ("{ \"" ^ ct ^ "\", " ^ p ^ "_inc, " ^ p ^ "_dec, " ^ p ^ "_mark }");
       "static inline cherry_any " ^ p ^ "_mk(" ^ decl_of t "x" ^ ");\n";
       "static inline " ^ decl_of t (p ^ "_get(cherry_any a)") ^ ";\n"] in
    (* A plain value in a box still has the box to free. *)
    let free_body =
      helper_static () ^ "void " ^ p ^ "_free(cherry_obj *o, int m) {\n  (void)m;\n" ^
      (if np then "  " ^ op "dec" ("((" ^ cell ^ " *)o)->v") ^ ";\n" else "") ^
      "  free(o);\n}\n" in
    let defs =
      [free_body;
       helper_static () ^ "void " ^ p ^ "_dec(uintptr_t v) {\n" ^
       "  if " ^ small ^ " {\n" ^
       (if np then unpack ^ "    " ^ op "dec" "x" ^ ";\n" else "") ^
       "  } else {\n" ^
       "    cherry_obj *o = (cherry_obj *)v;\n" ^
       "    if (cherry_dec_ref(o)) cherry_defer(o, " ^ p ^ "_free, 0);\n  }\n}\n"] @
      (* A plain payload too big for the word is still in a counted box,
         which has to be counted and marked even though its contents are
         not. *)
      [helper_static () ^ "void " ^ p ^ "_inc(uintptr_t v) {\n" ^
       "  if " ^ small ^ " {\n" ^
       (if np then unpack ^ "    " ^ op "inc" "x" ^ ";\n" else "") ^
       "  } else cherry_inc((cherry_obj *)v);\n}\n"] @
      (if np then
        [helper_static () ^ "void " ^ p ^ "_markf(cherry_obj *o, int m) {\n" ^
         "  " ^ op "mark" ("((" ^ cell ^ " *)o)->v") ^ ";\n}\n"]
       else []) @
      [helper_static () ^ "void " ^ p ^ "_mark(uintptr_t v, int m) {\n" ^
       "  if " ^ small ^ " {\n" ^
       (if np then unpack ^ "    " ^ op "mark" "x" ^ ";\n" else "    (void)m;\n") ^
       "  } else {\n    cherry_obj *o = (cherry_obj *)v;\n" ^
       (if np then "    if (cherry_mark_ref(o, m)) cherry_defer(o, " ^ p ^ "_markf, m);\n"
        else "    (void)cherry_mark_ref(o, m);\n") ^
       "  }\n}\n"] @
      ["static inline cherry_any " ^ p ^ "_mk(" ^ decl_of t "x" ^ ") {\n" ^
       "  cherry_any a;\n  a.rtti = &" ^ p ^ "_rtti;\n" ^
       "  if " ^ small ^ " {\n    a.v = 0;\n    memcpy(&a.v, &x, sizeof x);\n" ^
       "  } else {\n" ^
       "    " ^ cell ^ " *c = (" ^ cell ^ " *)cherry_alloc(sizeof(" ^ cell ^ "), CHERRY_TAG_ANY);\n" ^
       "    c->v = x;\n    a.v = (uintptr_t)c;\n  }\n  return a;\n}\n";
       "static inline " ^ decl_of t (p ^ "_get(cherry_any a)") ^ " {\n" ^
       "  if (__builtin_expect(a.rtti != &" ^ p ^ "_rtti, 0)) cherry_any_mismatch(a.rtti, \"" ^ ct ^ "\");\n" ^
       "  " ^ decl_of t "x" ^ ";\n" ^
       "  if " ^ small ^ " memcpy(&x, &a.v, sizeof x);\n" ^
       "  else x = ((" ^ cell ^ " *)a.v)->v;\n" ^
       (if np then "  " ^ op "inc" "x" ^ ";\n" else "") ^
       "  return x;\n}\n"] in
    protos, defs in
  let rs = !any_tys |> List.mapi one in
  List.collect fst rs, List.collect snd rs

(* The helpers for the Pulse containers [pbuf_tys] lists (cherry.h, "Pulse
   references and arrays").  A value is marked shared when it is stored. *)
let cherry_pbuf_helpers () : ML (list string & list string) =
  let protos : ref (list string) = mk_ref [] in
  let defs : ref (list string) = mk_ref [] in
  let fn (proto:string) (body:string) : ML unit =
    protos := !protos @ [proto ^ ";\n"];
    defs := !defs @ [proto ^ " {\n" ^ body ^ "}\n"] in
  !pbuf_tys |> List.iteri (fun i t ->
    let p = "cherry_pbuf" ^ string_of_int i in
    let b = decl_of (TBuf t) "b" in
    let op (o:string) (x:string) : ML string = rc_fn o t ^ "(" ^ x ^ ");" in
    let share = "  " ^ rc_fn "mark" t ^ "(v, CHERRY_SHARE);\n" in
    let fill =
      share ^
      "  if (n == 0) { " ^ op "dec" "v" ^ " return; }\n" ^
      "  for (size_t j = 0; j < n; j++) b[j] = v;\n" ^
      "  for (size_t j = 1; j < n; j++) " ^ op "inc" "v" ^ "\n" in
    let drop = "  for (size_t j = 0; j < n; j++) " ^ op "dec" "b[j]" ^ "\n" in
    fn ("static inline void " ^ p ^ "_init(" ^ b ^ ", " ^ decl_of t "v" ^ ", size_t n)") fill;
    fn ("static inline " ^ decl_of (TBuf t) (p ^ "_alloc(" ^ decl_of t "v" ^ ", size_t n)"))
       ("  " ^ b ^ " = (" ^ ty (TBuf t) ^ ")cherry_pbuf_new(n, sizeof(b[0]));\n" ^
        "  " ^ p ^ "_init(b, v, n);\n  return b;\n");
    fn ("static inline " ^ decl_of t (p ^ "_read(" ^ b ^ ", size_t i)"))
       ("  " ^ decl_of t "x" ^ " = b[i];\n  " ^ op "inc" "x" ^ "\n  return x;\n");
    fn ("static inline void " ^ p ^ "_write(" ^ b ^ ", size_t i, " ^ decl_of t "v" ^ ")")
       (share ^ "  " ^ decl_of t "old" ^ " = b[i];\n  b[i] = v;\n  " ^ op "dec" "old" ^ "\n");
    fn ("static inline void " ^ p ^ "_drop(" ^ b ^ ", size_t n)") drop;
    fn ("static inline void " ^ p ^ "_free(" ^ b ^ ")")
       ("  size_t n = cherry_pbuf_len((void *)b);\n" ^ drop ^ "  cherry_pbuf_release((void *)b);\n");
    (* The source range gains its references before the destination range
       loses its own, so that an overlap never frees what is copied. *)
    fn ("static inline void " ^ p ^ "_blit(" ^ decl_of (TBuf t) "s" ^ ", size_t si, " ^ b ^ ", size_t di, size_t n)")
       ("  for (size_t j = 0; j < n; j++) " ^ op "inc" "s[si + j]" ^ "\n" ^
        "  for (size_t j = 0; j < n; j++) " ^ op "dec" "b[di + j]" ^ "\n" ^
        "  memmove(&b[di], &s[si], n * sizeof(b[0]));\n"));
  !protos, !defs

let cherry_iarr_helpers () : ML (list string & list string) =
  let protos : ref (list string) = mk_ref [] in
  let defs : ref (list string) = mk_ref [] in
  let fn (proto:string) (body:string) : ML unit =
    protos := !protos @ [proto ^ ";\n"];
    defs := !defs @ [proto ^ " {\n" ^ body ^ "}\n"] in
  (* An element type that is itself an array adds to the list as it goes. *)
  let rec go (i:int) : ML unit =
    if i >= List.length !iarr_tys then () else begin
    let t = List.nth !iarr_tys i in
    let p = "cherry_iarr" ^ string_of_int i in
    let s = "struct " ^ p ^ "_s" in
    let counted = is_nonplain_ty t in
    let op (o:string) (x:string) : ML string =
      if counted then rc_call o t x ^ ";" else "" in
    let cell (x:string) : string = s ^ " *" ^ x in
    (* Debug mode (cherry.h): F* has checked the index, lax code may not have. *)
    let bounds (f:string) : ML string =
      "  CHERRY_ASSUME(cherry_iarray_in_bounds(a, i), \"ImmutableArray." ^ f ^
      ": index out of bounds\");\n" in
    let copy =
      "  for (size_t j = 0; j < n; j++) { d->data[j] = c->data[j]; " ^ op "inc" "d->data[j]" ^ " }\n" in
    protos := !protos @ [s ^ " { cherry_iarray_hdr h; " ^ decl_of t "data[]" ^ "; };\n"];
    fn ("static inline cherry_iarray " ^ p ^ "_alloc(size_t n, size_t cap)")
       ("  if (cap > (SIZE_MAX - sizeof(" ^ s ^ ")) / sizeof(((" ^ s ^ " *)0)->data[0])) abort();\n" ^
        "  " ^ cell "c" ^ " = (" ^ s ^ " *)cherry_alloc(sizeof(" ^ s ^ ") + cap * sizeof(c->data[0]), CHERRY_TAG_IARRAY);\n" ^
        "  c->h.size = n;\n  c->h.cap = cap;\n  return (cherry_iarray)c;\n");
    fn ("static inline void " ^ p ^ "_free(cherry_obj *a, int m)")
       ("  (void)m;\n" ^
        (if counted then
           "  " ^ cell "c" ^ " = (" ^ s ^ " *)a;\n" ^
           "  for (size_t j = 0; j < c->h.size; j++) " ^ op "dec" "c->data[j]" ^ "\n"
         else "") ^
        "  free(a);\n");
    fn ("static inline void " ^ p ^ "_markf(cherry_obj *a, int m)")
       ("  (void)a; (void)m;\n" ^
        (if counted then
           "  " ^ cell "c" ^ " = (" ^ s ^ " *)a;\n" ^
           "  for (size_t j = 0; j < c->h.size; j++) " ^ op "mark" "c->data[j]" ^ "\n"
         else ""));
    fn ("static inline void " ^ p ^ "_dec(cherry_iarray a)")
       ("  if (cherry_dec_ref(a)) " ^
        (if counted then "cherry_defer(a, " ^ p ^ "_free, 0);\n" else "free(a);\n"));
    fn ("static inline void " ^ p ^ "_mark(cherry_iarray a, int m)")
       (if counted then "  if (cherry_mark_ref(a, m)) cherry_defer(a, " ^ p ^ "_markf, m);\n"
        else "  (void)cherry_mark_ref(a, m);\n");
    fn ("static inline " ^ decl_of t (p ^ "_index(cherry_iarray a, cherry_int i)"))
       (bounds "index" ^
        "  " ^ decl_of t "x" ^ " = ((" ^ s ^ " *)a)->data[cherry_iarray_pos(i)];\n" ^
        (if counted then "  " ^ op "inc" "x" ^ "\n" else "") ^ "  return x;\n");
    (* A shared or persistent array is copied, as is one with another
       reference: the copy takes a reference to every element, and the
       original is released after, so that no element dies in between. *)
    let unique_or_copy (cap:string) : string =
      "  " ^ cell "c" ^ " = (" ^ s ^ " *)a;\n" ^
      "  size_t n = c->h.size;\n" ^
      "  if (!cherry_is_unique(a)) {\n" ^
      "    " ^ cell "d" ^ " = (" ^ s ^ " *)" ^ p ^ "_alloc(n, " ^ cap ^ ");\n" ^
      "  " ^ copy ^
      "    " ^ p ^ "_dec(a);\n    c = d;\n  }\n" in
    fn ("static inline cherry_iarray " ^ p ^ "_upd(cherry_iarray a, cherry_int i, " ^ decl_of t "v" ^ ")")
       (bounds "upd" ^ unique_or_copy "n" ^
        "  size_t k = cherry_iarray_pos(i);\n" ^
        (if counted then "  " ^ decl_of t "old" ^ " = c->data[k];\n" else "") ^
        "  c->data[k] = v;\n" ^
        (if counted then "  " ^ op "dec" "old" ^ "\n" else "") ^
        "  return (cherry_iarray)c;\n");
    fn ("static inline cherry_iarray " ^ p ^ "_push(cherry_iarray a, " ^ decl_of t "v" ^ ")")
       (unique_or_copy "2 * n + 1" ^
        "  if (n == c->h.cap) {\n" ^
        "    size_t cap = 2 * n + 1;\n" ^
        "    c = (" ^ s ^ " *)realloc(c, sizeof(" ^ s ^ ") + cap * sizeof(c->data[0]));\n" ^
        "    if (c == NULL) abort();\n" ^
        "    c->h.cap = cap;\n  }\n" ^
        "  c->data[n] = v;\n  c->h.size = n + 1;\n  return (cherry_iarray)c;\n");
    (* Conversions from and to the list type, when one was used. *)
    (match List.tryFind (fun (j, _) -> j = i) !iarr_lists with
     | Some (_, lt) ->
       let ln = (match lt with
                 | TApp (ln, []) -> ln
                 | _ -> failwith "Cherry: an immutable array converted from or to a non-list type") in
       (match find_type ln with
        | Some d when TVariant? d.dt_body ->
          let cs = TVariant?._0 d.dt_body in
          let nil = cs |> List.tryFind (fun (_, fs) -> Nil? fs) in
          let cons = cs |> List.tryFind (fun (_, fs) -> List.length fs = 2) in
          (match nil, cons with
           | Some (nc, _), Some (cc, [(hd, _); (tl, _)]) ->
             let l = ty lt in
             let cs = cell_struct d cc in
             fn ("static inline cherry_iarray " ^ p ^ "_of_list(" ^ l ^ " l)")
                ("  size_t n = 0;\n" ^
                 "  for (" ^ l ^ " q = l; !cherry_is_scalar(q); q = ((" ^ cs ^ " *)q)->" ^ c_var tl ^ ") n++;\n" ^
                 "  " ^ cell "d" ^ " = (" ^ s ^ " *)" ^ p ^ "_alloc(n, n);\n" ^
                 "  size_t j = 0;\n" ^
                 "  for (" ^ l ^ " q = l; !cherry_is_scalar(q); q = ((" ^ cs ^ " *)q)->" ^ c_var tl ^ ") {\n" ^
                 "    d->data[j] = ((" ^ cs ^ " *)q)->" ^ c_var hd ^ ";\n" ^
                 (if counted then "    " ^ op "inc" "d->data[j]" ^ "\n" else "") ^
                 "    j++;\n  }\n  return (cherry_iarray)d;\n");
             fn ("static inline " ^ l ^ " " ^ p ^ "_to_list(cherry_iarray a)")
                ("  " ^ cell "c" ^ " = (" ^ s ^ " *)a;\n" ^
                 "  " ^ l ^ " r = CHERRY_SCALAR(" ^ c_tag nc ^ ");\n" ^
                 "  for (size_t j = c->h.size; j-- > 0;) {\n" ^
                 (if counted then "    " ^ op "inc" "c->data[j]" ^ "\n" else "") ^
                 "    r = " ^ cell_new d cc ^ "(c->data[j], r);\n  }\n  return r;\n")
           | _ -> failwith "Cherry: a list type without Nil and Cons")
        | _ -> failwith "Cherry: an immutable array converted from or to an unknown list type")
     | _ -> ());
    go (i + 1)
    end in
  go 0;
  (!protos, !defs)

(* The closure helpers requested while printing: declarations (the
   environment structs, prototypes and static closures) and definitions. *)
let cherry_closure_helpers () : ML (list string & list string) =
  let protos : ref (list string) = mk_ref [] in
  let defs : ref (list string) = mk_ref [] in
  let fn (proto:string) (body:string) : ML unit =
    protos := !protos @ [proto ^ ";\n"];
    defs := !defs @ [proto ^ " {\n" ^ body ^ "}\n"] in
  let nonunit (xs:list (string & cty)) : ML (list (string & cty)) =
    List.filter (fun (_, t) -> not (TUnit? t)) xs in
  let named (pfx:string) (from:int) (ts:list cty) : ML (list (string & cty)) =
    ts |> List.mapi (fun i t -> (pfx ^ string_of_int (from + i), t)) in
  let params (xs:list (string & cty)) : ML string =
    String.concat "" (nonunit xs |> List.map (fun (x, t) -> ", " ^ decl_of t x)) in
  let names (xs:list (string & cty)) : ML (list string) =
    nonunit xs |> List.map fst in
  (* The type of a closure's entry point taking [ts], as a cast. *)
  let code_ty (ret:cty) (ts:list cty) : ML string =
    "(" ^ decl_of ret ("(*)(cherry_fn" ^
      String.concat "" (ts |> List.filter (fun t -> not (TUnit? t))
                           |> List.map (fun t -> ", " ^ decl_of t "")) ^ ")") ^ ")" in
  let on (op:string) (sel:string) (xs:list (string & cty)) : ML string =
    String.concat "" (nonunit xs |> List.collect (fun (x, t) ->
      if is_nonplain_ty t then ["  " ^ rc_call op t (sel ^ x) ^ ";\n"] else [])) in
  (* Closure cells with the same fields (names, C types and reference
     counting) share their struct, [drop] and [mark] functions and constructor: the cell's entry
     point and arity are what tells them apart, and the constructor takes
     both. *)
  let layouts : HashTable.t string string = HashTable.create 100 in
  let layout (fields:list (string & cty)) : ML string =
    let key = String.concat ";" (fields |> List.map (fun (x, t) -> decl_of t x)) ^
              "|" ^ on "dec" "" fields ^ "|" ^ on "mark" "" fields in
    match HashTable.try_find layouts key with
    | Some s -> s
    | None ->
      let s = "cherry_envl_" ^ string_of_int (HashTable.size layouts) in
      HashTable.add layouts key s;
      protos := !protos @ ["struct " ^ s ^ " {\n  cherry_closure clo;\n" ^
        String.concat "" (fields |> List.map (fun (x, t) -> "  " ^ decl_of t x ^ ";\n")) ^ "};\n"];
      let counted = fields |> List.existsb (fun (_, t) -> is_nonplain_ty t) in
      let drop, mark =
        if not counted then "NULL", "NULL" else begin
          ["dec"; "mark"] |> List.iter (fun op ->
            fn ("static inline void " ^ s ^ "_" ^ op ^ "(cherry_obj *o" ^
                (if op = "mark" then ", int m" else "") ^ ")")
               ("  struct " ^ s ^ " *env = (struct " ^ s ^ " *)o;\n" ^ on op "env->" fields));
          s ^ "_dec", s ^ "_mark"
        end in
      fn ("static inline cherry_fn " ^ s ^ "_new(cherry_code cherry_entry, uint32_t cherry_arity" ^
          String.concat "" (fields |> List.map (fun (x, t) -> ", " ^ decl_of t x)) ^ ")")
         ("  struct " ^ s ^ " *env = (struct " ^ s ^ " *)cherry_alloc(sizeof(struct " ^ s ^
          "), CHERRY_TAG_CLOSURE);\n" ^
          "  env->clo.fn = cherry_entry;\n" ^
          "  env->clo.drop = " ^ drop ^ ";\n" ^
          "  env->clo.mark = " ^ mark ^ ";\n" ^
          "  env->clo.arity = cherry_arity;\n" ^
          String.concat "" (fields |> List.map (fun (x, _) -> "  env->" ^ x ^ " = " ^ x ^ ";\n")) ^
          "  return (cherry_fn)env;\n");
      s in
  (* A closure cell holding [fields], built by [ctor] taking them all owned,
     whose entry point [entry] is defined by [body]. *)
  let closure (fields:list (string & cty)) (arity:string)
              (entry:string) (ret:cty) (eparams:list (string & cty)) (body:string)
              (ctor:string) : ML unit =
    let fields = nonunit fields in
    let s = layout fields in
    fn ("static inline " ^ decl_of ret (entry ^ "(cherry_fn self" ^ params eparams ^ ")"))
       ("  struct " ^ s ^ " *env = (struct " ^ s ^ " *)self;\n  (void)env;\n" ^ body);
    protos := !protos @ [
      (match fields with
       | [] -> "#define " ^ ctor ^ "() " ^ s ^ "_new((cherry_code)" ^ entry ^ ", " ^ arity ^ ")\n"
       | _ -> "#define " ^ ctor ^ "(...) " ^ s ^ "_new((cherry_code)" ^ entry ^ ", " ^ arity ^
              ", __VA_ARGS__)\n")] in
  (* What marks a [return] of a call with arguments [ts] and result [ret] a
     guaranteed tail call, when it can be one (cherry.md, "Tail calls"). *)
  let mt (ts:list cty) (ret:cty) : ML string =
    if musttail_sig_ok (List.filter (fun t -> not (TUnit? t)) ts) (Some ret)
    then "CHERRY_MUSTTAIL " else "" in
  let ret_of (call:string) (ts:list cty) (ret:cty) (void:bool) : ML string =
    if void then "  " ^ call ^ ";\n  return " ^ unit_value ^ ";\n"
    else "  " ^ mt ts ret ^ "return " ^ call ^ ";\n" in
  let gen (r:clo_req) : ML unit =
    match r with
    | ReqPap (n, k, vty) ->
      let bs, ret = Some?.v (fn_sig n) in
      let tys = List.map (fun (b:binder) -> b.b_ty) bs in
      let captured, rest = List.splitAt k tys in
      let fields = named "e" 0 captured in
      let eparams = named "p" k rest in
      (* Only unit parameters left, and a value, not a closure, returned:
         such a closure runs once its type has no arrow left, however many
         unit arguments that took -- Mono may have dropped some of its unit
         binders, and a call site some of their arguments. *)
      let arity =
        if Nil? (nonunit eparams) && None? (arrow_view ret) then "CHERRY_ARITY_UNITS"
        else string_of_int (List.length (nonunit eparams)) in
      let entry = "cherry_entry_" ^ c_name n ^ "_" ^ string_of_int k in
      let void = Some? (HashTable.try_find !void_fns (string_of_name n)) in
      let call = c_name n ^ "(" ^
                 String.concat ", " (List.map (fun x -> "env->" ^ x) (names fields) @
                                     names eparams) ^ ")" in
      (* The entry point takes its arguments owned, and the closure holds its
         fields, while the function's own convention (Cherry's borrow
         inference) may borrow some of them: a borrowed field is lent as it
         is, and a borrowed argument is released after the call. *)
      let owned = match HashTable.try_find !Cherry.param_owned (string_of_name n) with
                  | Some fl -> fl
                  | None -> List.map (fun _ -> true) bs in
      let own_f, own_p = List.splitAt k owned in
      let fields_owned = List.zip fields own_f |> List.collect (fun (f, o) -> if o then [f] else []) in
      let borrowed_ps = List.zip eparams own_p |> List.collect (fun (x, o) -> if o then [] else [x]) in
      let ret_of (call:string) (ret:cty) (void:bool) : ML string =
        if Nil? (List.filter (fun (_, t) -> is_nonplain_ty t) borrowed_ps) then ret_of call tys ret void
        else if void then "  " ^ call ^ ";\n" ^ on "dec" "" borrowed_ps ^ "  return " ^ unit_value ^ ";\n"
        else "  " ^ decl_of ret "r" ^ " = " ^ call ^ ";\n" ^ on "dec" "" borrowed_ps ^ "  return r;\n" in
      if k = 0 then begin
        fn ("static inline " ^ decl_of ret (entry ^ "(cherry_fn self" ^ params eparams ^ ")"))
           ("  (void)self;\n" ^ ret_of call ret void);
        protos := !protos @ ["CHERRY_STATIC_CLOSURE(" ^ static_clo_name n ^ ", " ^ entry ^
                             ", " ^ arity ^ ");\n"]
      end else
        closure fields arity entry ret eparams
                (on "inc" "env->" fields_owned ^ ret_of call ret void)
                (pap_name n k)
    | ReqApply (t, k) ->
      let doms, rk = arrow_take k t in
      let args = named "a" 0 doms in
      (* A closure's arity counts the parameters that are not unit, since C
         has none of the others and a call site may have dropped their
         arguments -- unless its type has nothing else, when they are all
         that tells [f ()] over [unit -> unit -> unit] from a call of it. *)
      let given = nonunit args in
      let kn = List.length given in
      let call_code (ret:cty) (f:string) (xs:list (string & cty)) : ML string =
        "(" ^ code_ty ret (List.map snd xs) ^
        "CHERRY_CLOSURE(" ^ f ^ ")->fn)(" ^ String.concat ", " (f :: names xs) ^ ")" in
      (* A closure taking fewer: call it with what it takes, up to the next
         argument it does not, and apply the result to the rest. *)
      let under = range 0 (kn - 1) |> List.map (fun m ->
        let first, _ = List.splitAt m given in
        let next = fst (List.nth given m) in
        let cut = List.length (fst (List.span (fun (x, _) -> x <> next) args)) in
        let _, tm = arrow_take cut t in
        let rest = snd (List.splitAt cut args) in
        clo_request (ReqApply (tm, k - cut));
        "    case " ^ string_of_int m ^ ": {\n" ^
        "      cherry_fn g = " ^ call_code (TArrow (TUnit, E_Pure, TUnit)) "f" first ^ ";\n" ^
        (* An exception: [g] is no closure, and the rest goes unused. *)
        "      if (CHERRY_EXN_PENDING()) {\n" ^
        String.concat "" (rest |> List.collect (fun (x, xt) ->
          if is_nonplain_ty xt then ["        " ^ rc_call "dec" xt x ^ ";\n"] else [])) ^
        "        " ^ decl_of rk "r" ^ ";\n        memset(&r, 0, sizeof r);\n        return r;\n" ^
        "      }\n" ^
        "      " ^ decl_of rk "r" ^ " = " ^ apply_name tm (k - cut) ^ "(" ^
                String.concat ", " ("g" :: names rest) ^ ");\n" ^
        "      cherry_dec_fn(g);\n" ^
        "      return r;\n" ^
        "    }\n") in
      let fty = TArrow (TUnit, E_Pure, TUnit) in
      let exact = "    case " ^ string_of_int kn ^ ": " ^ mt (fty :: List.map snd given) rk ^
                  "return " ^ call_code rk "f" given ^ ";\n" in
      let units =
        if kn > 0 then ""
        else if Some? (arrow_view rk) then "    case CHERRY_ARITY_UNITS: cherry_inc(f); return f;\n"
        else "    case CHERRY_ARITY_UNITS: " ^ mt [fty] rk ^ "return " ^ call_code rk "f" [] ^ ";\n" in
      (* A closure taking more: what it was given is captured. *)
      let over = range (kn + 1) (kn + nonunit_arrows rk) |> List.map (fun m ->
        if kn = 0 then "    case " ^ string_of_int m ^ ": cherry_inc(f); return f;\n" else begin
          clo_request (ReqPapc (t, k, m));
          "    case " ^ string_of_int m ^ ": cherry_inc(f); return " ^ papc_name t k m ^ "(" ^
          String.concat ", " ("f" :: names given) ^ ");\n"
        end) in
      fn ("static inline " ^ decl_of rk (apply_name t k ^ "(cherry_fn f" ^ params args ^ ")"))
         ("  switch (CHERRY_CLOSURE(f)->arity) {\n" ^
          (if kn > 0 then "    case CHERRY_ARITY_UNITS:\n" else "") ^
          String.concat "" under ^ exact ^ units ^ String.concat "" over ^
          "    default: abort();\n  }\n")
    | ReqPapc (t, k, m) ->
      let doms, rk = arrow_take k t in
      let fields = nonunit (named "a" 0 doms) in
      let left = m - List.length fields in
      let edoms, rm = split_nonunit left rk in
      let eparams = named "p" k edoms in
      let call = "(" ^ code_ty rm (List.map snd fields @ List.map snd (nonunit eparams)) ^
                 "CHERRY_CLOSURE(env->f)->fn)(" ^
                 String.concat ", " ("env->f" :: List.map (fun x -> "env->" ^ x) (names fields) @
                                     names eparams) ^ ")" in
      closure (("f", t) :: fields) (string_of_int left) (papc_name t k m ^ "_entry") rm eparams
              (on "inc" "env->" fields ^ "  " ^
               mt (t :: List.map snd fields @ List.map snd eparams) rm ^ "return " ^ call ^ ";\n")
              (papc_name t k m) in
  let rec drain () : ML unit =
    match !clo_queue with
    | [] -> ()
    | r :: rest -> clo_queue := rest; gen r; drain () in
  drain ();
  (!protos, !defs)

(* Cherry: the definitions called in tail position by [e], as far as
   {!emit} can see -- the bodies of [let]s and sequences, the arms of
   conditionals and matches.  Missing one costs a jump, not correctness: the
   call is then an ordinary one. *)
let rec tail_callees (e:expr) : ML (list string) =
  match e.e with
  | ELet (_, _, _, e2) -> tail_callees e2
  | ESeq (_, e2) -> tail_callees e2
  | EIf (_, t, f) -> tail_callees t @ tail_callees f
  | EMatch (_, brs) -> List.collect (fun ((_, _, b):branch) -> tail_callees b) brs
  | EApp ({ e = EQual (n, _) }, _) -> [string_of_name n]
  | _ -> []

(* Cherry: the tail groups of [p] ({!tail_group}).  Two definitions are in
   one when each reaches the other through calls in tail position, the
   strongly connected components of that graph -- every cycle of tail calls
   is inside one, so a chain of tail calls that leaves a group never comes
   back, and only finitely many calls stay on the stack.  A definition joins
   only if its body can be printed inside another C function: no stack
   allocation (see {!stack_allocates}), and none of the per-definition
   decoration that a shared function would have to share. *)
let build_tail_groups (p:program) : ML unit =
  let mergeable (l:dlet) : ML bool =
    Cons? l.dl_binders && not (stack_allocates l.dl_body) &&
    not (l.dl_flags |> List.existsb (fun f ->
           Guard? f || Prologue? f || Epilogue? f || CInline? f)) in
  let ret_key (l:dlet) : ML string =
    if TUnit? l.dl_ret then "void" else decl_of l.dl_ret "" in
  let cands = p |> List.collect (fun d ->
    match d with
    | DLet l when local d && mergeable l -> [l]
    | _ -> []) in
  let tbl : HashTable.t string (dlet & string) = HashTable.create 50 in
  cands |> List.iter (fun (l:dlet) ->
    current := string_of_name l.dl_name;
    HashTable.add tbl (string_of_name l.dl_name) (l, ret_key l));
  let succs (l:dlet) (k:string) : ML (list string) =
    tail_callees l.dl_body |> List.filter (fun g ->
      g <> string_of_name l.dl_name &&
      (match HashTable.try_find tbl g with
       | Some (_, k') -> k' = k
       | None -> false)) in
  (* Tarjan's algorithm. *)
  let index : HashTable.t string int = HashTable.create 50 in
  let low : HashTable.t string int = HashTable.create 50 in
  let on_stack : HashTable.t string bool = HashTable.create 50 in
  let stack : ref (list string) = mk_ref [] in
  let next = mk_ref 0 in
  let sccs : ref (list (list string)) = mk_ref [] in
  let get (t:HashTable.t string int) (v:string) : ML int =
    match HashTable.try_find t v with Some i -> i | None -> 0 in
  let rec strong (v:string) : ML unit =
    HashTable.add index v !next; HashTable.add low v !next; next := !next + 1;
    stack := v :: !stack; HashTable.add on_stack v true;
    let (l, k) = Some?.v (HashTable.try_find tbl v) in
    succs l k |> List.iter (fun w ->
      if None? (HashTable.try_find index w) then begin
        strong w;
        if get low w < get low v then HashTable.add low v (get low w)
      end else if HashTable.try_find on_stack w = Some true then
        (if get index w < get low v then HashTable.add low v (get index w)));
    if get low v = get index v then begin
      let rec pop (acc:list string) : ML (list string) =
        match !stack with
        | w :: rest ->
          stack := rest; HashTable.add on_stack w false;
          if w = v then w :: acc else pop (w :: acc)
        | [] -> acc in
      sccs := pop [] :: !sccs
    end in
  cands |> List.iter (fun (l:dlet) ->
    let v = string_of_name l.dl_name in
    if None? (HashTable.try_find index v) then strong v);
  !sccs |> List.iter (fun (c:list string) ->
    if List.length c >= 2 then begin
      let members = cands |> List.filter (fun (l:dlet) ->
        List.existsb (fun x -> x = string_of_name l.dl_name) c) in
      let first = c_name (List.hd members).dl_name in
      let g = { tg_fn = alloc_name (first ^ "__tail");
                tg_args = alloc_name (first ^ "__tail_args");
                tg_members = members } in
      members |> List.iteri (fun i (l:dlet) ->
        HashTable.add !tail_groups (string_of_name l.dl_name) (i, g))
    end)

(* Split output (cherry.md, "Split output") gives each file only the helpers,
   prototypes and literals its text refers to, transitively: the whole set is
   tens of megabytes, which every file would otherwise parse.  Generated C is
   regular enough to do this on the text.  Every top-level line of an item
   starts a declaration, whose name is the one after [#define], the first
   argument of a [MACRO(name, ...)], or else the last identifier before the
   first [(], [=], [;], [\{] or [\[]. *)
let is_ident_start (c:SI.t) : bool =
  let open SI in
  (of_char 'a' <= c && c <= of_char 'z') ||
  (of_char 'A' <= c && c <= of_char 'Z') || c = of_char '_'
let is_digit (c:SI.t) : bool = let open SI in of_char '0' <= c && c <= of_char '9'
let is_ident_char (c:SI.t) : bool = is_ident_start c || is_digit c

(* The first offset from [i] before [j] whose byte fails [p], else [j]. *)
let rec skip_while (s:string) (p:SI.t -> bool) (i:SI.t) (j:SI.t) : ML SI.t =
  if SI.(i < j) && p (String.byte_at s i) then skip_while s p SI.(i + one) j else i

(* The identifiers of [s] from [i] to [j], in order, with their offsets. *)
let idents_between (s:string) (i:SI.t) (j:SI.t) : ML (list (SI.t & string)) =
  let rec go (i:SI.t) (acc:list (SI.t & string)) : ML (list (SI.t & string)) =
    if not SI.(i < j) then List.rev acc else
    let c = String.byte_at s i in
    if is_ident_start c then
      let k = skip_while s is_ident_char i j in
      go k ((i, String.byte_substring s i k) :: acc)
    (* a number's suffix ([1u]) is not a name *)
    else if is_digit c then go (skip_while s is_ident_char i j) acc
    else go SI.(i + one) acc in
  go i []

let idents_of (s:string) : ML (list string) =
  List.map snd (idents_between s SI.zero (String.byte_length s))

(* The names an item declares. *)
let declared_names (s:string) : ML (list string) =
  let n = String.byte_length s in
  let stops = [SI.of_char '('; SI.of_char '='; SI.of_char ';'; SI.of_char '{'; SI.of_char '['] in
  let rec go (i:SI.t) (acc:list string) : ML (list string) =
    if not SI.(i < n) then acc else
    let e = skip_while s (fun c -> c <> SI.of_char '\n') i n in
    let c = String.byte_at s i in
    let acc =
      if c = SI.of_char '#' then
        (match idents_between s i e with
         | (_, "define") :: (_, x) :: _ -> x :: acc
         | _ -> acc)
      else if is_ident_start c then begin
        let ids = idents_between s i e in
        let stop = skip_while s (fun c -> not (List.mem c stops)) i e in
        let before = List.filter (fun (k, _) -> SI.(k < stop)) ids in
        match before, ids with
        | [_], _ :: (_, x) :: _ when String.byte_at s stop = SI.of_char '(' ->
          (* MACRO(name, ...) *)
          x :: acc
        | _ :: _, _ -> snd (List.last before) :: acc
        | _ -> acc
      end else acc in
    go SI.(e + one) acc in
  go SI.zero []

(* The items, in order, that the text [roots] needs. *)
let select_items (provides:HashTable.t string (list int)) (uses:int -> ML (list string))
                 (roots:list string) : ML (list int) =
  let seen : HashTable.t string bool = HashTable.create 1000 in
  let chosen : HashTable.t int bool = HashTable.create 1000 in
  let rec go (work:list string) (out:list int) : ML (list int) =
    match work with
    | [] -> out
    | x :: work ->
      if HashTable.mem seen x then go work out else begin
        HashTable.add seen x true;
        match HashTable.try_find provides x with
        | None -> go work out
        | Some ks ->
          let ks = List.filter (fun k -> not (HashTable.mem chosen k)) ks in
          ks |> List.iter (fun k -> HashTable.add chosen k true);
          go (List.collect uses ks @ work) (ks @ out)
      end in
  List.sortWith (fun a b -> a - b) (go roots [])

let print_program (base:string) (cu:unit_info) (p:program)
  : ML (string & string & list (string & string)) =
  (* Section 42.2.  An imported declaration is in [p] so that the tables below
     see its shape, and out of every list that is emitted: the unit that
     compiled it has a header, and that header is included instead.  Writing a
     declaration of our own for it is what section 14.10 is the record of. *)
  let init_name = init_name cu in
  (* Section 121.2.  Every per-program variable this module has, including
     the generated comparisons of section 107, which are one unit's. *)
  reset_program_state ();
  split_out := Options.custard_cherry () && Options.custard_split ();
  split_data := [];
  record_parents p;
  (* Section 102.2.  Before the tables, not after them.  The external table
     below stores a *resolved* C name -- an external is the one declaration
     whose name may come from somewhere other than its lid, so resolving it
     once is what keeps the prototype and every call site agreeing -- and it
     resolves through [c_name], which reads {!renames}.  Filling it first and
     renaming afterwards left the table holding the name the option had just
     replaced.  Nothing in here reads a table, so the move costs nothing. *)
  build_renames true cu.cu_no_prefix p;
  rename_clashes init_name p;
  (* Section 116.  After the renames and before anything is printed, because
     the first generated name may be allocated as early as the first body.
     [reset_program_state] emptied the table; this seeds it, under the
     spelling that is actually emitted -- section 121.3, which is why there
     is nothing to spell out here.  The initializer is the one name no
     declaration stands behind (section 117.3). *)
  p |> List.iter (fun d -> HashTable.add !taken_names (emitted_name d) true);
  HashTable.add !taken_names init_name true;
  let tt = HashTable.create 50 in
  let ct = HashTable.create 50 in
  let xt = HashTable.create 20 in
  let kt = HashTable.create 50 in
  let vt = HashTable.create 50 in
  let at = HashTable.create 50 in
  p |> List.iter (fun d ->
    match d with
    | DType t ->
      HashTable.add tt (string_of_name t.dt_name) t;
      (* Section 33.4. *)
      t.dt_flags |> List.iter (fun f ->
        match f with
        | Existential (c, fld) ->
          HashTable.add existentials (string_of_name t.dt_name) (c, fld)
        | _ -> ());
      (match t.dt_body with
       | TVariant cs ->
         cs |> List.iter (fun (c, fs) -> HashTable.add ct (string_of_name c) (t, fs))
       | _ -> ())
    | DExternal x ->
      (match ifdef_of_flags x.dx_flags with
       | Some c ->
         if not (match x.dx_ty with
                 | TApp (n, []) -> Some "bool" = builtin_type n
                 | _ -> false) then begin
           current := string_of_name x.dx_name;
           E.raise_error0 E.Error_CustardBadIfDef [
             text ("Custard: " ^ string_of_name x.dx_name ^
                   " is marked [@@custard_c_ifdef] but is not a [bool].");
             text "The attribute says the value is a preprocessor condition, \
                   which is true or false and nothing else." ]
         end;
         HashTable.add !ifdefs (string_of_name x.dx_name) c
       | None -> ());
      HashTable.add xt (string_of_name x.dx_name)
        (match x.dx_target with
         (* Section 121.3.  [emitted_name] answers exactly this; the case
            split is kept here only for the note below, which is about what
            a target spelling is and has nowhere else to live. *)
         | Some "" | None -> emitted_name (DExternal x)
         (* Section 45.1.  Verbatim, like the external *type* path a few
            hundred lines up already is.  [sanitize] exists to turn an F*
            name into a legal C identifier, and this is not an F* name: it is
            a symbol that already exists on the other side, spelled the way
            its own language spells it.  Sanitizing [wmma::mma_sync] into
            [wmma__mma_sync] does not make it legal, it makes it absent.
            A C keyword is not escaped either, and for the same reason.
            The escape was here to catch a mistake, but it cannot: renaming
            [float] to [float_] does not make a wrong name right, it turns a
            link error against a name the program *did* write into one
            against a name it did not.  And the name is sometimes exactly a
            keyword on purpose -- Kuiper's [wmma::fragment<..., float>] needs
            a token spelled [float], and the type path above already lets
            [auto] through for the same reason.  The two paths now agree. *)
         | Some t -> t);
      (* A unit parameter of an *external* goes too, and unconditionally: the
         function on the other side is C, C has no unit value, and whatever it
         was declared as it was not declared to take one.  There is no body to
         consult, but there is nothing to consult it about -- a unit argument
         carries no information.  karamel does the same, which is why
         [EverCrypt_AutoConfig2_init()] is what both C paths must emit. *)
      let flags = arg_ctys x.dx_ty |> List.map (fun a -> not (TUnit? a)) in
      if List.existsb (fun b -> not b) flags then
        HashTable.add kt (string_of_name x.dx_name) flags;
      (* Same for a unit *result*: the target function returns [void], and a
         prototype saying otherwise is a declaration that does not match the
         definition it will be linked against. *)
      if Cons? flags && TUnit? (ret_cty x.dx_ty) then
        HashTable.add vt (string_of_name x.dx_name) true
      ;
      (* An external's arity is the one its declared type states; a
         parameterless one is a variable and is not called at all. *)
      let n = List.length (List.filter (fun b -> b) flags) in
      if n > 0 then HashTable.add at (string_of_name x.dx_name) n
    | DLet l ->
      (* Section 53.1.  Unconditionally, exactly as the external above, and
         for the same reason: a unit argument carries no information.  It used
         to depend on whether the body mentioned the binder, which made a
         definition's C arity a function of its *body* -- and a function
         passed as a value has no body at the use site, so the pointer type
         and the definition disagreed.  A mentioned binder is bound to the
         unit constant in [let_decl] instead, which is what [ELet] at unit
         type has always done for a local. *)
      let flags = l.dl_binders |> List.map (fun b -> not (TUnit? b.b_ty)) in
      (* Only worth recording when it changes something, and never for a
         definition whose every parameter would go: [f()] is fine, but the
         rejection of a parameterless definition below is about the IR, so the
         two must not be confused. *)
      if List.existsb (fun b -> not b) flags then HashTable.add kt (string_of_name l.dl_name) flags;
      if TUnit? l.dl_ret && Cons? l.dl_binders then HashTable.add vt (string_of_name l.dl_name) true
      ;
      if Cons? l.dl_binders then
        HashTable.add !fn_sigs (string_of_name l.dl_name) (l.dl_binders, l.dl_ret)
      else if Some? (arrow_view l.dl_ret) then
        HashTable.add !fn_globals (string_of_name l.dl_name) l.dl_ret;
      (* A parameterless definition of arrow type is lowered to a *variable*
         of function-pointer type (section 25.3), and a call through it
         supplies every argument at once -- so its arity is the arity of its
         type, not zero.  Leaving it out of the table is what let section 26's
         [call_e] reach a C compiler: both the expansion and this check record
         definitions, and a variable of arrow type was neither. *)
      let n = List.length (List.filter (fun b -> b) flags) in
      (* Section 115.  Counting the *kept* arguments, for the same reason the
         flags above exist: the pointer this variable is emitted as drops its
         unit parameters (section 53.1), and so does every call through it,
         so an arity taken from the arrow unfiltered rejects the very calls
         the type it came from describes. *)
      HashTable.add at (string_of_name l.dl_name)
        (if Cons? l.dl_binders then n
         else List.length (arg_ctys l.dl_ret |> List.filter
                             (fun (a:cty) -> not (TUnit? a))))
    | _ -> ());
  types := tt; ctors := ct; externs := xt; keeps := kt; void_fns := vt;
  (if Options.custard_cherry () then begin
     let et = HashTable.create 20 in
     p |> List.iter (fun d -> match d with
       | DExn x -> HashTable.add et (string_of_name x.de_name)
                     (x.de_args |> List.mapi (fun i t -> ("f" ^ string_of_int i, t)))
       | _ -> ());
     exn_ctors := et;
     let bt = HashTable.create 20 in
     Cherry.boxed_types p |> List.iter (fun k -> HashTable.add bt k true);
     let nt = HashTable.create 20 in
     Cherry.nonplain_types p |> List.iter (fun k -> HashTable.add nt k true);
     boxed_tbl := bt; nonplain_tbl := nt
   end);
  build_macros p;
  check_interface_names p;
  check_emitted_names init_name p;
  check_reference_copies p;
  arities := at;
  if Options.custard_cherry () then build_tail_groups p;

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
     #include <string.h>\n" in

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
  let includes = if Options.custard_cherry ()
                 then List.filter (fun i -> i <> "#include \"cherry.h\"") includes
                 else includes in

  let exts_named = p |> List.collect (fun d ->
    if not (local d) then [] else
    match d with
    | DExternal x when Some? (ifdef_of_flags x.dx_flags) -> []
    | DExternal x ->
      (match extern_decl x with
       | Some s ->
         let nm = emitted_name (DExternal x) in
         [(nm, string_of_name x.dx_name, s)]
       | None -> [])
    | DExn _ when Options.custard_cherry () -> []
    | DExn _ ->
      current := "an exception declaration";
      reject "an exception declaration" ["C has no exceptions."]
    | _ -> []) in

  (* Section 53.3.  One C symbol has one prototype.  Two externals reaching
     the same target name with different types produce two [extern] lines that
     C rejects as conflicting, and there are two ways to get there: several
     hand-written declarations sharing a [@@custard_extern] target -- which is
     what Warning 367's own advice used to recommend, unqualified -- and, under
     [--custard_monomorphize_types], one polymorphic external specialized at
     several type vectors.  Both give a file that does not compile, and the C
     compiler describes it in terms of generated prototypes rather than of the
     declarations that produced them.  The answer either way is the same one
     that makes a variadic macro work: with [@@custard_c_header] no prototype
     is emitted at all, and the header's own declaration is the only one. *)
  let () =
    let seen : HashTable.t string (string & string) = HashTable.create 20 in
    exts_named |> List.iter (fun (nm, src, s) ->
      match HashTable.try_find seen nm with
      | Some (src', s') when s' <> s ->
        E.raise_error0 E.Error_CustardExternConflict
          ([text ("Custard: the external target `" ^ nm ^
                  "' is declared twice, with different types.");
            text ("'" ^ src' ^ "' declares it as: " ^ trim_nl s');
            text ("'" ^ src ^ "' declares it as: " ^ trim_nl s);
            text "One C symbol has one prototype, so these cannot both be emitted.";
            text "If the target really does accept both -- a variadic macro, or an overload set -- add [@@custard_c_header \"...\"] naming the header that declares it.  Custard then emits no prototype of its own and includes the header instead, which is the only arrangement in which several type vectors can share one symbol.";
            text "Otherwise give each type vector its own [@@custard_extern] target name."])
      | _ -> HashTable.add seen nm (src, s)) in

  let exts = dedup (exts_named |> List.map (fun (_, _, s) -> s)) in

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
    (* A public one is in the header, which this source includes; repeating it
       here would be a redefinition. *)
    | DLet l when is_macro l -> if is_public l then [] else [guarded l (prologue_of l ^ macro_decl l)]
    (* Split, every file declares it and the first one defines it. *)
    | DLet l when Nil? l.dl_binders && !split_out ->
      if is_public l then [] else [guarded l (prologue_of l ^ global_extern l)]
    | DLet l when Nil? l.dl_binders -> [guarded l (prologue_of l ^ storage l ^ global_decl l)]
    | DLet l when Cons? l.dl_binders ->
      if is_public l then []
      else [guarded l (prologue_of l ^ storage l ^ inline_of l ^ proto_of l)]
    | _ -> []) in

  let pub_decls = p |> List.collect (fun d ->
    if not (local d) then [] else
    match d with
    (* Section 68.  A [#define] and nothing else: it has no linkage, so an
       [extern] declaration beside it would declare a different object, and
       the macro would then rewrite that declaration's own name. *)
    | DLet l when is_public l && is_macro l -> [guarded l (prologue_of l ^ macro_decl l)]
    | DLet l when is_public l && Nil? l.dl_binders ->
      [guarded l (prologue_of l ^ global_extern l)]
    | DLet l when is_public l -> [guarded l (prologue_of l ^ inline_of l ^ proto_of l)]
    | _ -> []) in

  (* A definition's text, its F* module, and how a split output treats it:
     [""] for a plain one, ["#inline"] for one that goes in the shared header
     (a [static inline] one), or else the tail group it belongs to, which is
     kept in one file, since the group's function and argument buffer are
     [static]. *)
  let defs = p |> List.collect (fun d ->
    if not (local d) then [] else
    match d with
    | DLet l when Nil? l.dl_binders -> []
    | DLet l when Some? (HashTable.try_find !tail_groups (string_of_name l.dl_name)) ->
      let (i, g) = Some?.v (HashTable.try_find !tail_groups (string_of_name l.dl_name)) in
      [(g.tg_fn, module_of l.dl_name,
        (if i = 0 then tail_group_decl g else "") ^
        (* Only the group's function may call a member that nothing
           outside the group names. *)
        comment_of l ^ storage l ^ "CHERRY_UNUSED " ^ tail_member_decl i g l)]
    | DLet l -> [((if l.dl_flags |> List.existsb CInline? then "#inline" else ""),
                  module_of l.dl_name,
                  guarded l (comment_of l ^ prologue_of l ^ storage l ^ inline_of l ^
                             let_decl l ^ epilogue_of l))]
    | _ -> []) in
  let global_defs =
    if not !split_out then [] else
    p |> List.collect (fun d ->
      if not (local d) then [] else
      match d with
      | DLet l when is_macro l -> []
      | DLet l when Nil? l.dl_binders ->
        [(module_of l.dl_name, guarded l (prologue_of l ^ global_decl l))]
      | _ -> []) in

  (* In declaration order, which the SCC pass has already made a topological
     one: a global whose initializer reads another global sees it set. *)
  let init_lets = global_inits_of p in
  let inits = init_lets |> List.mapi (fun i l -> global_init (i = 0) l) in
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
  (* Cherry keeps the command line for [FStarC.Util.get_cmd_args]. *)
  let main_head () : ML string =
    if Options.custard_cherry ()
    then "int main(int argc, char **argv) {\n  cherry_set_args(argc, argv);\n"
    else "int main(void) {\n" in
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
      let pre = main_head () ^ String.concat "" calls in
      (* Cherry: an exception the program let escape. *)
      if Options.custard_cherry () then
        let chk = "  if (cherry_exn_slot) cherry_exn_uncaught();\n" in
        (match l.dl_ret with
         | TInt _ -> [pre ^ "  int r = (int)" ^ call ^ ";\n" ^ chk ^ "  return r;\n}\n"]
         | TUnit -> [pre ^ "  " ^ call ^ ";\n" ^ chk ^ "  return 0;\n}\n"]
         | _ -> [pre ^ "  (void)" ^ call ^ ";\n" ^ chk ^ "  return 0;\n}\n"])
      else
      (match l.dl_ret with
       | TInt _ -> [pre ^ "  return (int)" ^ call ^ ";\n}\n"]
       | TUnit -> [pre ^ "  " ^ call ^ ";\n  return 0;\n}\n"]
       | _ -> [pre ^ "  (void)" ^ call ^ ";\n  return 0;\n}\n"])
    | _ -> []) in
  (* [--custard_main M] naming a module: running the program is running the
     initializers, as it is for an OCaml executable. *)
  let mains =
    match mains, Options.custard_main () with
    | [], Some m when cu.cu_name = None || cu.cu_name = Some m ->
      let calls = (cu.cu_inits |> List.map (fun i -> "  " ^ i ^ "();\n")) @
                  (match inits with [] -> [] | _ -> ["  " ^ init_name ^ "();\n"]) in
      let chk = if Options.custard_cherry ()
                then "  if (cherry_exn_slot) cherry_exn_uncaught();\n" else "" in
      [main_head () ^ String.concat "" calls ^ chk ^ "  return 0;\n}\n"]
    | _ -> mains in

  (* Section 107.  After every body has been rendered, which is when the set
     of types actually compared is complete. *)
  let eq_protos, eq_defs = eq_decls () in
  let rc_protos, rc_defs, rc_homed = cherry_helpers p in
  let clo_protos, clo_defs = cherry_closure_helpers () in
  let pbuf_protos, pbuf_defs = cherry_pbuf_helpers () in
  let ref_protos, ref_defs = cherry_ref_helpers () in
  let iarr_protos, iarr_defs = cherry_iarr_helpers () in
  let exn_protos, exn_defs = cherry_exn_helpers p in
  let any_protos, any_defs = cherry_any_helpers () in

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

  let hdr_body =
  cpp_open ^
  String.concat "" fwds ^ (match fwds with [] -> "" | _ -> "\n") ^
  String.concat "" tys ^ (match tys with [] -> "" | _ -> "\n") ^
  String.concat "" pub_decls ^ (match pub_decls with [] -> "" | _ -> "\n") ^
  init_proto ^ (match inits with [] -> "" | _ -> "\n") ^
  cpp_close in

  let lits = !string_lit_defs in
  let fn_defs, inline_defs =
    let text (_, _, d) = d in
    if not !split_out then List.map text defs, [] else
    List.map text (List.filter (fun (k, _, _) -> k <> "#inline") defs),
    List.map text (List.filter (fun (k, _, _) -> k = "#inline") defs) in
  (* The pieces of the source before the definitions, each a list of items
     joined by its separator. *)
  let support_groups = [
    "", exts; "", lits; "", rc_protos; "", ref_protos; "", iarr_protos;
    "", exn_protos; "", any_protos; "", pbuf_protos; "\n", rc_defs; "", protos;
    "", clo_protos; "\n", clo_defs; "\n", ref_defs; "\n", iarr_defs;
    "\n", exn_defs; "\n", any_defs; "\n", pbuf_defs; "", eq_protos;
    "\n", eq_defs; "\n", inline_defs ] in
  let render_groups (gs:list (string & list string)) : ML string =
    String.concat "" (gs |> List.map (fun (sep, xs) ->
      String.concat sep xs ^ (match xs with [] -> "" | _ -> "\n"))) in
  let support_body = render_groups support_groups in
  let tail_body =
    (match inits with [] -> "" | _ -> init_fn) ^
    (match mains with [] -> "" | _ -> "\n" ^ String.concat "\n" mains) in
  let src_body = support_body ^ String.concat "\n" fn_defs ^ "\n" ^ tail_body in

  (* Sections 5.1, 66 and 98.  Each of the two support blocks goes into the
     header if the header needs it, otherwise into the source if the source
     does, otherwise nowhere.  A header is a file a person reads, and a block
     that every reader has to skip past to reach the declarations is a cost
     paid by every consumer for a feature almost none of them use.

     The narrow-float check goes after the [custard_c_header] includes and
     never before them: it is satisfied by supplying the type and the
     operations first, and the header that supplies them is named by an
     attribute on an F* declaration, so it arrives here and nowhere earlier.
     In the source the includes come in through the unit's own header, which
     is the first line, so the same rule holds there. *)
  let hdr_narrow = mentions_narrow hdr_body in
  let hdr_unit   = mentions_unit hdr_body in
  let hdr_fspec  = mentions_float_special hdr_body in
  let hdr =
    header ^
  (match includes with [] -> "" | _ -> "\n" ^ String.concat "\n" includes ^ "\n") ^
    (* The runtime is not generated: it ships with F* as ulib/c/cherry.h. *)
    (if Options.custard_cherry () then "\n#include \"cherry.h\"\n" else "") ^
    (if hdr_unit then "\n" ^ unit_support else "") ^
    (if hdr_fspec then "\n" ^ float_special_support else "") ^
    (if hdr_narrow then narrow_support else "") ^
    "\n" ^ hdr_body ^
  "#endif\n" in

  (* The source includes its own header, so the header is *checked* against
     the definitions rather than merely shipped alongside them. *)
  let body =
    banner ^
    "#include \"" ^ base ^ ".h\"\n" ^
    (if not hdr_unit && mentions_unit src_body
     then "\n" ^ unit_support else "") ^
    (if not hdr_fspec && mentions_float_special src_body
     then "\n" ^ float_special_support else "") ^
    (if not hdr_narrow && mentions_narrow src_body
     then narrow_support else "") ^
    "\n" ^ src_body in
  if not !split_out then hdr, body, [] else begin
    (* Split: one file per F* module, so that a change to one module changes
       its file and no other. *)
    let files : HashTable.t string (list string) = HashTable.create 100 in
    let order : ref (list string) = mk_ref [] in
    let put (m:string) (d:string) : ML unit =
      match HashTable.try_find files m with
      | Some l -> HashTable.add files m (d :: l)
      | None -> order := m :: !order; HashTable.add files m [d] in
    (* A tail group goes where its first member does. *)
    let group_home : HashTable.t string string = HashTable.create 50 in
    defs |> List.iter (fun (k, m, d) ->
      if k = "#inline" then ()
      else if k = "" then put m d
      else match HashTable.try_find group_home k with
        | Some m' -> put m' d
        | None -> HashTable.add group_home k m; put m d);
    global_defs |> List.iter (fun (m, d) -> put m d);
    rc_homed |> List.iter (fun (m, d) -> put m d);
    (* The initializer calls one function per run of consecutive globals of
       a module, defined in that module's file: as a single function it was
       slower to compile than everything else together. *)
    let runs = List.fold_left2 (fun (acc:list (string & list string)) l i ->
        let m = module_of l.dl_name in
        match acc with
        | (m', is) :: acc' when m' = m -> (m, i :: is) :: acc'
        | _ -> (m, [i]) :: acc) [] init_lets inits |> List.rev in
    let seen : HashTable.t string int = HashTable.create 50 in
    let pieces = runs |> List.map (fun (m, is) ->
      let k = match HashTable.try_find seen m with Some k -> k + 1 | None -> 1 in
      HashTable.add seen m k;
      let nm = init_name ^ "__" ^ sanitize m ^ (if k = 1 then "" else "_" ^ show k) in
      put m ("void " ^ nm ^ "(void) {\n" ^ String.concat "" (List.rev is) ^ "}\n");
      nm) in
    let piece_protos = pieces |> List.map (fun nm -> "void " ^ nm ^ "(void);\n") in
    let init_fn = match inits with
      | [] -> ""
      | _ -> "void " ^ init_name ^ "(void) {\n" ^ init_guard ^
             String.concat "" (pieces |> List.map (fun nm -> "  " ^ nm ^ "();\n")) ^
             "}\n" in
    let tail_body =
      init_fn ^ (match mains with [] -> "" | _ -> "\n" ^ String.concat "\n" mains) in
    (* Every item of the support code, numbered in order, indexed by the
       names it declares. *)
    let groups = support_groups @ ["", piece_protos] in
    let numbered, _ = List.fold_left (fun (acc, k) (sep, xs) ->
        let ys = List.mapi (fun i x -> (k + i, x)) xs in
        ((sep, ys) :: acc, k + List.length xs)) ([], 0) groups in
    let numbered = List.rev numbered in
    let uses : HashTable.t int (list string) = HashTable.create 100000 in
    let provides : HashTable.t string (list int) = HashTable.create 100000 in
    numbered |> List.iter (fun (_, ys) -> ys |> List.iter (fun (k, x) ->
      HashTable.add uses k (idents_of x);
      declared_names x |> List.iter (fun n ->
        HashTable.add provides n
          (k :: (match HashTable.try_find provides n with Some l -> l | None -> [])))));
    let uses_of k = match HashTable.try_find uses k with Some l -> l | None -> [] in
    let prelude =
      banner ^ "#include \"" ^ base ^ ".h\"\n" ^
      (if not hdr_unit && mentions_unit src_body
       then "\n" ^ unit_support else "") ^
      (if not hdr_fspec && mentions_float_special src_body
       then "\n" ^ float_special_support else "") ^
      (if not hdr_narrow && mentions_narrow src_body
       then narrow_support else "") ^
      "\n" in
    (* The items of [ys] whose numbers are in [sel], both ascending. *)
    let rec pick (sel:list int) (ys:list (int & string)) (acc:list string)
      : Tot (list int & list string) (decreases %[ys; sel]) =
      match sel, ys with
      | [], _ | _, [] -> sel, List.rev acc
      | k :: sel', (j, x) :: ys' ->
        if k = j then pick sel' ys' (x :: acc)
        else if k < j then pick sel' ys acc
        else pick sel ys' acc in
    let part (text:string) =
      let sel = select_items provides uses_of (idents_of text) in
      let _, gs = List.fold_left (fun (sel, gs) (sep, ys) ->
          let sel, xs = pick sel ys [] in
          (sel, (sep, xs) :: gs)) (sel, []) numbered in
      prelude ^ render_groups (List.rev gs) ^ text in
    (* The [-o] file: what exists once, the initializer and [main]. *)
    let body0 = part (String.concat "" !split_data ^ "\n" ^ tail_body) in
    let extras =
      List.rev !order |> List.map (fun m ->
        (base ^ "." ^ m ^ ".c",
         part (String.concat "\n"
                 (List.rev (match HashTable.try_find files m with Some l -> l | None -> []))))) in
    hdr, body0, extras
  end
