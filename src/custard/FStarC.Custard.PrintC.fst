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

    What C cannot express is *rejected by name*, with error 367, rather than
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

(* -------------------------------------------------------------------- *)
(* Rejections                                                           *)
(* -------------------------------------------------------------------- *)

(* The declaration being printed, so that a rejection can say where it is.
   The IR carries no source positions (section 2.2), so the declaration's name
   is the best locator there is -- and, since Custard's names are readable by
   construction, a good one. *)
let current : ref string = mk_ref "<toplevel>"

let reject (#a:Type) (what:string) (why:list string) : ML a =
  E.raise_error0 E.Error_CustardNoCRepresentation
    ([text ("Custard: " ^ what ^ " has no C representation, in " ^ !current ^ ".")]
     @ List.map text why)

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

let sanitize (s:string) : ML string =
  let ok (c:char) : ML bool =
    let i = BU.int_of_char c in
    is_alpha i || (i >= 48 && i <= 57) || i = 95
  in
  let s = String.concat ""
            (List.map (fun c -> if ok c then BU.string_of_char c else "_")
                      (String.list_of_string s)) in
  (* A C identifier may not start with a digit. *)
  if s = "" then "x"
  else if is_alpha (BU.int_of_char (List.hd (String.list_of_string s))) || 
          BU.int_of_char (List.hd (String.list_of_string s)) = 95
  then s else "x" ^ s

let escape_kw (s:string) : ML string =
  if List.existsb (fun k -> k = s) c_keywords then s ^ "_" else s

let c_name (n:name) : ML string = escape_kw (sanitize (mangled_name n))
let c_var (x:string) : ML string = escape_kw (sanitize x)

(* An enum tag.  Uppercased so that it cannot collide with a value or a type
   name derived from the same lid. *)
let c_tag (n:name) : ML string = String.uppercase (sanitize (mangled_name n))

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
let builtin_type (n:name) : ML (option string) =
  match (if Some? n.spec then "" else String.concat "." (n.ns @ [n.id])) with
  | "Prims.unit" -> Some "custard_unit"
  | "Prims.bool" -> Some "bool"
  | "Prims.string" -> Some "const char *"
  | "FStar.Char.char" -> Some "uint32_t"
  | _ -> None

(* C declarations are not "type, then name": the [*] of a pointer and the
   [(...)] of a function bind to the *declarator*, so the name has to be built
   from the inside out.  [decl_of t x] is the declaration of [x] at type [t],
   and [x = ""] gives the abstract declarator -- the form a cast or a compound
   literal wants.  Building the two together is what lets a returned pointer
   ([uint32_t *f(void)]) and a stored function ([size_t ( *hashf)(size_t)]) come
   out right without special cases at each use. *)
let rec decl_of (t:cty) (x:string) : ML string =
  match t with
  | TBuf e -> decl_of e ("*" ^ x)
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
  | TApp (n, []) ->
    (match builtin_type n with
     | Some s -> s
     | None ->
       (match find_type n with
        | Some { dt_body = TAbstract } ->
          reject ("the abstract type " ^ string_of_name n)
            ["A type with no definition has no size, so C cannot store it.";
             "Prims.int in particular is unbounded: use a machine integer type \
              instead."]
        | _ -> c_name n))
  | TApp (n, _) ->
    reject ("the polymorphic type " ^ string_of_name n)
      ["The direct-to-C backend requires --custard_monomorphize_types true \
        (section 5.0.1)."]
  | TVar x ->
    reject ("the type variable '" ^ x)
      ["The direct-to-C backend requires --custard_monomorphize_types true \
        (section 5.0.1)."]
  | TTuple _ ->
    reject "an anonymous tuple type"
      ["Tuples reach the backend as FStar.Pervasives.Native.tupleN, which is \
        an ordinary inductive; a bare TTuple means a rule introduced one."]
  | TAny ->
    reject "a value whose representation is unknown (TAny)"
      ["Run with --custard_warn_any to see where the representation was lost \
        (section 5.6)."]
  | TBuf _ | TArrow _ -> decl_of t ""

(* The abstract declarator: a type as a cast or a compound literal spells it. *)
let ty (t:cty) : ML string = decl_of t ""

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
      if i < 32 || i > 126
      then "\\" ^ (if i < 8 then "00" else if i < 64 then "0" else "") ^
           (* C string escapes are octal. *)
           show ((i / 64) * 100 + ((i / 8) % 8) * 10 + (i % 8))
      else BU.string_of_char c
  in
  String.concat "" (List.map esc (String.list_of_string s))

let constant (c:constant) : ML string =
  match c with
  | CUnit -> "((custard_unit)0)"
  | CBool b -> if b then "true" else "false"
  | CInt (s, Some sw) ->
    (* The cast pins the type: an unsuffixed literal is [int], which would make
       [x + 1] promote and then wrap at the wrong width. *)
    "((" ^ int_type sw ^ ")" ^ s ^ ")"
  | CInt (s, None) ->
    reject ("the unbounded integer literal " ^ s)
      ["Prims.int has no C representation; use a machine integer type."]
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
  | And -> Some (if Some? o.po_int then "&" else "&&")
  | Or -> Some (if Some? o.po_int then "|" else "||")
  | _ -> None

let prefix_op (o:prim_op) : ML (option string) =
  match o.po_op with
  | Not -> Some (if Some? o.po_int then "~" else "!")
  | BNot -> Some "~"
  | _ -> None

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
let scope : ref (list (string & string)) = mk_ref []
let declared : ref (SMap.t bool) = mk_ref (SMap.create 0)

let reset_scope () : ML unit =
  scope := []; declared := SMap.create 20

let bind_var (x:string) : ML string =
  let base = c_var x in
  let rec pick (i:int) : ML string =
    let cand = if i = 0 then base else base ^ "_" ^ show i in
    if Some? (SMap.try_find !declared cand) then pick (i + 1) else cand in
  let nm = pick 0 in
  SMap.add !declared nm true;
  scope := (x, nm) :: !scope;
  nm

let lookup_var (x:string) : ML string =
  match !scope |> List.tryFind (fun (y, _) -> y = x) with
  | Some (_, nm) -> nm
  | None -> c_var x

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
  | ECtor (_, es) | ERaise (_, es) | ETuple es | EOp (_, es) -> List.collect vars_of es
  | ERecord (_, fs) -> List.collect (fun (_, e) -> vars_of e) fs
  | EProj (a, _, _) | EDiscrim (a, _) | ECast (a, _) -> vars_of a

and vars_of_branch (br:branch) : ML (list string) =
  let _, g, b = br in
  (match g with Some g -> vars_of g | None -> []) @ vars_of b

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
  | EVar x -> lookup_var x
  | EAny ->
    (* What an uninitialized stack slot holds.  A zero of the right type is a
       legal value of it and is what C would give a static. *)
    "(" ^ ty e.ty ^ "){0}"
  | EQual (n, _) ->
    (match SMap.try_find !externs (string_of_name n) with
     | Some t -> t
     | None -> c_name n)
  | EApp (hd, args) ->
    c_expr out ind hd ^ "(" ^
    String.concat ", " (args |> List.map (c_expr out ind)) ^ ")"
  | ECast (e1, t) ->
    (match e1.ty, t with
     | TInt a, TInt b when a = b -> c_expr out ind e1
     | _ -> "(" ^ ty t ^ ")" ^ c_expr out ind e1)
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
    c_expr out ind b ^ "[" ^ c_expr out ind i ^ "]"
  | EOp ({ po_op = BufSub }, [b; i]) ->
    "(" ^ c_expr out ind b ^ " + " ^ c_expr out ind i ^ ")"
  | EOp ({ po_op = BufNull }, []) -> "(" ^ ty e.ty ^ ")NULL"
  | EOp ({ po_op = BufIsNull }, [b]) -> "(" ^ c_expr out ind b ^ " == NULL)"
  | EOp (o, [a; b]) when Some? (infix_op o) ->
    "(" ^ c_expr out ind a ^ " " ^ Some?.v (infix_op o) ^ " " ^ c_expr out ind b ^ ")"
  | EOp (o, [a]) when Some? (prefix_op o) ->
    "(" ^ Some?.v (prefix_op o) ^ c_expr out ind a ^ ")"
  | EOp (o, args) ->
    reject ("an operator applied to " ^ show (List.length args) ^ " arguments") []
  | EFun _ ->
    reject "a lambda"
      ["C has no closures.  Mark the parameter it is passed to \
        [@@@monomorphize] so that it is specialized away (section 3.1)."]
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
  let x = fresh "t" in
  out := !out ^ ind ^ decl_of e.ty x ^ ";\n" ^ emit ind (D_Assign x) e;
  x

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
  | D_Return -> ind ^ "return " ^ s ^ ";\n"
  | D_Assign x -> ind ^ x ^ " = " ^ s ^ ";\n"
  (* The value is computed for its effect; the cast silences the warning that
     it is unused. *)
  | D_Ignore -> ind ^ "(void)(" ^ s ^ ");\n"

and emit (ind:string) (d:dest) (e:expr) : ML string =
  let ind' = ind ^ "  " in
  match e.e with
  (* [e1] is elaborated before [x] is bound: the IR scopes [x] over [e2] only,
     and a name reused between the two must not capture. *)
  | ELet (x, t, e1, e2) ->
    let saved = !scope in
    let s1 =
      if is_stmt e1
      then (let x = bind_var x in
            ind ^ decl_of t x ^ ";\n" ^
            (let saved' = !scope in
             scope := saved;
             let s = emit ind (D_Assign x) e1 in
             scope := saved'; s))
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
    !out ^
    ind ^ "if (" ^ cs ^ ") {\n" ^ emit ind' d t ^
    ind ^ "} else {\n" ^ emit ind' d f ^
    ind ^ "}\n"

  | EMatch (scrut, brs) -> emit_match ind d scrut brs

  (* Pulse's loop (section 7.4).  The condition is a computation, not an
     expression, so it goes inside the loop and the exit is a [break]. *)
  | EWhile (c, body) ->
    let out = mk_ref "" in
    let cs = c_expr out ind' c in
    ind ^ "while (true) {\n" ^ !out ^
    ind' ^ "if (!(" ^ cs ^ ")) { break; }\n" ^
    emit ind' D_Ignore body ^
    ind ^ "}\n" ^
    (match d with D_Ignore -> "" | _ -> finish ind d "((custard_unit)0)")

  (* Control does not reach here.  [abort] is [_Noreturn], so no [return]
     has to follow it even in a value position. *)
  | EAbort s -> ind ^ "/* " ^ escape s ^ " */\n" ^ ind ^ "abort();\n"

  | EOp ({ po_op = BufCreate lt }, [init; len]) ->
    emit_alloc ind d lt e.ty init len

  | EOp ({ po_op = BufWrite }, [b; i; v]) ->
    let out = mk_ref "" in
    let b = c_expr out ind b in
    let i = c_expr out ind i in
    let v = c_expr out ind v in
    !out ^ ind ^ b ^ "[" ^ i ^ "] = " ^ v ^ ";\n" ^ unit_result ind d

  | EOp ({ po_op = BufFree }, [b]) ->
    let out = mk_ref "" in
    let b = c_expr out ind b in
    !out ^ ind ^ "free(" ^ b ^ ");\n" ^ unit_result ind d

  | EOp ({ po_op = BufBlit }, [src; si; dst; di; len]) ->
    let out = mk_ref "" in
    let elt = match dst.ty with
              | TBuf e -> ty e
              | _ -> reject "a blit whose destination is not a pointer" [] in
    let srcv = c_expr out ind src in
    let siv = c_expr out ind si in
    let dstv = c_expr out ind dst in
    let div = c_expr out ind di in
    let lenv = c_expr out ind len in
    !out ^ ind ^ "memmove(" ^ dstv ^ " + " ^ div ^ ", " ^ srcv ^ " + " ^ siv ^
    ", (" ^ lenv ^ ") * sizeof(" ^ elt ^ "));\n" ^ unit_result ind d

  | _ ->
    let out = mk_ref "" in
    let s = c_expr out ind e in
    !out ^ finish ind d s

and unit_result (ind:string) (d:dest) : ML string =
  match d with D_Ignore -> "" | _ -> finish ind d "((custard_unit)0)"

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
            | TBuf e -> ty e
            | _ -> reject "an allocation whose result is not a pointer" [] in
  let arr = fresh "buf" in
  let i = fresh "i" in
  let alloc =
    match lt with
    | LStack -> ind ^ elt ^ " " ^ arr ^ "[" ^ lv ^ "];\n"
    | LHeap ->
      ind ^ elt ^ " *" ^ arr ^ " = (" ^ elt ^ " *)malloc((" ^ lv ^
      ") * sizeof(" ^ elt ^ "));\n" ^
      ind ^ "if (" ^ arr ^ " == NULL) { abort(); }\n" in
  !out ^ alloc ^
  ind ^ "for (size_t " ^ i ^ " = 0; " ^ i ^ " < (size_t)(" ^ lv ^ "); " ^ i ^ "++) {\n" ^
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
and pat_tests (used:list string) (path:string) (t:cty) (p:pat)
    : ML (list string & list string) =
  match p with
  | PWild -> ([], [])
  | PVar x ->
    if List.existsb (fun y -> y = x) used
    then ([], [decl_of t (bind_var x) ^ " = " ^ path ^ ";"])
    else ([], [])
  | PConst c -> ([path ^ " == " ^ constant c], [])
  | PTuple _ ->
    reject "an anonymous tuple pattern"
      ["Tuples reach the backend as FStar.Pervasives.Native.MktupleN."]
  | POr _ ->
    reject "a pattern disjunction"
      ["Split the branch into one per alternative."]
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
                : ML (list string & list string) =
         match fs, ps with
         | (f, ft) :: fs, p :: ps ->
           let t1, b1 = pat_tests used (sub f) ft p in
           let t2, b2 = go fs ps in
           (t1 @ t2, b1 @ b2)
         | _ -> ([], []) in
       let t2, b2 = go fields ps in
       (tests @ t2, b2))

and emit_match (ind:string) (d:dest) (scrut:expr) (brs:list branch) : ML string =
  let out = mk_ref "" in
  let sv = c_expr out ind scrut in
  (* The scrutinee is tested once per branch, so it has to be a name -- unless
     no branch looks at it, in which case naming it would leave an unused
     variable behind.  That happens for a single catch-all branch, which is
     what a [let] over an irrefutable pattern turns into. *)
  let x = fresh "s" in
  let looked_at =
    let saved = !scope in
    let r = brs |> List.existsb (fun (p, g, b) ->
              let ts, bs = pat_tests (vars_of_branch (p, g, b)) x scrut.ty p in
              Cons? ts || Cons? bs) in
    scope := saved; r in
  let ind' = ind ^ "  " in
  if not looked_at then
    (match brs with
     | (_, None, b) :: _ -> !out ^ ind ^ "(void)(" ^ sv ^ ");\n" ^ emit ind d b
     | _ -> !out ^ ind ^ "(void)(" ^ sv ^ ");\n" ^ ind ^ "abort();\n")
  else
  let head = !out ^ ind ^ decl_of scrut.ty x ^ " = " ^ sv ^ ";\n" in
  let rec go (first:bool) (brs:list branch) : ML string =
    match brs with
    | [] ->
      (* A match the type says is exhaustive but the tests do not prove so.
         Falling off the end of a value-producing chain would be undefined,
         so it aborts instead. *)
      ind ^ "else {\n" ^ ind' ^ "abort();\n" ^ ind ^ "}\n"
    | (p, g, b) :: rest ->
      if Some? g then
        reject "a pattern guard"
          ["Rewrite the guard as an 'if' in the branch body."];
      let saved = !scope in
      let tests, binds = pat_tests (vars_of_branch (p, g, b)) x scrut.ty p in
      let body =
        String.concat "" (binds |> List.map (fun s -> ind' ^ s ^ "\n")) ^
        emit ind' d b in
      scope := saved;
      if Nil? tests then
        (* Irrefutable, so it is the last branch that can run; anything after
           it is dead and C would warn about it. *)
        (if first then ind ^ "{\n" ^ body ^ ind ^ "}\n"
         else ind ^ "else {\n" ^ body ^ ind ^ "}\n")
      else
        (if first then ind else ind ^ "else ") ^
        "if (" ^ String.concat " && " tests ^ ") {\n" ^ body ^ ind ^ "}\n" ^
        go false rest in
  head ^ go true brs

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

let type_decl (d:dtype) : ML (option string) =
  if Some? (builtin_type d.dt_name) then None else
  let n = c_name d.dt_name in
  match d.dt_body with
  | TAbstract -> None
  | TAbbrev c -> Some ("typedef " ^ decl_of c n ^ ";\n")
  | TRecord fs ->
    check_finite d;
    Some ("typedef struct {\n" ^
          String.concat "" (fs |> List.map (fun (f, c) ->
            "  " ^ decl_of c (c_var f) ^ ";\n")) ^
          "} " ^ n ^ ";\n")
  | TVariant cs ->
    check_finite d;
    if is_enum d then
      Some ("typedef enum {\n" ^
            String.concat ",\n" (cs |> List.map (fun (c, _) -> "  " ^ c_tag c)) ^
            "\n} " ^ n ^ ";\n")
    else if single_ctor d then
      let _, fs = List.hd cs in
      Some ("typedef struct {\n" ^
            String.concat "" (fs |> List.map (fun (f, c) ->
              "  " ^ decl_of c (c_var f) ^ ";\n")) ^
            "} " ^ n ^ ";\n")
    else
      (* A tagged union.  The per-constructor structs are anonymous members of
         one union, named after the constructor, so that a use site can name a
         field knowing only the constructor -- which after monomorphization it
         always does. *)
      let nonempty = cs |> List.filter (fun (_, fs) -> Cons? fs) in
      Some ("typedef struct {\n" ^
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
            "} " ^ n ^ ";\n")

(* The C signature of a definition, without the trailing [;] or body. *)
let signature (l:dlet) : ML string =
  let args =
    match l.dl_binders with
    | [] -> "void"
    | bs -> String.concat ", " (bs |> List.map (fun b -> decl_of b.b_ty (lookup_var b.b_name))) in
  decl_of l.dl_ret (c_name l.dl_name ^ "(" ^ args ^ ")")

(* A definition with no parameters is a C *variable*, not a function of no
   arguments, and its initializer has to be a constant expression -- which the
   body of an arbitrary F* definition is not.  So it becomes a function of no
   arguments plus a call at each use, which is what the extractor already
   emits: an [EQual] with an empty spine is applied nowhere, so it would be a
   function pointer.  Rejecting is honest; nothing in the corpus needs it. *)
let let_decl (l:dlet) : ML string =
  current := string_of_name l.dl_name;
  ctr := 0;
  reset_scope ();
  l.dl_binders |> List.iter (fun b -> let _ = bind_var b.b_name in ());
  if Nil? l.dl_binders then
    reject ("the top-level value " ^ string_of_name l.dl_name)
      ["C has no way to initialize a global from a computation.";
       "Make it a function of unit."];
  let used = vars_of l.dl_body in
  (* C also warns about an unused *parameter*, and a definition's parameters
     have to be named, so the ones the body never mentions are voided
     explicitly. *)
  let voids = String.concat "" (l.dl_binders |> List.collect (fun b ->
    if List.existsb (fun y -> y = b.b_name) used then []
    else ["  (void)" ^ lookup_var b.b_name ^ ";\n"])) in
  signature l ^ " {\n" ^ voids ^ emit "  " D_Return l.dl_body ^ "}\n"

(* An external is a symbol someone else defines.  When it comes with a header
   we include the header and say nothing more; otherwise we declare it from
   its Custard type, which is exactly the contract the hand-written C has to
   meet. *)
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
    Some ("extern " ^
          decl_of ret (nm ^ "(" ^ String.concat ", " (args |> List.map ty) ^ ")") ^
          ";\n")
  | None -> Some ("extern " ^ decl_of x.dx_ty nm ^ ";\n")

(* -------------------------------------------------------------------- *)
(* The file                                                             *)
(* -------------------------------------------------------------------- *)

let rec dedup (xs : list string) : ML (list string) =
  match xs with
  | [] -> []
  | x :: rest -> x :: dedup (rest |> List.filter (fun y -> y <> x))

let print_program (p:program) : ML string =
  let tt = SMap.create 50 in
  let ct = SMap.create 50 in
  let xt = SMap.create 20 in
  p |> List.iter (fun d ->
    match d with
    | DType t ->
      SMap.add tt (string_of_name t.dt_name) t;
      (match t.dt_body with
       | TVariant cs ->
         cs |> List.iter (fun (c, fs) -> SMap.add ct (string_of_name c) (t, fs))
       | _ -> ())
    | DExternal x ->
      SMap.add xt (string_of_name x.dx_name)
        (match x.dx_target with
         | Some "" | None -> c_name x.dx_name
         | Some t -> escape_kw (sanitize t))
    | _ -> ());
  types := tt; ctors := ct; externs := xt;

  (* Only the standard library, and only the parts that are used unavoidably:
     fixed-width integers, malloc/free/abort, memmove, and bool. *)
  let header =
    "/* Generated by F* Custard extraction. Do not edit. */\n\
     #include <stdint.h>\n\
     #include <stdlib.h>\n\
     #include <stdbool.h>\n\
     #include <string.h>\n\
     \n\
     /* The sole inhabited erased value (section 5.1).  A distinct typedef \
     rather\n\
        than void, so that it can be stored in a variable and returned like \
     any\n\
        other value. */\n\
     typedef uint8_t custard_unit;\n" in

  let includes =
    p |> List.collect (fun d ->
      match d with
      | DExternal ({ dx_header = Some h }) -> ["#include \"" ^ h ^ "\""]
      | _ -> []) in
  let includes = dedup includes in

  let exts = p |> List.collect (fun d ->
    match d with
    | DExternal x -> (match extern_decl x with Some s -> [s] | None -> [])
    | DExn _ ->
      current := "an exception declaration";
      reject "an exception declaration" ["C has no exceptions."]
    | _ -> []) in

  let tys = p |> List.collect (fun d ->
    match d with
    | DType t ->
      current := string_of_name t.dt_name;
      (match type_decl t with Some s -> [s] | None -> [])
    | _ -> []) in

  (* Every function is declared before any is defined, so that a recursive
     group needs no analysis: the SCC pass has already grouped them, but C
     wants a prototype, not a group. *)
  let protos = p |> List.collect (fun d ->
    match d with
    | DLet l when Cons? l.dl_binders ->
      current := string_of_name l.dl_name;
      reset_scope ();
      l.dl_binders |> List.iter (fun b -> let _ = bind_var b.b_name in ());
      [(if l.dl_flags |> List.existsb Private? then "static " else "") ^
       signature l ^ ";\n"]
    | _ -> []) in

  let defs = p |> List.collect (fun d ->
    match d with
    | DLet l -> [(if l.dl_flags |> List.existsb Private? then "static " else "") ^
                 let_decl l]
    | _ -> []) in

  (* Custard compiles standalone programs (section 4.4).  An entry point
     returning a machine integer is the process exit status, which is what a C
     [main] returns; anything else is run for its effect. *)
  let mains = p |> List.collect (fun d ->
    match d with
    | DLet l when l.dl_flags |> List.existsb Entrypoint? ->
      current := string_of_name l.dl_name;
      let args = String.concat ", "
                   (l.dl_binders |> List.map (fun _ -> "((custard_unit)0)")) in
      let call = c_name l.dl_name ^ "(" ^ args ^ ")" in
      (match l.dl_ret with
       | TInt _ -> ["int main(void) {\n  return (int)" ^ call ^ ";\n}\n"]
       | _ -> ["int main(void) {\n  (void)" ^ call ^ ";\n  return 0;\n}\n"])
    | _ -> []) in

  let body =
    header ^ "\n" ^
  (match includes with [] -> "" | _ -> String.concat "\n" includes ^ "\n\n") ^
  String.concat "" tys ^ (match tys with [] -> "" | _ -> "\n") ^
  String.concat "" exts ^ (match exts with [] -> "" | _ -> "\n") ^
  String.concat "" protos ^ (match protos with [] -> "" | _ -> "\n") ^
  String.concat "\n" defs ^
    (match mains with [] -> "" | _ -> "\n" ^ String.concat "\n" mains) in
  body
