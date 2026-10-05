(*
   Copyright 2008-2025 Microsoft Research

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

(* The F* grammar, written with the Pratt engine of FStarC.Parser.Pratt.

   This is a port of the former Menhir grammar FStarC_Parser_Parse.mly,
   which stage0 still uses to parse the compiler. It is meant to produce
   exactly the same ASTs (including ranges and generated names) as the
   Menhir parser on all inputs that Menhir accepts.

   Precedences of terms. A term position asks for a minimal precedence;
   the named nonterminals of the Menhir grammar correspond to:

     0  term                  ;  ;;  ;op  x <-- e; e
     1  noSeqTerm             if, match, let, fun-like keywords, a.(i) <- e
     5                        e <: t    e $: t
    10  typ (tmIff)           <==>
    20  (tmImplies)           ==>
    30  tmArrow               ->        (also domains like #x:t -> ...)
    40  tmFormula             \/
    50  tmConjunction         /\
    60  tmTuple               ,
    71  tmEq                  :=
    72..79                    0a 0b (0c =) 0d |> <| 1 (2 -)  ;  - ` ' prefix (80)
    81  tmNoEq                ::
    82..86                    & 3L 3R `f` 4
   100  applications, atoms, records, fun, forall, exists, ~, `%

   Arrows are special: in [tmArrow(tmNoEq)] (type ascriptions) the
   domains of arrows are tmNoEq, and in [simpleArrow] (binder types)
   they are tmEqNoRefinement; see [ctx] in FStarC.Parser.Pratt. *)
module FStarC.Parser.Grammar

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Parser.AST
open FStarC.Ident
open FStarC.Const
open FStarC.Parser.Pratt
module L  = FStarC.Parser.Lexer
module R  = FStarC.Range
module RO = FStarC.Range.Ops
module E  = FStarC.Errors
module Codes = FStarC.Errors.Codes
module C  = FStarC.Parser.Const
module SS = FStarC.Syntax.Syntax
module AU = FStarC.Parser.AST.Util
module GS = FStarC.GenSym
module SI = FStarC.SmallInt
module PSM = FStarC.PSMap

(* ---------------------------------------------------------------------- *)
(* Contexts and term entry points                                         *)
(* ---------------------------------------------------------------------- *)

let dflt       : ctx = { noref = false; dom = 40; paren_doms = true }
let noeq_ctx   : ctx = { noref = false; dom = 81; paren_doms = true }
let simple_ctx : ctx = { noref = true;  dom = 71; paren_doms = false }
let noref_ctx  : ctx = { noref = true;  dom = 40; paren_doms = true }

let p_term          ps = term_at ps dflt 0
let p_noSeqTerm     ps = term_at ps dflt 1
let p_typ           ps = term_at ps dflt 10
let p_tmArrowFormula ps = term_at ps dflt 30
let p_tmFormula     ps = term_at ps dflt 40
let p_tmConjunction ps = term_at ps dflt 50
let p_tmTuple       ps = term_at ps dflt 60
let p_tmEq          ps = term_at ps dflt 71
let p_tmNoEq        ps = term_at ps dflt 81
let p_tmArrowNoEq   ps = term_at ps noeq_ctx 30
let p_simpleArrow   ps = term_at ps simple_ctx 30
let p_tmEqNoRef     ps = term_at ps noref_ctx 71
let p_formula (ps:pstate) : ML term =
  let e = p_noSeqTerm ps in
  { e with level = Formula }

(* ---------------------------------------------------------------------- *)
(* Generic helpers                                                        *)
(* ---------------------------------------------------------------------- *)

let syntax_error (#a:Type) (r:R.range) (msg:string) : ML a =
  E.raise_error_text r Codes.Fatal_SyntaxError msg

let mk_id_tok (ps:pstate) (t:L.token) (s:string) : ML ident =
  mk_ident (s, tok_rng ps t)

(* right_flexible_list(SEP, X): X (SEP X)* SEP?, possibly empty. [stop]
   tells whether the list is over (the next token is the closer). *)
let rec rflex_rest (#a:Type) (ps:pstate) (sep:string) (closer:string) (x:pstate -> ML a) : ML (list a) =
  if is ps closer then []
  else begin
    let v = x ps in
    if accept ps sep then v :: rflex_rest ps sep closer x
    else [v]
  end

let rflex (#a:Type) (ps:pstate) (sep closer:string) (x:pstate -> ML a) : ML (list a) =
  rflex_rest ps sep closer x

let rflex_nonempty (#a:Type) (ps:pstate) (sep closer:string) (x:pstate -> ML a) : ML (list a) =
  let v = x ps in
  if accept ps sep then v :: rflex_rest ps sep closer x
  else [v]

(* separated_nonempty_list(SEP, X) *)
let rec sep_nonempty (#a:Type) (ps:pstate) (sep:string) (x:pstate -> ML a) : ML (list a) =
  let v = x ps in
  if accept ps sep then v :: sep_nonempty ps sep x
  else [v]

let opt (#a:Type) (ps:pstate) (k:string) (x:pstate -> ML a) : ML (option a) =
  if accept ps k then Some (x ps) else None

(* ---------------------------------------------------------------------- *)
(* Identifiers                                                            *)
(* ---------------------------------------------------------------------- *)

let p_lident (ps:pstate) : ML ident =
  let t = expect ps "IDENT" in
  mk_id_tok ps t t.text

let p_uident (ps:pstate) : ML ident =
  let t = expect ps "NAME" in
  mk_id_tok ps t t.text

let p_ident (ps:pstate) : ML ident =
  if is ps "IDENT" then p_lident ps else p_uident ps

let lidentOrUnderscore (ps:pstate) : ML ident =
  if is ps "UNDERSCORE" then
    let t = advance ps in
    gen (tok_rng ps t)
  else p_lident ps

(* path(Id): (NAME DOT)* Id. Returns the identifiers and whether the last
   one is a NAME. The path continues as long as a NAME is followed by a
   DOT and an identifier. *)
let p_path (ps:pstate) : ML (list ident & bool) =
  let rec go (acc:list ident) : ML (list ident & bool) =
    let t = peek ps in
    if t.kind = "IDENT" then
      (ignore (advance ps); (rev (mk_id_tok ps t t.text :: acc), false))
    else if t.kind = "NAME" then begin
      ignore (advance ps);
      let acc = mk_id_tok ps t t.text :: acc in
      let k1 = peek_kind_n ps 1 in
      if is ps "DOT" && (k1 = "IDENT" || k1 = "NAME") then
        (ignore (advance ps); go acc)
      else (rev acc, true)
    end
    else fail ps
  in
  go []

let p_qlident (ps:pstate) : ML lident =
  let ids, is_name = p_path ps in
  if is_name then fail ps else lid_of_ids ids

let p_quident (ps:pstate) : ML lident =
  let ids, is_name = p_path ps in
  if not is_name then fail ps else lid_of_ids ids

(* ---------------------------------------------------------------------- *)
(* Constants                                                              *)
(* ---------------------------------------------------------------------- *)

let machine_int_kinds : list (string & signedness & width) = [
  "UINT8",  Unsigned, Int8;
  "INT8",   Signed,   Int8;
  "UINT16", Unsigned, Int16;
  "INT16",  Signed,   Int16;
  "UINT32", Unsigned, Int32;
  "INT32",  Signed,   Int32;
  "UINT64", Unsigned, Int64;
  "INT64",  Signed,   Int64;
  "SIZET",  Unsigned, Sizet;
]

let rec find_machine_int (k:string) (l:list (string & signedness & width))
  : option (signedness & width) =
  match l with
  | [] -> None
  | (k', s, w) :: l -> if k = k' then Some (s, w) else find_machine_int k l

let is_constant_kind (k:string) : bool =
  match k with
  | "LPAREN_RPAREN" | "INT" | "CHAR" | "STRING" | "TRUE" | "FALSE" | "REAL"
  | "REIFY" | "RANGE_OF" | "SET_RANGE_OF"
  | "UINT8" | "INT8" | "UINT16" | "INT16" | "UINT32" | "INT32"
  | "UINT64" | "INT64" | "SIZET" -> true
  | _ -> false

let constant (ps:pstate) : ML sconst =
  let t = peek ps in
  if not (is_constant_kind t.kind) then fail ps
  else begin
    ignore (advance ps);
    match t.kind with
    | "LPAREN_RPAREN" -> Const_unit
    | "INT" -> let (v, b) = parse_int_literal t.text in Const_int (v, b)
    | "CHAR" ->
      (match t.extra with
       | L.CharLit c -> Const_char (FStarC.Util.char_of_int c)
       | _ -> failwith "impossible: CHAR without payload")
    | "STRING" -> Const_string (t.text, tok_rng ps t)
    | "TRUE" -> Const_bool true
    | "FALSE" -> Const_bool false
    | "REAL" ->
      (match FStarC.Real.of_string t.text with
       | Some r -> Const_real r
       | None -> failwith ("Invalid real literal: " ^ t.text))
    | "REIFY" -> Const_reify None
    | "RANGE_OF" -> Const_range_of
    | "SET_RANGE_OF" -> Const_set_range_of
    | k ->
      match find_machine_int k machine_int_kinds with
      | Some (s, w) ->
        let (v, b) = parse_int_literal t.text in
        Const_machine_int (v, b, s, w)
      | None -> failwith "impossible"
  end

(* ---------------------------------------------------------------------- *)
(* Operators                                                              *)
(* ---------------------------------------------------------------------- *)

(* binop_name: the name of an infix operator token, if it is one *)
let binop_name_of (t:L.token) : option string =
  match t.kind with
  | "OPINFIX0a" | "OPINFIX0b" | "OPINFIX0c" | "OPINFIX0d"
  | "OPINFIX1" | "OPINFIX2" | "OPINFIX3L" | "OPINFIX3R" | "OPINFIX4"
  | "OP_MIXFIX_ASSIGNMENT" | "OP_MIXFIX_ACCESS" -> Some t.text
  | "EQUALS" -> Some "="
  | "IMPLIES" -> Some "==>"
  | "CONJUNCTION" -> Some "/\\"
  | "DISJUNCTION" -> Some "\\/"
  | "IFF" -> Some "<==>"
  | "COLON_EQUALS" -> Some ":="
  | "COLON_COLON" -> Some "::"
  | _ -> None

let operator_of (t:L.token) : option string =
  match binop_name_of t with
  | Some s -> Some s
  | None ->
    match t.kind with
    | "OPPREFIX" -> Some t.text
    | "TILDE" -> Some t.text
    | "MINUS" -> Some "-"
    | "AND_OP" -> Some ("and" ^ t.text)
    | "LET_OP" -> Some ("let" ^ t.text)
    | "EXISTS_OP" -> Some ("exists" ^ t.text)
    | "FORALL_OP" -> Some ("forall" ^ t.text)
    | _ -> None

let binop_name (ps:pstate) : ML ident =
  let t = peek ps in
  match binop_name_of t with
  | Some s -> ignore (advance ps); mk_id_tok ps t s
  | None -> fail ps

let operator (ps:pstate) : ML ident =
  let t = peek ps in
  match operator_of t with
  | Some s -> ignore (advance ps); mk_id_tok ps t s
  | None -> fail ps

(* Is the input LPAREN operator RPAREN? *)
let is_op_paren (ps:pstate) : ML bool =
  is ps "LPAREN" && Some? (operator_of (peek_n ps 1)) && peek_kind_n ps 2 = "RPAREN"

(* LPAREN operator RPAREN, returning the operator *)
let op_paren (ps:pstate) : ML ident =
  ignore (expect ps "LPAREN");
  let op = operator ps in
  ignore (expect ps "RPAREN");
  op

let compiled_op_ident (op:ident) : ML ident =
  mk_ident (compile_op (string_of_id op) (range_of_id op), range_of_id op)

let lidentOrOperator (ps:pstate) : ML ident =
  if is_op_paren ps then compiled_op_ident (op_paren ps) else p_lident ps

let identOrOperator (ps:pstate) : ML ident =
  if is_op_paren ps then compiled_op_ident (op_paren ps) else p_ident ps

let qlidentOrOperator (ps:pstate) : ML lident =
  if is_op_paren ps then
    let id = op_paren ps in
    lid_of_ns_and_id [] (id_of_text (compile_op (string_of_id id) (range_of_id id)))
  else p_qlident ps

(* ---------------------------------------------------------------------- *)
(* Token classes                                                          *)
(* ---------------------------------------------------------------------- *)

(* Tokens that can start an atomicTerm *)
let is_atomic_start_kind (k:string) : bool =
  match k with
  | "UNDERSCORE" | "OPPREFIX" | "LPAREN" | "LENS_PAREN_LEFT"
  | "NAME" | "IDENT" | "BEGIN" | "LBRACK"
  | "SEQ_BANG_LBRACK" | "PERCENT_LBRACK" | "BANG_LBRACE" -> true
  | _ -> is_constant_kind k

let is_atomic_start (ps:pstate) : ML bool = is_atomic_start_kind (peek_kind ps)

(* Tokens that start an onlyTrailingTerm *)
let is_quantifier_kind (k:string) : bool =
  match k with
  | "FORALL" | "EXISTS" | "FORALL_OP" | "EXISTS_OP" -> true
  | _ -> false

let is_only_trailing_start (ps:pstate) : ML bool =
  let k = peek_kind ps in
  k = "FUN" || is_quantifier_kind k

let pragma_start_kinds : list string = [
  "PRAGMA_SHOW_OPTIONS"; "PRAGMA_SET_OPTIONS"; "PRAGMA_RESET_OPTIONS";
  "PRAGMA_PUSH_OPTIONS"; "PRAGMA_POP_OPTIONS"; "PRAGMA_RESTART_SOLVER";
  "PRAGMA_PRINT_EFFECTS_GRAPH"; "PRAGMA_CHECK"; "PRAGMA_EVAL";
]

let qualifier_kinds : list string = [
  "ASSUME"; "INLINE"; "UNFOLDABLE"; "INLINE_FOR_EXTRACTION"; "UNFOLD";
  "IRREDUCIBLE"; "NOEXTRACT"; "TOTAL"; "PRIVATE"; "NOEQUALITY";
  "UNOPTEQUALITY"; "NEW"; "LOGIC"; "OPAQUE"; "REIFIABLE"; "REFLECTABLE";
]

let start_of_next_decl_kinds : list string =
  FStar.List.Tot.append pragma_start_kinds (FStar.List.Tot.append qualifier_kinds [
    "EOF"; "LBRACK_AT"; "LBRACK_AT_AT"; "CLASS"; "INSTANCE"; "OPEN"; "FRIEND";
    "INCLUDE"; "MODULE"; "TYPE"; "EFFECT"; "LET"; "VAL"; "SPLICE"; "SPLICET";
    "EXCEPTION"; "NEW_EFFECT"; "SUB_EFFECT"; "BLOB"; "USE_LANG_BLOB";
  ])

(* ---------------------------------------------------------------------- *)
(* Helpers from the header of the Menhir grammar                          *)
(* ---------------------------------------------------------------------- *)

type tc_constraint = {
  tc_id : ident;
  tc_t  : term;
  tc_r  : R.range;
}

let pattern_must_be_binder (p:pattern) : ML binder =
  match p.pat with
  | PatConst Const_unit ->
    let x = gen p.prange in
    let u = unit_type p.prange in
    mk_binder (Annotated (x, u)) p.prange Expr None
  | PatAscribed ({ pat = PatVar (x, aq, attrs) }, (t, _)) ->
    mk_binder_with_attrs (Annotated (x, t)) p.prange Expr aq attrs
  | PatVar (x, aq, attrs) ->
    mk_binder_with_attrs (Variable x) p.prange Expr aq attrs
  | PatAscribed ({ pat = PatWild (aq, attrs) }, (t, _)) ->
    let x = gen p.prange in
    mk_binder_with_attrs (Annotated (x, t)) p.prange Expr aq attrs
  | PatWild (aq, attrs) ->
    let x = gen p.prange in
    mk_binder_with_attrs (Variable x) p.prange Expr aq attrs
  | _ ->
    syntax_error p.prange ("Must be a simple binder: " ^ pat_to_string p)

(* In order: for each x, for each constraint *)
let expand_inline_constraints (cts:list term) (xs:list ident) : ML (list pattern) =
  let rec for_cts (x:ident) (cts:list term) : ML (list pattern) =
    match cts with
    | [] -> []
    | ct :: cts ->
      let r = ct.range in
      let x_t = mk_term (Var (lid_of_ids [x])) r Expr in
      let ct = mk_term (App (ct, x_t, Nothing)) r Expr in
      let id = gen r in
      let p = mk_pattern (PatAscribed (mk_pattern (PatVar (id, Some TypeClassArg, [])) r, (ct, None))) r in
      p :: for_cts x cts
  in
  let rec for_xs (xs:list ident) : ML (list pattern) =
    match xs with
    | [] -> []
    | x :: xs ->
      let ps = for_cts x cts in
      FStar.List.Tot.append ps (for_xs xs)
  in
  for_xs xs

let rec pat_names (bs:list pattern) : ML (list ident) =
  match bs with
  | [] -> []
  | b :: bs' ->
    match b.pat with
    | PatAscribed ({ pat = PatVar (x, _, _) }, _)
    | PatVar (x, _, _) -> x :: pat_names bs'
    | _ ->
      syntax_error b.prange
        ("Inline constraints require simple variable binders, got: " ^ pat_to_string b)

(* Map in order (the function may generate names) *)
let rec map_inorder (#a #b:Type) (f:a -> ML b) (l:list a) : ML (list b) =
  match l with
  | [] -> []
  | x :: xs -> let y = f x in y :: map_inorder f xs

let rec mapi_inorder (#a #b:Type) (i:int) (f:int -> a -> ML b) (l:list a) : ML (list b) =
  match l with
  | [] -> []
  | x :: xs -> let y = f i x in y :: mapi_inorder (i + 1) f xs

let thunk_at (ps:pstate) (i0:pos) (t:term) : ML term =
  let r = loc ps i0 in
  mk_term (Abs ([mk_pattern (PatWild (None, [])) r], t)) r Expr

let thunk2_at (ps:pstate) (i0:pos) (t:term) : ML term =
  let r = loc ps i0 in
  let u = mk_term (Const Const_unit) r Expr in
  let t = mk_term (Seq (u, t)) r Expr in
  mk_term (Abs ([mk_pattern (PatWild (None, [])) r], t)) r Expr

(* ---------------------------------------------------------------------- *)
(* Qualifiers and attributes of binders                                   *)
(* ---------------------------------------------------------------------- *)

let semiColonTermList (ps:pstate) : ML (list term) =
  rflex ps "SEMICOLON" "RBRACK" p_noSeqTerm

let is_aqual_start (ps:pstate) : ML bool =
  match peek_kind ps with "HASH" | "DOLLAR" -> true | _ -> false

(* aqual: HASH LBRACK thunk(term) RBRACK | HASH | DOLLAR *)
let p_aqual (ps:pstate) : ML arg_qualifier =
  if accept ps "DOLLAR" then Equality
  else begin
    ignore (expect ps "HASH");
    if accept ps "LBRACK" then begin
      let i0 = !ps.idx in
      let t = p_term ps in
      let t = thunk_at ps i0 t in
      ignore (expect ps "RBRACK");
      Meta t
    end
    else Implicit
  end

let binderAttributes (ps:pstate) : ML (list term) =
  ignore (expect ps "LBRACK_AT_AT_AT");
  let t = semiColonTermList ps in
  ignore (expect ps "RBRACK");
  t

let aqual_attrs (ps:pstate) : ML (aqual & list term) =
  let aq = if is_aqual_start ps then Some (p_aqual ps) else None in
  let attrs = if is ps "LBRACK_AT_AT_AT" then binderAttributes ps else [] in
  (aq, attrs)

(* aqualifiedWithAttrs(lidentOrUnderscore) *)
let aqualified_lidentOrUnderscore (ps:pstate) : ML ((aqual & list term) & ident) =
  let qa = aqual_attrs ps in
  let x = lidentOrUnderscore ps in
  (qa, x)

let is_aqualified_start_kind (k:string) : bool =
  k = "HASH" || k = "DOLLAR" || k = "LBRACK_AT_AT_AT"

let refineOpt (ps:pstate) : ML (option term) =
  if accept ps "LBRACE" then begin
    let phi = p_formula ps in
    ignore (expect ps "RBRACE");
    Some phi
  end else None

(* ---------------------------------------------------------------------- *)
(* Universes                                                              *)
(* ---------------------------------------------------------------------- *)

let is_atomic_universe_start (ps:pstate) : ML bool =
  let k = peek_kind ps in
  k = "UNDERSCORE" || k = "INT" || k = "IDENT" || k = "LPAREN"

let rec atomicUniverse (ps:pstate) : ML term =
  let i0 = !ps.idx in
  let t = peek ps in
  match t.kind with
  | "UNDERSCORE" -> ignore (advance ps); mk_term Wild (loc ps i0) Expr
  | "INT" ->
    ignore (advance ps);
    let (v, b) = parse_int_literal t.text in
    mk_term (Const (Const_int (v, b))) (loc ps i0) Expr
  | "IDENT" ->
    let u = p_lident ps in
    mk_term (Uvar u) (range_of_id u) Expr
  | "LPAREN" ->
    ignore (advance ps);
    let u = universeFrom ps in
    ignore (expect ps "RPAREN");
    u
  | _ -> fail ps

and universeFrom (ps:pstate) : ML term =
  let i0 = !ps.idx in
  let u1 =
    let k = peek_kind ps in
    let k1 = peek_kind_n ps 1 in
    let max_follows = k1 = "UNDERSCORE" || k1 = "INT" || k1 = "IDENT" || k1 = "LPAREN" in
    if (k = "IDENT" && max_follows) || k = "NAME" then begin
      let max = p_ident ps in
      let i1 = !ps.idx in
      let rec args () : ML (list term) =
        let u = atomicUniverse ps in
        if is_atomic_universe_start ps then u :: args () else [u]
      in
      let us = args () in
      if string_of_id max <> string_of_lid C.max_lid then
        E.log_issue_text (rng ps i0 i1) Codes.Error_InvalidUniverseVar
          ("A lower case ident " ^ string_of_id max ^
           " was found in a universe context. " ^
           "It should be either max or a universe variable 'usomething.");
      let max = mk_term (Var (lid_of_ids [max])) (rng ps i0 i1) Expr in
      mkApp max (map (fun u -> u, Nothing) us) (loc ps i0)
    end
    else atomicUniverse ps
  in
  universeFrom_rest ps i0 u1

and universeFrom_rest (ps:pstate) (i0:pos) (u1:term) : ML term =
  if is ps "OPINFIX2" then begin
    let i_u1_end = !ps.idx in
    let t = advance ps in
    let op_plus = t.text in
    let i2 = !ps.idx in
    let u2 =
      (* the right operand of a left-associative operator *)
      let k = peek_kind ps in
      let k1 = peek_kind_n ps 1 in
      let max_follows = k1 = "UNDERSCORE" || k1 = "INT" || k1 = "IDENT" || k1 = "LPAREN" in
      if (k = "IDENT" && max_follows) || k = "NAME" then begin
        let max = p_ident ps in
        let i1 = !ps.idx in
        let rec args () : ML (list term) =
          let u = atomicUniverse ps in
          if is_atomic_universe_start ps then u :: args () else [u]
        in
        let us = args () in
        if string_of_id max <> string_of_lid C.max_lid then
          E.log_issue_text (rng ps i2 i1) Codes.Error_InvalidUniverseVar
            ("A lower case ident " ^ string_of_id max ^
             " was found in a universe context. " ^
             "It should be either max or a universe variable 'usomething.");
        let max = mk_term (Var (lid_of_ids [max])) (rng ps i2 i1) Expr in
        mkApp max (map (fun u -> u, Nothing) us) (loc ps i2)
      end
      else atomicUniverse ps
    in
    if op_plus <> "+" then
      E.log_issue_text (rng ps i0 i_u1_end) Codes.Error_OpPlusInUniverse
        ("The operator " ^ op_plus ^ " was found in universe context."
         ^ "The only allowed operator in that context is +.");
    let u = mk_term (Op (mk_id_tok ps t op_plus, [u1; u2])) (loc ps i0) Expr in
    universeFrom_rest ps i0 u
  end
  else u1

(* The index of the start and end of the last indexing term [e.(i)] with
   exactly one dot-operator, for [e.(i) <- v]. *)
let last_index : ref (pos & pos) = mk_ref (SI.minus_one, SI.minus_one)

let is_dot_operator_kind (k:string) : bool =
  k = "DOT_LPAREN" || k = "DOT_LBRACK" || k = "DOT_LBRACK_BAR" || k = "DOT_LENS_PAREN_LEFT"

let is_genBinder_start_kind (k:string) : bool =
  match k with
  | "LBRACE_BAR" | "LPAREN" | "DOT_DOT" | "LBRACK" | "LBRACE"
  | "LENS_PAREN_LEFT" | "MINUS" | "BACKTICK_PERC"
  | "HASH" | "DOLLAR" | "LBRACK_AT_AT_AT" | "IDENT"
  | "UNDERSCORE" | "NAME" -> true
  | _ -> is_constant_kind k

let is_atomic_pattern_start_kind (k:string) : bool =
  k <> "LBRACE_BAR" && is_genBinder_start_kind k

let is_multiBinder_start_kind (k:string) : bool =
  match k with
  | "LBRACE_BAR" | "LPAREN" | "LPAREN_RPAREN" | "HASH"
  | "DOLLAR" | "LBRACK_AT_AT_AT" | "IDENT" | "UNDERSCORE" -> true
  | _ -> false

(* ---------------------------------------------------------------------- *)
(* Atoms, applications, patterns and binders                              *)
(* ---------------------------------------------------------------------- *)

(* atomicTerm. The boolean tells whether the term is an atomicTermQUident
   (which cannot be indexed). *)
let rec atomic (ps:pstate) : ML (term & bool) =
  let i0 = !ps.idx in
  let t = peek ps in
  match t.kind with
  | "UNDERSCORE" -> ignore (advance ps); (mk_term Wild (loc ps i0) Un, false)
  | "OPPREFIX" ->
    ignore (advance ps);
    let op = mk_id_tok ps t t.text in
    let e, q = atomic ps in
    (mk_term (Op (op, [e])) (loc ps i0) Expr, q)
  | "LPAREN" ->
    if is_op_paren ps then begin
      let op = op_paren ps in
      (mk_term (Op (op, [])) (loc ps i0) Un, false)
    end else begin
      ignore (advance ps);
      let e = p_term ps in
      let e1 =
        if accept ps "SUBKIND" then begin
          let t = p_typ ps in
          ignore (expect ps "RPAREN");
          mk_term (Ascribed (e, { t with level = Type_level }, None, false)) (loc ps i0) Type_level
        end else (ignore (expect ps "RPAREN"); e)
      in
      let e = mk_term (Paren e1) (loc ps i0) e.level in
      (projections ps i0 e, false)
    end
  | "LENS_PAREN_LEFT" ->
    ignore (advance ps);
    let e0 = p_tmEq ps in
    ignore (expect ps "COMMA");
    let el = sep_nonempty ps "COMMA" p_tmEq in
    ignore (expect ps "LENS_PAREN_RIGHT");
    (mkDTuple (e0 :: el) (loc ps i0), false)
  | "BEGIN" ->
    ignore (advance ps);
    let e = p_term ps in
    ignore (expect ps "END");
    (e, false)
  | "IDENT"
  | "NAME" ->
    let ids, is_name = p_path ps in
    let r_id = loc ps i0 in
    let lid = lid_of_ids ids in
    if not is_name then begin
      let e = mk_term (if C.is_name lid then Name lid else Var lid) r_id Un in
      (projections ps i0 e, false)
    end
    else if accept ps "QMARK_DOT" then begin
      let id = p_lident ps in
      let e = mk_term (Projector (lid, id)) (loc ps i0) Expr in
      (projections ps i0 e, false)
    end
    else if accept ps "QMARK" then begin
      let e = mk_term (Discrim lid) (loc ps i0) Un in
      (projections ps i0 e, false)
    end
    else if accept ps "DOT_LPAREN" then begin
      let t = p_term ps in
      ignore (expect ps "RPAREN");
      (mk_term (LetOpen (lid, t)) (loc ps i0) Expr, true)
    end
    else (mk_term (Name lid) r_id Un, true)
  | "LBRACK" ->
    ignore (advance ps);
    let es = semiColonTermList ps in
    ignore (expect ps "RBRACK");
    (projections ps i0 (mkListLit (loc ps i0) es), false)
  | "SEQ_BANG_LBRACK" ->
    ignore (advance ps);
    let es = semiColonTermList ps in
    ignore (expect ps "RBRACK");
    (projections ps i0 (mkSeqLit (loc ps i0) es), false)
  | "PERCENT_LBRACK" ->
    ignore (advance ps);
    let es = semiColonTermList ps in
    ignore (expect ps "RBRACK");
    (projections ps i0 (mk_term (LexList es) (loc ps i0) Type_level), false)
  | "BANG_LBRACE" ->
    ignore (advance ps);
    let es = rflex ps "COMMA" "RBRACE" app_term_full in
    ignore (expect ps "RBRACE");
    let e = mkRefSet (loc ps i0) es in
    (projections ps i0 e, false)
  | k ->
    if is_constant_kind k then begin
      let c = constant ps in
      (mk_term (Const c) (loc ps i0) Expr, false)
    end
    else fail ps

(* list(DOT qlident) after a projectionLHS *)
and projections (ps:pstate) (i0:pos) (e:term) : ML term =
  let rec fields () : ML (list lident) =
    let k1 = peek_kind_n ps 1 in
    if is ps "DOT" && (k1 = "IDENT" || k1 = "NAME") then begin
      ignore (advance ps);
      let lid = p_qlident ps in
      lid :: fields ()
    end else begin
      (* Menhir shifts a DOT here before failing; report errors past it *)
      if is ps "DOT" && SI.(!ps.idx + one > !ps.furthest) then ps.furthest := SI.(!ps.idx + one);
      []
    end
  in
  let fs = fields () in
  let r = loc ps i0 in
  fold_left (fun e lid -> mk_term (Project (e, lid)) r Expr) e fs

and atomicTerm (ps:pstate) : ML term = fst (atomic ps)

(* indexingTerm *)
and indexing_term (ps:pstate) : ML (term & bool) =
  let i0 = !ps.idx in
  let e, q = atomic ps in
  if q then (e, q)
  else begin
    let rec go (e:term) (n:SI.t) : ML (term & SI.t) =
      let t = peek ps in
      let closer =
        match t.kind with
        | "DOT_LPAREN" -> Some (".()", "RPAREN")
        | "DOT_LBRACK" -> Some (".[]", "RBRACK")
        | "DOT_LBRACK_BAR" -> Some (".[||]", "BAR_RBRACK")
        | "DOT_LENS_PAREN_LEFT" -> Some (".(||)", "LENS_PAREN_RIGHT")
        | _ -> None
      in
      match closer with
      | None -> (e, n)
      | Some (name, closer) ->
        let iop = !ps.idx in
        ignore (advance ps);
        let op = mk_id_tok ps t name in
        let e2 = p_term ps in
        ignore (expect ps closer);
        let r = loc ps iop in
        let e = mk_term (Op (op, [e; e2])) (RO.union_ranges e.range r) Expr in
        go e SI.(n + one)
    in
    let e, n = go e SI.zero in
    if n = SI.one then last_index := (i0, !ps.idx);
    (e, false)
  end

(* appTermArgs / appTermArgsNoRecordExp *)
and app_args (ps:pstate) (noref:bool) : ML (list (term & imp)) =
  if is ps "UNIV_HASH" then begin
    ignore (advance ps);
    let u = atomicUniverse ps in
    (u, UnivApp) :: app_args ps noref
  end else begin
    let k1 = peek_kind_n ps 1 in
    let hash_arg =
      is ps "HASH" &&
      (is_atomic_start_kind k1 ||
       (not noref && (k1 = "LBRACE" || k1 = "FUN" || is_quantifier_kind k1)))
    in
    let h = if hash_arg then (ignore (advance ps); Hash) else Nothing in
    if is_atomic_start ps then begin
      let a, _ = indexing_term ps in
      (a, h) :: app_args ps noref
    end
    else if not noref && is ps "LBRACE" then begin
      let a = record_term ps in
      (a, h) :: app_args ps noref
    end
    else if not noref && is_only_trailing_start ps then begin
      let a = only_trailing ps in
      [(a, h)]
    end
    else []
  end

(* appTermCommon(args) *)
and app_term (ps:pstate) (noref:bool) : ML term =
  let i0 = !ps.idx in
  let head, _ = indexing_term ps in
  let args = app_args ps noref in
  mkApp head args (loc ps i0)

(* appTerm, including onlyTrailingTerm *)
and app_term_full (ps:pstate) : ML term =
  if is_only_trailing_start ps then only_trailing ps
  else app_term ps false

(* LBRACE recordExp RBRACE *)
and record_term (ps:pstate) : ML term =
  ignore (expect ps "LBRACE");
  let i1 = !ps.idx in
  let base = attempt ps (fun () ->
    let e = app_term_full ps in
    ignore (expect ps "WITH");
    e)
  in
  let fields = rflex_nonempty ps "SEMICOLON" "RBRACE" simpleDef in
  let r = loc ps i1 in
  ignore (expect ps "RBRACE");
  mk_term (Record (base, fields)) r Expr

and simpleDef (ps:pstate) : ML (lident & term) =
  let i0 = !ps.idx in
  let lid = qlidentOrOperator ps in
  if accept ps "EQUALS" then (lid, p_noSeqTerm ps)
  else (lid, mk_term (Var (lid_of_ids [ident_of_lid lid])) (loc ps i0) Un)

(* onlyTrailingTerm *)
and only_trailing (ps:pstate) : ML term =
  let i0 = !ps.idx in
  let t = advance ps in
  match t.kind with
  | "FUN" ->
    let rec pats () : ML (list (list pattern)) =
      let p = genBinder ps in
      if is ps "RARROW" then [p] else p :: pats ()
    in
    let pats = pats () in
    ignore (expect ps "RARROW");
    let e = p_term ps in
    mk_term (Abs (flatten pats, e)) (loc ps i0) Un
  | k ->
    if not (is_quantifier_kind k) then fail ps else begin
    let bs = binders ps in
    ignore (expect ps "DOT");
    let i_dot = !ps.idx in
    let trigger =
      if accept ps "LBRACE_COLON_PATTERN" then begin
        let pats = sep_nonempty ps "DISJUNCTION" (fun ps -> sep_nonempty ps "SEMICOLON" app_term_full) in
        ignore (expect ps "RBRACE");
        pats
      end else []
    in
    let e = p_term ps in
    match bs with
    | [] ->
      E.raise_error_text (rng ps i0 i_dot) Codes.Fatal_MissingQuantifierBinder "Missing binders for a quantifier"
    | _ ->
      let idents = idents_of_binders bs (rng ps i0 i_dot) in
      let q =
        match k with
        | "FORALL" -> QForall (bs, (idents, trigger), e)
        | "EXISTS" -> QExists (bs, (idents, trigger), e)
        | "FORALL_OP" -> QuantOp (mk_id_tok ps t ("forall" ^ t.text), bs, (idents, trigger), e)
        | _ -> QuantOp (mk_id_tok ps t ("exists" ^ t.text), bs, (idents, trigger), e)
      in
      mk_term q (loc ps i0) Formula
    end

(* atomicPattern *)
and atomicPattern (ps:pstate) : ML pattern =
  let i0 = !ps.idx in
  let t = peek ps in
  match t.kind with
  | "LPAREN" ->
    if is_op_paren ps then begin
      let op = op_paren ps in
      mk_pattern (PatOp op) (loc ps i0)
    end else begin
      match paren_pattern ps false with
      | [p] -> p
      | _ -> failwith "impossible"
    end
  | "DOT_DOT" -> ignore (advance ps); mk_pattern PatRest (loc ps i0)
  | "LBRACK" ->
    ignore (advance ps);
    let pats = rflex ps "SEMICOLON" "RBRACK" tuplePattern in
    ignore (expect ps "RBRACK");
    mk_pattern (PatList pats) (loc ps i0)
  | "LBRACE" ->
    ignore (advance ps);
    let pats = rflex ps "SEMICOLON" "RBRACE" fieldPattern in
    ignore (expect ps "RBRACE");
    mk_pattern (PatRecord pats) (loc ps i0)
  | "LENS_PAREN_LEFT" ->
    ignore (advance ps);
    let p0 = constructorPattern ps in
    ignore (expect ps "COMMA");
    let pats = sep_nonempty ps "COMMA" constructorPattern in
    ignore (expect ps "LENS_PAREN_RIGHT");
    mk_pattern (PatTuple (p0 :: pats, true)) (loc ps i0)
  | "MINUS" ->
    ignore (advance ps);
    let c = constant ps in
    let r = loc ps i0 in
    let c =
      match c with
      | Const_int (v, b) -> Const_int (0 - v, b)
      | Const_machine_int (v, b, sw, w) ->
        (match sw with
         | Signed -> Const_machine_int (0 - v, b, sw, w)
         | _ -> syntax_error r "Syntax_error: negative integer constant with unsigned width")
      | _ -> syntax_error r "Syntax_error: negative constant that is not an integer"
    in
    mk_pattern (PatConst c) r
  | "BACKTICK_PERC" ->
    ignore (advance ps);
    let q = atomicTerm ps in
    mk_pattern (PatVQuote q) (loc ps i0)
  | "NAME" ->
    let uid = p_quident ps in
    mk_pattern (PatName uid) (loc ps i0)
  | k ->
    if is_constant_kind k then begin
      let c = constant ps in
      mk_pattern (PatConst c) (loc ps i0)
    end
    else if k = "IDENT" || k = "UNDERSCORE" || is_aqualified_start_kind k then begin
      let aq, attrs = aqual_attrs ps in
      if is ps "IDENT" then begin
        let x = p_lident ps in
        mk_pattern (PatVar (x, aq, attrs)) (loc ps i0)
      end else begin
        ignore (expect ps "UNDERSCORE");
        mk_pattern (PatWild (aq, attrs)) (loc ps i0)
      end
    end
    else fail ps

(* LPAREN tuplePattern [COLON simpleArrow refineOpt [BAR constraints]] RPAREN,
   the constraints being only allowed in a genBinder *)
and paren_pattern (ps:pstate) (allow_cts:bool) : ML (list pattern) =
  let i0 = !ps.idx in
  ignore (expect ps "LPAREN");
  let i_pat = !ps.idx in
  let pat = tuplePattern ps in
  if accept ps "COLON" then begin
    let t = p_simpleArrow ps in
    let i_t = !ps.idx in
    let r = refineOpt ps in
    if allow_cts && accept ps "BAR" then begin
      let cts = rflex_nonempty ps "COMMA" "RPAREN" p_tmEqNoRef in
      ignore (expect ps "RPAREN");
      let p = mkRefinedPattern pat t true r (rng ps i_pat i_t) (loc ps i0) in
      let names = pat_names [p] in
      p :: expand_inline_constraints cts names
    end else begin
      ignore (expect ps "RPAREN");
      [mkRefinedPattern pat t true r (rng ps i_pat i_t) (loc ps i0)]
    end
  end else begin
    ignore (expect ps "RPAREN");
    [pat]
  end

and fieldPattern (ps:pstate) : ML (lident & pattern) =
  let i0 = !ps.idx in
  let lid = p_qlident ps in
  if accept ps "EQUALS" then (lid, tuplePattern ps)
  else (lid, mk_pattern (PatVar (ident_of_lid lid, None, [])) (loc ps i0))

and constructorPattern (ps:pstate) : ML pattern =
  let i0 = !ps.idx in
  let pat =
    if is ps "NAME" then begin
      let uid = p_quident ps in
      let r_uid = loc ps i0 in
      if is_atomic_pattern_start_kind (peek_kind ps) then begin
        let rec args () : ML (list pattern) =
          let p = atomicPattern ps in
          if is_atomic_pattern_start_kind (peek_kind ps) then p :: args () else [p]
        in
        let args = args () in
        let head = mk_pattern (PatName uid) r_uid in
        mk_pattern (PatApp (head, args)) (loc ps i0)
      end
      else mk_pattern (PatName uid) r_uid
    end
    else atomicPattern ps
  in
  if accept ps "COLON_COLON" then begin
    let i_rest = !ps.idx in
    let rest = constructorPattern ps in
    mk_pattern (consPat (loc ps i_rest) pat rest) (loc ps i0)
  end
  else pat

and tuplePattern (ps:pstate) : ML pattern =
  let i0 = !ps.idx in
  match sep_nonempty ps "COMMA" constructorPattern with
  | [x] -> x
  | l -> mk_pattern (PatTuple (l, false)) (loc ps i0)

and p_tc_constraint (ps:pstate) : ML tc_constraint =
  let i0 = !ps.idx in
  let k = peek_kind ps in
  let id =
    if (k = "IDENT" || k = "UNDERSCORE") && peek_kind_n ps 1 = "COLON" then begin
      let id = lidentOrUnderscore ps in
      ignore (expect ps "COLON");
      Some id
    end else None
  in
  let t = p_simpleArrow ps in
  let r = if None? id then eps_loc ps i0 else loc ps i0 in
  let id = match id with Some id -> id | None -> gen r in
  { tc_id = id; tc_t = t; tc_r = r }

and tc_constraints (ps:pstate) : ML (list tc_constraint) =
  rflex_nonempty ps "COMMA" "BAR_RBRACE" p_tc_constraint

and type_tc_constraints (ps:pstate) : ML (list term) =
  if accept ps "BAR" then rflex_nonempty ps "COMMA" "RPAREN" p_tmEqNoRef
  else []

(* LPAREN aqualifiedWithAttrs(lidentOrUnderscore)+ COLON, the common prefix
   of the multi-identifier binders *)
and multi_ids (ps:pstate) (min:int) : ML (list ((aqual & list term) & ident)) =
  ignore (expect ps "LPAREN");
  let rec go () : ML (list ((aqual & list term) & ident)) =
    let k = peek_kind ps in
    if k = "IDENT" || k = "UNDERSCORE" || is_aqualified_start_kind k then begin
      let q = aqualified_lidentOrUnderscore ps in
      q :: go ()
    end else []
  in
  let ids = go () in
  if length ids < min then fail ps;
  ignore (expect ps "COLON");
  ids

and genBinder (ps:pstate) : ML (list pattern) =
  let i0 = !ps.idx in
  if accept ps "LBRACE_BAR" then begin
    let cs = tc_constraints ps in
    ignore (expect ps "BAR_RBRACE");
    map (fun c ->
      let w = mk_pattern (PatVar (c.tc_id, Some TypeClassArg, [])) c.tc_r in
      mk_pattern (PatAscribed (w, (c.tc_t, None))) c.tc_r) cs
  end
  else if is ps "LPAREN" && not (is_op_paren ps) then begin
    match attempt ps (fun () -> multi_ids ps 2) with
    | Some qual_ids ->
      let i_t = !ps.idx in
      let t = p_simpleArrow ps in
      let r_t = loc ps i_t in
      let r = refineOpt ps in
      let cts = type_tc_constraints ps in
      ignore (expect ps "RPAREN");
      let pos = loc ps i0 in
      let n = length qual_ids in
      let pats = mapi_inorder 0 (fun idx ((aq, attrs), x) ->
        let pat = mk_pattern (PatVar (x, aq, attrs)) pos in
        let refine_opt = if idx = n - 1 then r else None in
        mkRefinedPattern pat t true refine_opt r_t pos) qual_ids
      in
      let names = map (fun (_, x) -> x) qual_ids in
      FStar.List.Tot.append pats (expand_inline_constraints cts names)
    | None -> paren_pattern ps true
  end
  else [atomicPattern ps]

and multiBinder (ps:pstate) : ML (list binder) =
  let i0 = !ps.idx in
  let k = peek_kind ps in
  if accept ps "LBRACE_BAR" then begin
    let cs = tc_constraints ps in
    ignore (expect ps "BAR_RBRACE");
    map (fun c -> mk_binder (Annotated (c.tc_id, c.tc_t)) c.tc_r Type_level (Some TypeClassArg)) cs
  end
  else if k = "LPAREN" then begin
    let qual_ids = multi_ids ps 1 in
    let t = p_simpleArrow ps in
    let r = refineOpt ps in
    let cts = type_tc_constraints ps in
    ignore (expect ps "RPAREN");
    let pos = loc ps i0 in
    let n = length qual_ids in
    let bs = mapi_inorder 0 (fun idx ((q, attrs), x) ->
      let refine_opt = if idx = n - 1 then r else None in
      mkRefinedBinder x t true refine_opt pos q attrs) qual_ids
    in
    let names = map (fun (_, x) -> x) qual_ids in
    let cts_binders = map_inorder pattern_must_be_binder (expand_inline_constraints cts names) in
    FStar.List.Tot.append bs cts_binders
  end
  else if k = "LPAREN_RPAREN" then begin
    ignore (advance ps);
    let r = loc ps i0 in
    let unit_t = unit_type r in
    [mk_binder (Annotated (gen r, unit_t)) r Type_level None]
  end
  else begin
    let (q, attrs), lid = aqualified_lidentOrUnderscore ps in
    [mk_binder_with_attrs (Variable lid) (loc ps i0) Type_level q attrs]
  end

and binders (ps:pstate) : ML (list binder) =
  if is_multiBinder_start_kind (peek_kind ps) then begin
    let bs = multiBinder ps in
    FStar.List.Tot.append bs (binders ps)
  end else []

(* ---------------------------------------------------------------------- *)
(* Pieces of terms: branches, let bindings, attributes, ...               *)
(* ---------------------------------------------------------------------- *)

let patternBranch (ps:pstate) : ML (bool & branch) =
  let i0 = !ps.idx in
  let pats = sep_nonempty ps "BAR" tuplePattern in
  let i_p = !ps.idx in
  let when_opt = if accept ps "WHEN" then Some (p_tmFormula ps) else None in
  let focus =
    if accept ps "RARROW" then false
    else if accept ps "SQUIGGLY_RARROW" then true
    else fail ps
  in
  let e = p_term ps in
  let pat =
    match pats with
    | [p] -> p
    | ps' -> mk_pattern (PatOr ps') (rng ps i0 i_p)
  in
  (focus, (pat, when_opt, e))

(* left_flexible_nonempty_list(BAR, patternBranch) *)
let branches_nonempty (ps:pstate) : ML (list (bool & branch)) =
  ignore (accept ps "BAR");
  let b = patternBranch ps in
  let rec go () : ML (list (bool & branch)) =
    if accept ps "BAR" then
      let b = patternBranch ps in
      b :: go ()
    else []
  in
  b :: go ()

(* left_flexible_list(BAR, patternBranch) *)
let branches (ps:pstate) : ML (list (bool & branch)) =
  if is ps "BAR" || is_atomic_pattern_start_kind (peek_kind ps)
  then branches_nonempty ps
  else []

(* trailingTerm *)
let trailingTerm (ps:pstate) : ML term =
  if is_only_trailing_start ps then only_trailing ps else atomicTerm ps

(* ascribeTyp: COLON tmArrow(tmNoEq) [BY thunk(trailingTerm)] *)
let ascribeTyp (ps:pstate) : ML (term & option term) =
  ignore (expect ps "COLON");
  let t = p_tmArrowNoEq ps in
  let tac =
    if accept ps "BY" then begin
      let i0 = !ps.idx in
      let tac = trailingTerm ps in
      Some (thunk_at ps i0 tac)
    end else None
  in
  (t, tac)

let attribute (ps:pstate) : ML (list term) =
  let i0 = !ps.idx in
  if accept ps "LBRACK_AT" then begin
    let rec go () : ML (list term) =
      if is_atomic_start ps then
        let t = atomicTerm ps in
        t :: go ()
      else []
    in
    let x = go () in
    ignore (expect ps "RBRACK");
    (match x with
     | _ :: _ :: _ ->
       E.log_issue_text (loc ps i0) Codes.Warning_DeprecatedAttributeSyntax
         "The `[@ ...]` syntax of attributes is deprecated. Use `[@@ a1; a2; ...; an]`, a semi-colon separated list of attributes, instead"
     | _ -> ());
    x
  end else begin
    ignore (expect ps "LBRACK_AT_AT");
    let x = semiColonTermList ps in
    ignore (expect ps "RBRACK");
    x
  end

let is_attribute_start (ps:pstate) : ML bool =
  is ps "LBRACK_AT" || is ps "LBRACK_AT_AT"

let letbinding (ps:pstate) : ML (bool & (pattern & term)) =
  let i_f = !ps.idx in
  let focus = accept ps "SQUIGGLY_RARROW" in
  let i_f1 = !ps.idx in
  let form1 =
    (is ps "IDENT" && is_genBinder_start_kind (peek_kind_n ps 1)) ||
    (is_op_paren ps && is_genBinder_start_kind (peek_kind_n ps 3))
  in
  if form1 then begin
    let i_lid = !ps.idx in
    let lid = lidentOrOperator ps in
    let r_lid = loc ps i_lid in
    let i_lbp = !ps.idx in
    let rec go () : ML (list (list pattern)) =
      let b = genBinder ps in
      if is_genBinder_start_kind (peek_kind ps) then b :: go () else [b]
    in
    let lbp = go () in
    let i_lbp1 = !ps.idx in
    let ascr_opt = if is ps "COLON" then Some (ascribeTyp ps) else None in
    ignore (expect ps "EQUALS");
    let i_tm = !ps.idx in
    let tm = p_term ps in
    let pat = mk_pattern (PatVar (lid, None, [])) r_lid in
    let pat = mk_pattern (PatApp (pat, flatten lbp)) (rng2 ps i_f i_f1 i_lbp i_lbp1) in
    let pos = rng2 ps i_f i_f1 i_tm !ps.idx in
    match ascr_opt with
    | None -> (focus, (pat, tm))
    | Some t -> (focus, (mk_pattern (PatAscribed (pat, t)) pos, tm))
  end else begin
    let pat = tuplePattern ps in
    if is ps "COLON" then begin
      let ascr = ascribeTyp ps in
      let i_eq = !ps.idx in
      ignore (expect ps "EQUALS");
      let r = rng2 ps i_f i_f1 i_eq SI.(i_eq + one) in
      let tm = p_term ps in
      (focus, (mk_pattern (PatAscribed (pat, ascr)) r, tm))
    end else begin
      ignore (expect ps "EQUALS");
      let tm = p_term ps in
      (focus, (pat, tm))
    end
  end

let letoperatorbinding (ps:pstate) : ML (pattern & term) =
  let i0 = !ps.idx in
  let pat = tuplePattern ps in
  let i_a = !ps.idx in
  let ascr_opt = if is ps "COLON" then Some (ascribeTyp ps) else None in
  let i_a1 = !ps.idx in
  let tm = if accept ps "EQUALS" then Some (p_term ps) else None in
  let h (tm:term) : ML (pattern & term) =
    ((match ascr_opt with
      | None -> pat
      | Some t -> mk_pattern (PatAscribed (pat, t)) (rng2 ps i0 i_a i_a i_a1)),
     tm)
  in
  match pat.pat, tm with
  | _, Some tm -> h tm
  | PatVar (v, _, _), None ->
    let v = lid_of_ns_and_id [] v in
    h (mk_term (Var v) (rng ps i0 i_a) Expr)
  | _ -> syntax_error (rng ps i_a i_a1) "Syntax error: let-punning expects a name, not a pattern"

let match_returning (ps:pstate) : ML (option match_returns_annotation) =
  let k = peek_kind ps in
  if k = "AS" || k = "RETURNS" || k = "RETURNS_EQ" then begin
    let as_opt = if accept ps "AS" then Some (p_lident ps) else None in
    if accept ps "RETURNS" then
      let t = p_typ ps in Some (as_opt, t, false)
    else begin
      ignore (expect ps "RETURNS_EQ");
      let t = p_typ ps in Some (as_opt, t, true)
    end
  end else None

let calcRel (ps:pstate) : ML term =
  let i0 = !ps.idx in
  match binop_name_of (peek ps) with
  | Some _ ->
    let i = binop_name ps in
    mk_term (Op (i, [])) (loc ps i0) Expr
  | None ->
    if accept ps "BACKTICK" then begin
      let id = p_qlident ps in
      ignore (expect ps "BACKTICK");
      mk_term (Var id) (loc ps i0) Un
    end
    else atomicTerm ps

let calcStep (ps:pstate) : ML calc_step =
  let rel = calcRel ps in
  let i_lb = !ps.idx in
  ignore (expect ps "LBRACE");
  let justif = if is ps "RBRACE" then None else Some (p_term ps) in
  ignore (expect ps "RBRACE");
  let r_j = loc ps i_lb in
  let next = p_noSeqTerm ps in
  ignore (expect ps "SEMICOLON");
  let justif =
    match justif with
    | Some t -> t
    | None -> mk_term (Const Const_unit) r_j Expr
  in
  mkCalcStep rel justif next

let rec list_atomic (ps:pstate) : ML (list term) =
  if is_atomic_start ps then
    let t = atomicTerm ps in
    t :: list_atomic ps
  else []

(* ---------------------------------------------------------------------- *)
(* Leading rules                                                          *)
(* ---------------------------------------------------------------------- *)

let always (_:pstate) (_:ctx) : ML bool = true
let not_noref (_:pstate) (ctx:ctx) : ML bool = not ctx.noref

let lrule (name:string) (allowed level:int) (guard:pstate -> ctx -> ML bool)
          (run:pstate -> ctx -> ML term) : leading_rule =
  { l_name = name; l_allowed = allowed; l_level = level; l_guard = guard; l_run = run }

let trule (name:string) (level lhs_min:int) (guard:pstate -> ctx -> term -> pos -> ML bool)
          (run:pstate -> ctx -> term -> pos -> ML term) : trailing_rule =
  { t_name = name; t_level = level; t_lhs_min = lhs_min; t_guard = guard; t_run = run }

(* The base of the grammar: tmRefinement, or an application *)
let base (ps:pstate) (ctx:ctx) : ML term =
  let i0 = !ps.idx in
  let k = peek_kind ps in
  if not ctx.noref && (k = "IDENT" || k = "UNDERSCORE") && peek_kind_n ps 1 = "COLON" then begin
    let id = lidentOrUnderscore ps in
    ignore (expect ps "COLON");
    let e = app_term ps true in
    let i_e = !ps.idx in
    let phi_opt = refineOpt ps in
    let t =
      match phi_opt with
      | None -> NamedTyp (id, e)
      | Some phi -> Refine (mk_binder (Annotated (id, e)) (rng ps i0 i_e) Type_level None, phi)
    in
    mk_term t (loc ps i0) Type_level
  end
  else app_term ps ctx.noref

let r_uminus (ps:pstate) (ctx:ctx) : ML term =
  let i0 = !ps.idx in
  let t = advance ps in
  let e = term_at ps ctx 80 in
  mk_uminus e (tok_rng ps t) (loc ps i0) Expr

let r_quote (k:quote_kind) (ps:pstate) (ctx:ctx) : ML term =
  let i0 = !ps.idx in
  ignore (advance ps);
  let e = term_at ps ctx 80 in
  mk_term (Quote (e, k)) (loc ps i0) Un

let r_backtick_at (ps:pstate) (_:ctx) : ML term =
  let i0 = !ps.idx in
  ignore (advance ps);
  let e = atomicTerm ps in
  let q = mk_term (Quote (e, Dynamic)) (loc ps i0) Un in
  mk_term (Antiquote q) (loc ps i0) Un

let r_backtick_hash (ps:pstate) (_:ctx) : ML term =
  let i0 = !ps.idx in
  ignore (advance ps);
  let e = atomicTerm ps in
  mk_term (Antiquote e) (loc ps i0) Un

let r_backtick_perc (ps:pstate) (_:ctx) : ML term =
  let i0 = !ps.idx in
  ignore (advance ps);
  let e = atomicTerm ps in
  mk_term (VQuote e) (loc ps i0) Un

let r_tilde (ps:pstate) (_:ctx) : ML term =
  let i0 = !ps.idx in
  let t = advance ps in
  let e = atomicTerm ps in
  mk_term (Op (mk_id_tok ps t t.text, [e])) (loc ps i0) Formula

let r_record (ps:pstate) (_:ctx) : ML term = record_term ps

let r_only_trailing (ps:pstate) (_:ctx) : ML term = only_trailing ps

(* Arrows whose domain carries a qualifier or attributes:
     {| t |} -> u      #x:t -> u      (#x:t) -> u     ([@@@a] t) -> u *)
let r_domain (ps:pstate) (ctx:ctx) : ML term =
  let i0 = !ps.idx in
  let aq, attrs, dom_tm =
    if accept ps "LBRACE_BAR" then begin
      let t = term_at ps ctx ctx.dom in
      ignore (expect ps "BAR_RBRACE");
      (Some TypeClassArg, [], t)
    end
    else if accept ps "LPAREN" then begin
      let aq, attrs = aqual_attrs ps in
      let t = term_at ps ctx ctx.dom in
      ignore (expect ps "RPAREN");
      (aq, attrs, t)
    end
    else begin
      let aq, attrs = aqual_attrs ps in
      let t = term_at ps ctx ctx.dom in
      (aq, attrs, t)
    end
  in
  let i_dom = !ps.idx in
  ignore (expect ps "RARROW");
  let tgt = term_at ps ctx 30 in
  let r_dom = rng ps i0 i_dom in
  let b =
    match extract_named_refinement true dom_tm with
    | None -> mk_binder_with_attrs (NoName dom_tm) r_dom Un aq attrs
    | Some (x, t, f) -> mkRefinedBinder x t true f r_dom aq attrs
  in
  mk_term (Product ([b], tgt)) (loc ps i0) Un

(* [( #a:t ) -> u] vs. [( #a:t -> u )]: the latter is a parenthesized
   arrow, so only commit to the domain rule if [) ->] follows. *)
let paren_domain_guard (ps:pstate) (ctx:ctx) : ML bool =
  ctx.paren_doms && is_aqualified_start_kind (peek_kind_n ps 1) &&
  lookahead ps (fun () ->
    ignore (advance ps);
    ignore (aqual_attrs ps);
    ignore (term_at ps ctx ctx.dom);
    ignore (expect ps "RPAREN");
    ignore (expect ps "RARROW"))

let r_requires (ps:pstate) (_:ctx) : ML term =
  let i0 = !ps.idx in
  ignore (advance ps);
  let t = p_typ ps in
  mk_term (Requires t) (loc ps i0) Type_level

let r_ensures (ps:pstate) (_:ctx) : ML term =
  let i0 = !ps.idx in
  ignore (advance ps);
  let t = p_typ ps in
  mk_term (Ensures t) (loc ps i0) Type_level

let r_decreases (ps:pstate) (_:ctx) : ML term =
  let i0 = !ps.idx in
  ignore (advance ps);
  if accept ps "LBRACE_COLON_WELL_FOUNDED" then begin
    let i_t = !ps.idx in
    let t = p_noSeqTerm ps in
    let r_t = loc ps i_t in
    ignore (expect ps "RBRACE");
    match t.tm with
    | App (t1, t2, _) ->
      let ot = mk_term (WFOrder (t1, t2)) r_t Type_level in
      mk_term (Decreases ot) (loc ps i0) Type_level
    | _ -> syntax_error r_t "Syntax error: To use well-founded relations, write e1 e2"
  end else begin
    let t = p_typ ps in
    mk_term (Decreases t) (loc ps i0) Type_level
  end

let op_of_kw (ps:pstate) (t:L.token) (plain:string) : ML (option ident) =
  if t.kind = plain then None
  else Some (mk_id_tok ps t ("let" ^ t.text))

let r_if (ps:pstate) (_:ctx) : ML term =
  let i0 = !ps.idx in
  let t = advance ps in
  let op = op_of_kw ps t "IF" in
  let e1 = p_noSeqTerm ps in
  let ret_opt = match_returning ps in
  ignore (expect ps "THEN");
  let e2 = p_noSeqTerm ps in
  if accept ps "ELSE" then begin
    let e3 = p_noSeqTerm ps in
    mk_term (If (e1, op, ret_opt, e2, e3)) (loc ps i0) Expr
  end else begin
    let e3 = mk_term (Const Const_unit) (loc ps i0) Expr in
    mk_term (If (e1, op, ret_opt, e2, e3)) (loc ps i0) Expr
  end

let r_try (ps:pstate) (_:ctx) : ML term =
  let i0 = !ps.idx in
  ignore (advance ps);
  let e1 = p_term ps in
  ignore (expect ps "WITH");
  let pbs = branches_nonempty ps in
  let branches = focusBranches pbs (loc ps i0) in
  mk_term (TryWith (e1, branches)) (loc ps i0) Expr

let r_match (ps:pstate) (_:ctx) : ML term =
  let i0 = !ps.idx in
  let t = advance ps in
  let op = op_of_kw ps t "MATCH" in
  let e = p_term ps in
  let ret_opt = match_returning ps in
  ignore (expect ps "WITH");
  let pbs = branches ps in
  let branches = focusBranches pbs (loc ps i0) in
  mk_term (Match (e, op, ret_opt, branches)) (loc ps i0) Expr

(* [attrs] LET ... IN e, or LET OPEN t IN e *)
let r_let (ps:pstate) (_:ctx) : ML term =
  let i0 = !ps.idx in
  let attrs = if is_attribute_start ps then Some (attribute ps) else None in
  ignore (expect ps "LET");
  if None? attrs && accept ps "OPEN" then begin
    let i_t = !ps.idx in
    let t = p_term ps in
    let r_t = loc ps i_t in
    ignore (expect ps "IN");
    let e = p_term ps in
    match t.tm with
    | Ascribed (r, rty, None, _) -> mk_term (LetOpenRecord (r, rty, e)) (loc ps i0) Expr
    | Name uid -> mk_term (LetOpen (uid, e)) (loc ps i0) Expr
    | _ ->
      syntax_error r_t
        "Syntax error: local opens expects either opening\na module or namespace using `let open T in e`\nor, a record type with `let open e <: t in e'`"
  end else begin
    let i_q = !ps.idx in
    let q =
      if accept ps "REC" then LocalRec
      else if accept ps "UNFOLD" then LocalUnfold
      else LocalNoLetQualifier
    in
    let i_q1 = !ps.idx in
    let lb = letbinding ps in
    let i_lb1 = !ps.idx in
    let rec more () : ML (list (option attributes_ & (bool & (pattern & term)))) =
      if is ps "AND" || (is_attribute_start ps) then begin
        let a = if is_attribute_start ps then Some (attribute ps) else None in
        ignore (expect ps "AND");
        let lb = letbinding ps in
        (a, lb) :: more ()
      end else []
    in
    let lbs = more () in
    ignore (expect ps "IN");
    let e = p_term ps in
    let lbs = (attrs, lb) :: lbs in
    let lbs = focusAttrLetBindings lbs (rng2 ps i_q i_q1 i_q i_lb1) in
    let r = if None? attrs then eps_loc ps i0 else loc ps i0 in
    mk_term (Let (q, lbs, e)) r Expr
  end

let r_let_op (ps:pstate) (_:ctx) : ML term =
  let i0 = !ps.idx in
  let t = advance ps in
  let op = mk_id_tok ps t ("let" ^ t.text) in
  let b = letoperatorbinding ps in
  let rec more () : ML (list (ident & (pattern & term))) =
    if is ps "AND_OP" then begin
      let t = advance ps in
      let op = mk_id_tok ps t ("and" ^ t.text) in
      let b = letoperatorbinding ps in
      (op, b) :: more ()
    end else []
  in
  let lbs = (op, b) :: more () in
  ignore (expect ps "IN");
  let e = p_term ps in
  mk_term (LetOperator (map (fun (op, (pat, tm)) -> (op, pat, tm)) lbs, e)) (loc ps i0) Expr

let r_function (ps:pstate) (_:ctx) : ML term =
  let i0 = !ps.idx in
  ignore (advance ps);
  let pbs = branches_nonempty ps in
  let branches = focusBranches pbs (loc ps i0) in
  mk_function branches (loc ps i0) (loc ps i0)

let r_assume (ps:pstate) (_:ctx) : ML term =
  let i0 = !ps.idx in
  let t = advance ps in
  let e = p_noSeqTerm ps in
  let a = set_lid_range C.assume_lid (tok_rng ps t) in
  mkExplicitApp (mk_term (Var a) (tok_rng ps t) Expr) [e] (loc ps i0)

let r_assert (ps:pstate) (_:ctx) : ML term =
  let i0 = !ps.idx in
  let t = advance ps in
  let e = p_noSeqTerm ps in
  if accept ps "BY" then begin
    let i_tac = !ps.idx in
    let tac = p_typ ps in
    let tac = thunk2_at ps i_tac tac in
    let a = set_lid_range C.assert_by_tactic_lid (tok_rng ps t) in
    mkExplicitApp (mk_term (Var a) (tok_rng ps t) Expr) [e; tac] (loc ps i0)
  end else begin
    let a = set_lid_range C.assert_lid (tok_rng ps t) in
    mkExplicitApp (mk_term (Var a) (tok_rng ps t) Expr) [e] (loc ps i0)
  end

let r_underscore_by (ps:pstate) (_:ctx) : ML term =
  let i0 = !ps.idx in
  let u = advance ps in
  ignore (expect ps "BY");
  let i_tac = !ps.idx in
  let tac = atomicTerm ps in
  let tac = thunk_at ps i_tac tac in
  let a = set_lid_range C.synth_lid (tok_rng ps u) in
  mkExplicitApp (mk_term (Var a) (tok_rng ps u) Expr) [tac] (loc ps i0)

let r_synth (ps:pstate) (_:ctx) : ML term =
  let i0 = !ps.idx in
  let s = advance ps in
  let tac = atomicTerm ps in
  let a = set_lid_range C.synth_lid (tok_rng ps s) in
  mkExplicitApp (mk_term (Var a) (tok_rng ps s) Expr) [tac] (loc ps i0)

let r_calc (ps:pstate) (_:ctx) : ML term =
  let i0 = !ps.idx in
  ignore (advance ps);
  let rel = atomicTerm ps in
  ignore (expect ps "LBRACE");
  let init = p_noSeqTerm ps in
  ignore (expect ps "SEMICOLON");
  let rec steps () : ML (list calc_step) =
    if is ps "RBRACE" then []
    else let s = calcStep ps in s :: steps ()
  in
  let steps = steps () in
  ignore (expect ps "RBRACE");
  mk_term (CalcProof (rel, init, steps)) (loc ps i0) Expr

(* Is [t] the binary operator [op] applied at the top (not in parentheses)? *)
let as_binop (op:string) (t:term) : option (term & term) =
  match t.tm with
  | Op (o, [p; q]) -> if string_of_id o = op then Some (p, q) else None
  | _ -> None

let r_intro (ps:pstate) (_:ctx) : ML term =
  let i0 = !ps.idx in
  ignore (advance ps);
  if accept ps "FORALL" then begin
    let bs = binders ps in
    ignore (expect ps "DOT");
    let p = p_noSeqTerm ps in
    ignore (expect ps "WITH");
    let e = p_noSeqTerm ps in
    mk_term (IntroForall (bs, p, e)) (loc ps i0) Expr
  end
  else if accept ps "EXISTS" then begin
    let bs = binders ps in
    ignore (expect ps "DOT");
    let p = p_noSeqTerm ps in
    ignore (expect ps "WITH");
    let i_vs = !ps.idx in
    let vs = list_atomic ps in
    let r_vs = loc ps i_vs in
    ignore (expect ps "AND");
    let e = p_noSeqTerm ps in
    if length bs <> length vs
    then syntax_error r_vs "Syntax error: expected instantiations for all binders"
    else mk_term (IntroExists (bs, p, vs, e)) (loc ps i0) Expr
  end
  else begin
    let p = p_tmArrowFormula ps in
    if accept ps "IMPLIES" then begin
      let q = p_tmFormula ps in
      ignore (expect ps "WITH");
      let i_e = !ps.idx in
      let e = p_noSeqTerm ps in
      let rec head (t:term) : term =
        match t.tm with
        | App (t, _, _) -> head t
        | _ -> t
      in
      let separated_by_space (r1 r2:R.range) : ML bool =
        let e1 = RO.end_of_range r1 in
        let s2 = RO.start_of_range r2 in
        RO.line_of_pos s2 <> RO.line_of_pos e1 ||
        RO.col_of_pos s2 > RO.col_of_pos e1 + 1
      in
      (match (head e).tm with
       | Project ({ tm = Var l; range = lhs_range }, f) ->
         if Nil? (ns_of_lid l) && separated_by_space lhs_range (range_of_lid f) then
           syntax_error (loc ps i_e)
             "Syntax error: 'introduce _ ==> _' no longer takes a name for the hypothesis. Write 'introduce P ==> Q with e' instead; P is available in the proof context of e."
       | _ -> ());
      mk_term (IntroImplies (p, q, e)) (loc ps i0) Expr
    end
    else match as_binop "\\/" p with
    | Some (p, q) ->
      ignore (expect ps "WITH");
      let lr = expect ps "NAME" in
      let e = p_noSeqTerm ps in
      let b =
        if lr.text = "Left" then true
        else if lr.text = "Right" then false
        else syntax_error (tok_rng ps lr) "Syntax error: _intro_ \\/ expects either 'Left' or 'Right'"
      in
      mk_term (IntroOr (b, p, q, e)) (loc ps i0) Expr
    | None ->
      match as_binop "/\\" p with
      | Some (p, q) ->
        ignore (expect ps "WITH");
        let e1 = p_noSeqTerm ps in
        ignore (expect ps "AND");
        let e2 = p_noSeqTerm ps in
        mk_term (IntroAnd (p, q, e1, e2)) (loc ps i0) Expr
      | None -> fail ps
  end

let r_elim (ps:pstate) (_:ctx) : ML term =
  let i0 = !ps.idx in
  ignore (advance ps);
  if accept ps "FORALL" then begin
    let xs = binders ps in
    ignore (expect ps "DOT");
    let p = p_noSeqTerm ps in
    ignore (expect ps "WITH");
    let vs = list_atomic ps in
    mk_term (ElimForall (xs, p, vs)) (loc ps i0) Expr
  end
  else if accept ps "EXISTS" then begin
    let bs = binders ps in
    ignore (expect ps "DOT");
    let p = p_noSeqTerm ps in
    if is ps "RETURNS" then begin
      let i_ret = !ps.idx in
      ignore (advance ps);
      let _q = p_noSeqTerm ps in
      ignore (expect ps "WITH");
      let _y = binders ps in
      ignore (expect ps "DOT");
      let _e = p_noSeqTerm ps in
      syntax_error (loc ps i_ret)
        "Syntax error: 'eliminate exists' no longer takes a 'returns' clause nor a name for the hypothesis. Write 'eliminate exists x1...xn. P with e' instead; x1...xn are bound in e, and P is available in the proof context of e."
    end else begin
      ignore (expect ps "WITH");
      let e = p_noSeqTerm ps in
      mk_term (ElimExists (bs, p, e)) (loc ps i0) Expr
    end
  end
  else begin
    let p = p_tmArrowFormula ps in
    if accept ps "IMPLIES" then begin
      let q = p_tmFormula ps in
      ignore (expect ps "WITH");
      let e = p_noSeqTerm ps in
      mk_term (ElimImplies (p, q, e)) (loc ps i0) Expr
    end
    else match as_binop "\\/" p with
    | Some (p, q) ->
      if is ps "RETURNS" then begin
        let i_ret = !ps.idx in
        ignore (advance ps);
        let _r = p_noSeqTerm ps in
        ignore (expect ps "WITH");
        let _x = binders ps in
        ignore (expect ps "DOT");
        let _e1 = p_noSeqTerm ps in
        ignore (expect ps "AND");
        let _y = binders ps in
        ignore (expect ps "DOT");
        let _e2 = p_noSeqTerm ps in
        syntax_error (loc ps i_ret)
          "Syntax error: 'eliminate _ \\/ _' no longer takes a 'returns' clause nor names for the hypotheses. Write 'eliminate P \\/ Q with e1 and e2' instead; P is available in the proof context of e1, and Q in that of e2."
      end else begin
        ignore (expect ps "WITH");
        let e1 = p_noSeqTerm ps in
        ignore (expect ps "AND");
        let e2 = p_noSeqTerm ps in
        mk_term (ElimOr (p, q, e1, e2)) (loc ps i0) Expr
      end
    | None ->
      match as_binop "/\\" p with
      | Some (p, q) ->
        if is ps "RETURNS" then begin
          let i_ret = !ps.idx in
          ignore (advance ps);
          let _r = p_noSeqTerm ps in
          ignore (expect ps "WITH");
          let _xs = binders ps in
          ignore (expect ps "DOT");
          let _e = p_noSeqTerm ps in
          syntax_error (loc ps i_ret)
            "Syntax error: 'eliminate _ /\\ _' no longer takes a 'returns' clause nor names for the hypotheses. Write 'eliminate P /\\ Q with e' instead; both P and Q are available in the proof context of e."
        end else begin
          ignore (expect ps "WITH");
          let e = p_noSeqTerm ps in
          mk_term (ElimAnd (p, q, e)) (loc ps i0) Expr
        end
      | None -> fail ps
  end

(* x <-- e1; e2 *)
let r_long_left_arrow (ps:pstate) (_:ctx) : ML term =
  let i0 = !ps.idx in
  let x = lidentOrUnderscore ps in
  ignore (expect ps "LONG_LEFT_ARROW");
  let e1 = p_noSeqTerm ps in
  ignore (expect ps "SEMICOLON");
  let e2 = p_term ps in
  mk_term (Bind (x, e1, e2)) (loc ps i0) Expr

let next_is (k:string) (ps:pstate) (_:ctx) : ML bool = peek_kind_n ps 1 = k

(* ---------------------------------------------------------------------- *)
(* Trailing rules                                                         *)
(* ---------------------------------------------------------------------- *)

let tguard (_:pstate) (_:ctx) (_:term) (_:pos) : ML bool = true

(* A binary operator e1 op e2, with the operator named by [name] *)
let binop (name:L.token -> string) (rhs:int) (lv:level)
  (ps:pstate) (ctx:ctx) (lhs:term) (i0:pos) : ML term =
  let t = advance ps in
  let e2 = term_at ps ctx rhs in
  mk_term (Op (mk_id_tok ps t (name t), [lhs; e2])) (loc ps i0) lv

let tok_text (t:L.token) : string = t.text
let const_name (s:string) (_:L.token) : string = s

(* Left-associative operators at [l]: lhs at l, rhs at l+1;
   right-associative: lhs at l+1, rhs at l. *)
let left_op (key:string) (l:int) (name:L.token -> string) (lv:level) : string & trailing_rule =
  (key, trule key l l tguard (binop name (l + 1) lv))
let right_op (key:string) (l:int) (name:L.token -> string) (lv:level) : string & trailing_rule =
  (key, trule key l (l + 1) tguard (binop name l lv))

(* e1; e2 *)
let t_seq (ps:pstate) (ctx:ctx) (lhs:term) (i0:pos) : ML term =
  ignore (advance ps);
  let e2 = term_at ps ctx 0 in
  mk_term (Seq (lhs, e2)) (loc ps i0) Expr

(* e1 ;; e2   and   e1 ;op e2 *)
let t_seq_op (ps:pstate) (ctx:ctx) (lhs:term) (i0:pos) : ML term =
  let t = advance ps in
  let e2 = term_at ps ctx 0 in
  let r_op = tok_rng ps t in
  let tm =
    if t.text = "" then Bind (gen r_op, lhs, e2)
    else
      let op = mk_ident ("let" ^ t.text, r_op) in
      let pat = mk_pattern (PatWild (None, [])) r_op in
      LetOperator ([(op, pat, lhs)], e2)
  in
  mk_term tm (loc ps i0) Expr

(* e1.(e2) <- e3: only when the lhs is exactly an indexing term *)
let larrow_guard (ps:pstate) (_:ctx) (lhs:term) (i0:pos) : ML bool =
  let (a, b) = !last_index in
  a = i0 && b = !ps.idx &&
  (match lhs.tm with Op (_, [_; _]) -> true | _ -> false)

let t_larrow (ps:pstate) (ctx:ctx) (lhs:term) (i0:pos) : ML term =
  ignore (advance ps);
  let e3 = term_at ps ctx 1 in
  match lhs.tm with
  | Op (op, [e1; e2]) ->
    let opid = mk_ident (string_of_id op ^ "<-", range_of_id op) in
    mk_term (Op (opid, [e1; e2; e3])) (loc ps i0) Expr
  | _ -> fail ps

(* e <: t [by tac]   and   e $: t [by tac] *)
let t_ascribe (eq:bool) (ps:pstate) (_:ctx) (lhs:term) (i0:pos) : ML term =
  let i_op = !ps.idx in
  ignore (advance ps);
  let t = p_typ ps in
  let tac, r =
    if accept ps "BY" then begin
      let i_t = !ps.idx in
      let tac = p_typ ps in
      Some (thunk_at ps i_t tac), loc ps i0
    end
    else None, rng ps i0 i_op
  in
  if eq then
    E.log_issue_text (loc ps i0) Codes.Warning_BleedingEdge_Feature
      "Equality type ascriptions is an experimental feature subject to redesign in the future";
  mk_term (Ascribed (lhs, { t with level = Expr }, tac, eq)) r Expr

(* dom -> tgt *)
let t_arrow (ps:pstate) (ctx:ctx) (lhs:term) (i0:pos) : ML term =
  let i_arrow = !ps.idx in
  ignore (advance ps);
  let tgt = term_at ps ctx 30 in
  let r_dom = rng ps i0 i_arrow in
  let b =
    match extract_named_refinement true lhs with
    | None -> mk_binder_with_attrs (NoName lhs) r_dom Un None []
    | Some (x, t, f) -> mkRefinedBinder x t true f r_dom None []
  in
  mk_term (Product ([b], tgt)) (loc ps i0) Un

(* e1, ..., en *)
let t_tuple (ps:pstate) (ctx:ctx) (lhs:term) (i0:pos) : ML term =
  let i_e = !ps.idx in
  let rec go () : ML (list term) =
    if accept ps "COMMA" then
      let e = term_at ps ctx 71 in
      e :: go ()
    else []
  in
  let rest = go () in
  mkTuple (lhs :: rest) (rng ps i0 i_e)

(* e1 :: e2 *)
let t_cons (ps:pstate) (ctx:ctx) (lhs:term) (i0:pos) : ML term =
  ignore (advance ps);
  let e2 = term_at ps ctx 81 in
  consTerm (loc ps i0) lhs e2

(* dependent tuple types  x:t & u *)
let t_sum (ps:pstate) (ctx:ctx) (lhs:term) (i0:pos) : ML term =
  let i_amp = !ps.idx in
  ignore (advance ps);
  let e2 = term_at ps ctx 82 in
  let dom =
    match extract_named_refinement false lhs with
    | Some (x, t, f) -> Inl (mkRefinedBinder x t true f (rng ps i0 i_amp) None [])
    | None -> Inr lhs
  in
  let dom, res =
    match e2.tm with
    | Sum (dom', res) -> dom :: dom', res
    | _ -> [dom], e2
  in
  mk_term (Sum (dom, res)) (loc ps i0) Type_level

(* e1 `op` e2 *)
let t_backtick (ps:pstate) (ctx:ctx) (lhs:term) (i0:pos) : ML term =
  ignore (advance ps);
  let op = term_at ps ctx 86 in
  ignore (expect ps "BACKTICK");
  let e2 = term_at ps ctx 86 in
  mkApp op [(lhs, Infix); (e2, Nothing)] (loc ps i0)

(* ---------------------------------------------------------------------- *)
(* The grammar of F* terms                                                *)
(* ---------------------------------------------------------------------- *)

let leading_rules : list (string & leading_rule) = [
  "MINUS",         lrule "uminus" 80 80 always r_uminus;
  "QUOTE",         lrule "quote" 80 80 always (r_quote Dynamic);
  "BACKTICK",      lrule "static_quote" 80 80 always (r_quote Static);
  "BACKTICK_AT",   lrule "antiquote_quote" 80 80 always r_backtick_at;
  "BACKTICK_HASH", lrule "antiquote" 80 80 always r_backtick_hash;
  "BACKTICK_PERC", lrule "vquote" 100 100 always r_backtick_perc;
  "TILDE",         lrule "tilde" 100 100 always r_tilde;
  "LBRACE",        lrule "record" 100 100 always r_record;
  "FUN",           lrule "fun" 100 100 not_noref r_only_trailing;
  "FORALL",        lrule "forall" 100 100 not_noref r_only_trailing;
  "EXISTS",        lrule "exists" 100 100 not_noref r_only_trailing;
  "FORALL_OP",     lrule "forall_op" 100 100 not_noref r_only_trailing;
  "EXISTS_OP",     lrule "exists_op" 100 100 not_noref r_only_trailing;
  "LBRACE_BAR",    lrule "tc_arrow" 30 30 always r_domain;
  "HASH",          lrule "implicit_arrow" 30 30 always r_domain;
  "DOLLAR",        lrule "equality_arrow" 30 30 always r_domain;
  "LBRACK_AT_AT_AT", lrule "attr_arrow" 30 30 always r_domain;
  "LPAREN",        lrule "paren_arrow" 30 30 paren_domain_guard r_domain;
  "REQUIRES",      lrule "requires" 1 1 always r_requires;
  "ENSURES",       lrule "ensures" 1 1 always r_ensures;
  "DECREASES",     lrule "decreases" 1 1 always r_decreases;
  "IF",            lrule "if" 1 1 always r_if;
  "IF_OP",         lrule "if_op" 1 1 always r_if;
  "TRY",           lrule "try" 1 1 always r_try;
  "MATCH",         lrule "match" 1 1 always r_match;
  "MATCH_OP",      lrule "match_op" 1 1 always r_match;
  "LET",           lrule "let" 1 1 always r_let;
  "LBRACK_AT",     lrule "attr_let" 1 1 always r_let;
  "LBRACK_AT_AT",  lrule "attr_let" 1 1 always r_let;
  "LET_OP",        lrule "let_op" 1 1 always r_let_op;
  "FUNCTION",      lrule "function" 1 1 always r_function;
  "ASSUME",        lrule "assume" 1 1 always r_assume;
  "ASSERT",        lrule "assert" 1 1 always r_assert;
  "UNDERSCORE",    lrule "underscore_by" 1 1 (next_is "BY") r_underscore_by;
  "SYNTH",         lrule "synth" 1 1 always r_synth;
  "CALC",          lrule "calc" 1 1 always r_calc;
  "INTRO",         lrule "introduce" 1 1 always r_intro;
  "ELIM",          lrule "eliminate" 1 1 always r_elim;
  "IDENT",         lrule "bind" 0 0 (next_is "LONG_LEFT_ARROW") r_long_left_arrow;
  "UNDERSCORE",    lrule "bind" 0 0 (next_is "LONG_LEFT_ARROW") r_long_left_arrow;
]

let trailing_rules : list (string & trailing_rule) = [
  "SEMICOLON",    trule "seq" 0 1 tguard t_seq;
  "SEMICOLON_OP", trule "seq_op" 0 1 tguard t_seq_op;
  "LARROW",       trule "larrow" 1 0 larrow_guard t_larrow;
  "SUBTYPE",      trule "subtype" 5 10 tguard (t_ascribe false);
  "EQUALTYPE",    trule "equaltype" 5 10 tguard (t_ascribe true);
  right_op "IFF" 10 (const_name "<==>") Formula;
  right_op "IMPLIES" 20 (const_name "==>") Formula;
  "RARROW",       trule "arrow" 30 31 tguard t_arrow;
  left_op "DISJUNCTION" 40 (const_name "\\/") Formula;
  left_op "CONJUNCTION" 50 (const_name "/\\") Formula;
  "COMMA",        trule "tuple" 60 71 tguard t_tuple;
  ("COLON_EQUALS", trule "COLON_EQUALS" 71 72 tguard (binop (const_name ":=") 72 Un));
  left_op "OPINFIX0a" 72 tok_text Un;
  left_op "OPINFIX0b" 73 tok_text Un;
  left_op "OPINFIX0c" 74 tok_text Un;
  left_op "EQUALS" 74 (const_name "=") Un;
  left_op "OPINFIX0d" 75 tok_text Un;
  left_op "PIPE_RIGHT" 76 (const_name "|>") Un;
  right_op "PIPE_LEFT" 77 (const_name "<|") Un;
  right_op "OPINFIX1" 78 tok_text Un;
  left_op "OPINFIX2" 79 tok_text Un;
  left_op "MINUS" 79 (const_name "-") Un;
  "COLON_COLON",  trule "cons" 81 82 tguard t_cons;
  "AMP",          trule "sum" 82 83 tguard t_sum;
  left_op "OPINFIX3L" 83 tok_text Un;
  right_op "OPINFIX3R" 84 tok_text Un;
  "BACKTICK",     trule "infix_app" 85 85 tguard t_backtick;
  right_op "OPINFIX4" 86 tok_text Un;
]

let rec add_all_leading (g:grammar) (rs:list (string & leading_rule)) : ML grammar =
  match rs with
  | [] -> g
  | (k, r) :: rs -> add_all_leading (add_leading g k r) rs

let rec add_all_trailing (g:grammar) (rs:list (string & trailing_rule)) : ML grammar =
  match rs with
  | [] -> g
  | (k, r) :: rs -> add_all_trailing (add_trailing g k r) rs

let fstar_grammar : grammar =
  add_all_trailing (add_all_leading (empty_grammar base 100) leading_rules) trailing_rules

(* ---------------------------------------------------------------------- *)
(* Declarations                                                           *)
(* ---------------------------------------------------------------------- *)

let p_string (ps:pstate) : ML string = (expect ps "STRING").text

let opt_string (ps:pstate) : ML (option string) =
  if is ps "STRING" then Some (p_string ps) else None

let p_pragma (ps:pstate) : ML pragma =
  let t = advance ps in
  match t.kind with
  | "PRAGMA_SHOW_OPTIONS" -> ShowOptions
  | "PRAGMA_SET_OPTIONS" -> SetOptions (p_string ps)
  | "PRAGMA_RESET_OPTIONS" -> ResetOptions (opt_string ps)
  | "PRAGMA_PUSH_OPTIONS" -> PushOptions (opt_string ps)
  | "PRAGMA_POP_OPTIONS" -> PopOptions
  | "PRAGMA_RESTART_SOLVER" -> RestartSolver
  | "PRAGMA_PRINT_EFFECTS_GRAPH" -> PrintEffectsGraph
  | "PRAGMA_CHECK" -> Check (p_term ps)
  | "PRAGMA_EVAL" -> Eval (p_term ps)
  | _ -> fail ps

let logic_qualifier_deprecation_warning =
  "logic qualifier is deprecated, please remove it from the source program. In case your program verifies with the qualifier annotated but not without it, please try to minimize the example and file a github issue."

let p_qualifier (ps:pstate) : ML qualifier =
  let t = peek ps in
  let r = tok_rng ps t in
  let q =
    match t.kind with
    | "ASSUME" -> Assumption
    | "INLINE_FOR_EXTRACTION" -> Inline_for_extraction
    | "UNFOLD" -> Unfold_for_unification_and_vcgen
    | "IRREDUCIBLE" -> Irreducible
    | "NOEXTRACT" -> NoExtract
    | "TOTAL" -> TotalEffect
    | "PRIVATE" -> Private
    | "NOEQUALITY" -> Noeq
    | "UNOPTEQUALITY" -> Unopteq
    | "NEW" -> New
    | "LOGIC" -> Logic
    | "OPAQUE" -> Opaque
    | "REIFIABLE" -> Reifiable
    | "REFLECTABLE" -> Reflectable
    | "INLINE" | "UNFOLDABLE" -> Logic (* handled below *)
    | _ -> fail ps
  in
  ignore (advance ps);
  match t.kind with
  | "INLINE" ->
    E.raise_error_text r Codes.Fatal_InlineRenamedAsUnfold
      "The 'inline' qualifier has been renamed to 'unfold'"
  | "UNFOLDABLE" ->
    E.raise_error_text r Codes.Fatal_UnfoldableDeprecated
      "The 'unfoldable' qualifier is no longer denotable; it is the default qualifier so just omit it"
  | "LOGIC" ->
    E.log_issue_text r Codes.Warning_logicqualifier logic_qualifier_deprecation_warning;
    Logic
  | _ -> q

let rec decorations (ps:pstate) : ML (list decoration) =
  if is_attribute_start ps then
    let a = attribute ps in
    DeclAttributes a :: decorations ps
  else if FStar.List.Tot.mem (peek_kind ps) qualifier_kinds then
    let q = p_qualifier ps in
    Qualifier q :: decorations ps
  else []

(* recordDefinition: LBRACE right_flexible_nonempty_list(SEMICOLON, recordFieldDecl) RBRACE *)
let recordFieldDecl (ps:pstate) : ML (ident & aqual & list term & term) =
  let (aq, attrs) = aqual_attrs ps in
  let lid = lidentOrOperator ps in
  ignore (expect ps "COLON");
  let t = p_typ ps in
  (lid, aq, attrs, t)

let recordDefinition (ps:pstate) : ML tycon_record =
  ignore (expect ps "LBRACE");
  let fs = rflex_nonempty ps "SEMICOLON" "RBRACE" recordFieldDecl in
  ignore (expect ps "RBRACE");
  fs

let constructorPayload (ps:pstate) : ML (option constructor_payload) =
  if accept ps "COLON" then Some (VpArbitrary (p_typ ps))
  else if accept ps "OF" then Some (VpOfNotation (p_typ ps))
  else if is ps "LBRACE" then begin
    let fields = recordDefinition ps in
    let t = opt ps "COLON" p_typ in
    Some (VpRecord (fields, t))
  end
  else None

let constructorDecl (ps:pstate) : ML (ident & option constructor_payload & list term) =
  ignore (expect ps "BAR");
  let attrs = if is ps "LBRACK_AT_AT_AT" then binderAttributes ps else [] in
  let uid = p_uident ps in
  let payload = constructorPayload ps in
  (uid, payload, attrs)

let typeDecl (ps:pstate) : ML tycon =
  let lid = p_ident ps in
  let tparams = binders ps in
  let kopt =
    if accept ps "COLON" then
      let k = p_tmArrowNoEq ps in
      Some { k with level = Kind }
    else None
  in
  if accept ps "EQUALS" then begin
    let k = peek_kind ps in
    if k = "BAR" then begin
      let rec go () : ML (list (ident & option constructor_payload & list term)) =
        if is ps "BAR" then
          let c = constructorDecl ps in
          c :: go ()
        else []
      in
      let cs = go () in
      check_id lid;
      TyconVariant (lid, tparams, kopt, cs)
    end
    else begin
      let record =
        if k = "LBRACE" || k = "LBRACK_AT_AT_AT" then
          attempt ps (fun () ->
            let attrs = if is ps "LBRACK_AT_AT_AT" then binderAttributes ps else [] in
            let fs = recordDefinition ps in
            (attrs, fs))
        else None
      in
      match record with
      | Some (attrs, fs) ->
        check_id lid;
        TyconRecord (lid, tparams, kopt, attrs, fs)
      | None ->
        if FStar.List.Tot.mem k start_of_next_decl_kinds || k = "AND" then begin
          check_id lid;
          TyconVariant (lid, tparams, kopt, [])
        end else begin
          let t = p_typ ps in
          check_id lid;
          TyconAbbrev (lid, tparams, kopt, t)
        end
    end
  end
  else begin
    check_id lid;
    TyconAbstract (lid, tparams, kopt)
  end

(* effect { M binders with { combinators } } *)
let effectDefinition (ps:pstate) : ML effect_decl =
  ignore (expect ps "LBRACE");
  let lid = p_uident ps in
  let bs = binders ps in
  ignore (expect ps "WITH");
  let r = p_tmNoEq ps in
  ignore (expect ps "RBRACE");
  let rec decls (r:term) : ML (list decl) =
    match r.tm with
    | Paren r -> decls r
    | Record (None, flds) ->
      map_inorder (fun (lid, t) ->
        mk_decl (Tycon (false, false, [TyconAbbrev (ident_of_lid lid, [], None, t)])) t.range [])
        flds
    | _ ->
      syntax_error r.range "Syntax error: effect combinators should be declared as a record"
  in
  DefineEffect (lid, bs, decls r)

let subEffect (ps:pstate) : ML lift =
  let src = p_quident ps in
  ignore (expect ps "SQUIGGLY_RARROW");
  let tgt = p_quident ps in
  let lift_op = opt ps "EQUALS" p_typ in
  { msource = src; mdest = tgt; lift_op = lift_op }

let restriction (ps:pstate) : ML SS.restriction =
  if accept ps "LBRACE" then begin
    let item (ps:pstate) : ML (ident & option ident) =
      let id = identOrOperator ps in
      let renamed = opt ps "AS" identOrOperator in
      (id, renamed)
    in
    let ids = rflex ps "COMMA" "RBRACE" item in
    ignore (expect ps "RBRACE");
    SS.AllowList ids
  end
  else SS.Unrestricted

let letqualifier (ps:pstate) : ML let_qualifier =
  if accept ps "REC" then Rec else NoLetQualifier

let val_type (ps:pstate) : ML term =
  let i_bs = !ps.idx in
  let bs = binders ps in
  let i_bs1 = !ps.idx in
  ignore (expect ps "COLON");
  let i_t = !ps.idx in
  let t = p_typ ps in
  match bs with
  | [] -> t
  | bs -> mk_term (Product (bs, t)) (rng2 ps i_bs i_bs1 i_t !ps.idx) Type_level

let rawDecl (ps:pstate) : ML decl' =
  let i0 = !ps.idx in
  let k = peek_kind ps in
  if FStar.List.Tot.mem k pragma_start_kinds then Pragma (p_pragma ps)
  else begin
    ignore (advance ps);
    match k with
    | "OPEN" ->
      let uid = p_quident ps in
      let r = restriction ps in
      Open (uid, r)
    | "FRIEND" -> Friend (p_quident ps)
    | "INCLUDE" ->
      let uid = p_quident ps in
      let r = restriction ps in
      Include (uid, r)
    | "MODULE" ->
      if is ps "UNDERSCORE" then begin
        ignore (advance ps);
        ignore (expect ps "EQUALS");
        let uid = p_quident ps in
        Open (uid, SS.AllowList [])
      end
      else if is ps "NAME" && peek_kind_n ps 1 = "EQUALS" then begin
        let uid1 = p_uident ps in
        ignore (advance ps);
        let uid2 = p_quident ps in
        ModuleAbbrev (uid1, uid2)
      end
      else begin
        let i_q = !ps.idx in
        let ids, is_name = p_path ps in
        if is_name then TopLevelModule (lid_of_ids ids)
        else syntax_error (loc ps i_q) "Syntax error: expected a module name"
      end
    | "TYPE" -> Tycon (false, false, sep_nonempty ps "AND" typeDecl)
    | "EFFECT" ->
      if is ps "LBRACE" then NewEffect (effectDefinition ps)
      else begin
        let uid = p_uident ps in
        let tparams = binders ps in
        match opt ps "EQUALS" p_typ with
        | Some t -> Tycon (true, false, [TyconAbbrev (uid, tparams, None, t)])
        | None -> NewEffect (DeclareEffect (uid, tparams))
      end
    | "LET" ->
      let q = letqualifier ps in
      let lbs = sep_nonempty ps "AND" letbinding in
      TopLevelLet (q, focusLetBindings lbs (loc ps i0))
    | "VAL" ->
      if is_constant_kind (peek_kind ps) then begin
        ignore (constant ps);
        syntax_error (loc ps i0) "Syntax error: constants are not allowed in val declarations"
      end else begin
        let lid = lidentOrOperator ps in
        let t = val_type ps in
        Val (lid, t)
      end
    | "SPLICE" | "SPLICET" ->
      ignore (expect ps "LBRACK");
      let ids = rflex ps "SEMICOLON" "RBRACK" p_ident in
      ignore (expect ps "RBRACK");
      let i_t = !ps.idx in
      let t = atomicTerm ps in
      if k = "SPLICE" then Splice (false, ids, thunk_at ps i_t t)
      else Splice (true, ids, t)
    | "EXCEPTION" ->
      let lid = p_uident ps in
      let t = opt ps "OF" p_typ in
      Exception (lid, t)
    | "NEW_EFFECT" -> NewEffect (effectDefinition ps)
    | "SUB_EFFECT" -> SubEffect (subEffect ps)
    | "BLOB" ->
      let t = tok_at ps i0 in
      (match t.extra with
       | L.Blob (name, contents, pos, snap) ->
         let blob_range = R.mk_range ps.fname snap t.ep in
         let start_range = R.mk_range ps.fname pos pos in
         DeclSyntaxExtension (name, contents, blob_range, start_range)
       | _ -> failwith "impossible: BLOB without payload")
    | _ -> ps.idx := i0; fail ps
  end

let tcinstance_attr (r:R.range) : ML term =
  mk_term (Var C.tcinstance_lid) r Type_level

let typeclassDecl (ps:pstate) : ML (decl' & list term) =
  let i0 = !ps.idx in
  if accept ps "CLASS" then begin
    let tc = typeDecl ps in
    (Tycon (false, true, [tc]), [])
  end else begin
    ignore (expect ps "INSTANCE");
    if accept ps "VAL" then begin
      let lid = lidentOrOperator ps in
      let t = val_type ps in
      (Val (lid, t), [tcinstance_attr (loc ps i0)])
    end else begin
      let q = letqualifier ps in
      let lb = letbinding ps in
      let r = loc ps i0 in
      let lbs = focusLetBindings [lb] r in
      (TopLevelLet (q, lbs), [tcinstance_attr r])
    end
  end

(* noDecorationDecl *)
let p_no_decoration_decl (ps:pstate) : ML (option (list decl)) =
  let i0 = !ps.idx in
  if is ps "ASSUME" && peek_kind_n ps 1 = "NAME" then begin
    ignore (advance ps);
    let lid = p_uident ps in
    ignore (expect ps "COLON");
    let phi = p_formula ps in
    Some [mk_decl (Assume (lid, phi)) (loc ps i0) [Qualifier Assumption]]
  end
  else if is ps "USE_LANG_BLOB" then begin
    let t = advance ps in
    match t.extra with
    | L.Blob (name, contents, pos, _) ->
      let start_range = R.mk_range ps.fname pos pos in
      let ds = AU.parse_extension_lang name contents start_range in
      Some (mk_decl (UseLangDecls name) start_range [] :: ds)
    | _ -> failwith "impossible: USE_LANG_BLOB without payload"
  end
  else None

(* decoratableDecl, with the decorations [ds] already parsed *)
let p_decoratable_decl (ps:pstate) (ds:list decoration) : ML (list decl) =
  let i_d = !ps.idx in
  if is ps "CLASS" || is ps "INSTANCE" then begin
    let (d, extra) = typeclassDecl ps in
    let d = mk_decl d (loc ps i_d) ds in
    [{ d with attrs = FStar.List.Tot.append extra d.attrs }]
  end else begin
    let d = rawDecl ps in
    [mk_decl d (loc ps i_d) ds]
  end

let p_decl (ps:pstate) : ML (list decl) =
  match p_no_decoration_decl ps with
  | Some ds -> ds
  | None ->
    let ds = decorations ps in
    p_decoratable_decl ps ds

(* ---------------------------------------------------------------------- *)
(* Entry points                                                           *)
(* ---------------------------------------------------------------------- *)

let legacy_hint_msg =
  "Syntax error. Note: 'introduce' and 'eliminate' no longer bind names for hypotheses; write 'with e' instead of 'with h. e'. The hypothesis is available in the proof context of e."

(* The error for a failed parse: at the end of the furthest token that
   the parser could not consume, as Menhir does. *)
let error_of_failure (ps:pstate) : ML E.error =
  let f = SI.max !ps.furthest !ps.idx in
  let t = tok_at ps f in
  if t.kind = "ERROR" then raise_lex_error t
  else begin
    let k (n:int) : ML string =
      let i = SI.(f - of_int n) in
      if SI.(i >= zero) then (tok_at ps i).kind else "" in
    let binder_name (n:int) : ML bool = k n = "IDENT" || k n = "UNDERSCORE" in
    let hint =
      (k 0 = "DOT" && binder_name 1 && k 2 = "WITH") ||
      (k 1 = "DOT" && binder_name 2 && k 3 = "WITH")
    in
    let msg = if hint then legacy_hint_msg else "Syntax error" in
    (Codes.Fatal_SyntaxError, FStarC.Errors.Msg.mkmsg msg, R.mk_range ps.fname t.ep t.ep, [])
  end

(* Run [f] with the terms of grammar [g], turning a failure into a syntax error *)
let run_with (#a:Type) (g:grammar) (ps:pstate) (f:unit -> ML a) : ML a =
  last_index := (SI.minus_one, SI.minus_one);
  with_grammar g (fun () ->
    try f () with
    | Fail -> raise (E.Error (error_of_failure ps)))

let run (#a:Type) (ps:pstate) (f:unit -> ML a) : ML a = run_with fstar_grammar ps f

(* Lex [contents]; [rw] may reclassify tokens, e.g. to turn the
   identifiers that are keywords of a language extension into keywords. *)
let start_with (rw:L.token -> ML L.token) (fname:string) (contents:string) (line col:int)
  : ML (pstate & list (string & R.range))
= let toks, comments = L.lex_all fname contents line col in
  let ps = mk_pstate fname (R.mk_pos line col) (map rw toks) in
  (ps, comments)

let start (fname:string) (contents:string) (line col:int) : ML (pstate & list (string & R.range)) =
  let toks, comments = L.lex_all fname contents line col in
  let ps = mk_pstate fname (R.mk_pos line col) toks in
  (ps, comments)

let parse_decls (ps:pstate) : ML (list decl) =
  let decls = run ps (fun () ->
    let rec go () : ML (list (list decl)) =
      if is ps "EOF" then []
      else
        let d = p_decl ps in
        d :: go ()
    in
    go ())
  in
  flatten decls

let parse_file (fname:string) (contents:string) (line col:int)
  : ML (inputFragment & list (string & R.range))
= let ps, comments = start fname contents line col in
  (as_frag (parse_decls ps), comments)

(* Parse already lexed tokens, for benchmarking the parser alone *)
let parse_tokens (fname:string) (toks:list L.token) : ML (list decl) =
  parse_decls (mk_pstate fname (R.mk_pos 1 0) toks)

let parse_term (fname:string) (contents:string) (line col:int) : ML term =
  let ps, _ = start fname contents line col in
  run ps (fun () ->
    let t = p_term ps in
    ignore (expect ps "EOF");
    t)

let rec drop (#a:Type) (n:int) (l:list a) : list a =
  if n <= 0 then l else match l with [] -> [] | _ :: l -> drop (n - 1) l

(* Parse declarations one by one with grammar [g], stopping at the first
   error. Each declaration must be followed by a token for which
   [next_ok] holds. *)
let parse_incremental_gen (#a:Type) (g:grammar) (ps:pstate)
    (p_one:pstate -> ML (list a)) (next_ok:string -> ML bool)
  : ML (list a & option (Codes.error_code & E.error_message & R.range))
= let rec go (acc:list a) : ML (list a & option (Codes.error_code & E.error_message & R.range)) =
    GS.reset_gensym ();
    ps.furthest := !ps.idx;
    let res =
      try
        if is ps "EOF" then Inl None
        else begin
          let ds = run_with g ps (fun () ->
            let ds = p_one ps in
            if next_ok (peek_kind ps) then ds
            else fail ps)
          in
          Inl (Some ds)
        end
      with
      | E.Error (e, msg, r, _) -> Inr (e, msg, r)
    in
    match res with
    | Inl None -> (rev acc, None)
    | Inl (Some ds) -> go (FStar.List.Tot.rev_acc ds acc)
    | Inr err -> (rev acc, Some err)
  in
  go []

(* Parse F* declarations one by one, stopping at the first error.
   Returns the declarations, the comments read (most recent first) and
   the error, if any. *)
let parse_incremental (fname:string) (contents:string) (line col:int)
  : ML (list decl & list (string & R.range) & option (Codes.error_code & E.error_message & R.range))
= let ps, comments = start fname contents line col in
  let ncomments = length comments in
  let decls, err =
    parse_incremental_gen fstar_grammar ps p_decl
      (fun k -> FStar.List.Tot.mem k start_of_next_decl_kinds)
  in
  match err with
  | None -> (decls, comments, None)
  | Some _ ->
    (* Like the lazy lexer of Menhir, only report the comments before the
       token where parsing stopped *)
    let f = SI.max !ps.furthest !ps.idx in
    let seen = (tok_at ps f).ncom in
    (decls, drop (ncomments - seen) comments, err)
