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

(* A small parsing engine: a token cursor with backtracking, plus a
   table-driven Pratt parser for terms in the style of Lean 4.

   Every term syntax is either a *leading* rule (it starts a term: a
   keyword, a prefix operator, an atom, ...) or a *trailing* rule (it
   continues a term that has already been parsed: an infix operator,
   an ascription, ...). Each rule declares its precedence explicitly:

   - a leading rule may only start a term at a position that asks for
     precedence at most [l_allowed]; the term it produces has
     precedence [l_level];

   - a trailing rule of precedence [t_level] only applies when the
     surrounding context asks for precedence at most [t_level], and
     only if the term on its left has precedence at least [t_lhs_min].
     The rule parses its own right-hand side, usually by calling
     [term_at] recursively at the precedence it wants for it.

   Rules are stored in a [grammar] keyed by token kind, so that language
   extensions can add syntax to F* terms by registering more rules. *)
module FStarC.Parser.Pratt

open FStarC
open FStarC.Effect
open FStarC.Parser.AST
open FStarC.Parser.TokenKind
module L  = FStarC.Parser.Lexer
module R  = FStarC.Range
module U  = FStarC.Util
module M  = FStarC.PSMap
module S  = FStarC.String
module A  = FStar.ImmutableArray.Base
module E  = FStarC.Errors
module GS = FStarC.GenSym
module SI = FStarC.SmallInt

(* Raised when a rule does not apply; caught by [attempt]. The position
   of the failure is recorded in [furthest] for error reporting. *)
exception Fail

(* Token positions are native integers: they are manipulated a lot. *)
type pos = SI.t

type pstate = {
  toks      : A.t L.token;
  ntoks     : pos;
  idx       : ref pos;
  furthest  : ref pos;
  fname     : string;
  start_pos : R.pos;
}

let mk_pstate (fname:string) (start_pos:R.pos) (toks:list L.token) : ML pstate =
  let arr = A.of_list toks in
  { toks = arr; ntoks = SI.array_length arr; idx = mk_ref SI.zero; furthest = mk_ref SI.zero;
    fname = fname; start_pos = start_pos }

(* The token list is never empty: it ends with EOF (or ERROR). Tokens
   past the end are that final token. *)
let last_idx (ps:pstate) : pos = SI.(ps.ntoks - one)

let tok_at (ps:pstate) (i:pos) : L.token =
  SI.array_index ps.toks (if SI.(i < ps.ntoks) then i else last_idx ps)

let raise_lex_error (#a:Type) (t:L.token) : ML a =
  match t.extra with
  | L.LexError (code, msg, r) -> raise (E.Error (code, FStarC.Errors.Msg.mkmsg msg, r, []))
  | _ -> failwith "impossible: ERROR token without payload"

(* The next token. Like the (lazy) Menhir lexer, a lexical error is only
   reported once the parser asks for the offending token, which is
   always the last one. *)
let peek (ps:pstate) : ML L.token =
  let i = !ps.idx in
  if SI.(i < last_idx ps) then SI.array_index ps.toks i
  else
    let t = SI.array_index ps.toks (last_idx ps) in
    if t.kind = ERROR then raise_lex_error t else t

let peek_kind (ps:pstate) : ML token_kind = (peek ps).kind

(* Further lookahead, [peek_n ps 0 = peek ps] *)
let peek_n (ps:pstate) (n:int) : ML L.token = tok_at ps SI.(!ps.idx + of_int n)
let peek_kind_n (ps:pstate) (n:int) : ML token_kind = (peek_n ps n).kind

let is (ps:pstate) (k:token_kind) : ML bool = peek_kind ps = k

let fail (#a:Type) (ps:pstate) : ML a =
  if SI.(!ps.idx > !ps.furthest) then ps.furthest := !ps.idx;
  raise_notrace Fail

(* Step back over the last [n] tokens *)
let backup (ps:pstate) (n:int) : ML unit = ps.idx := SI.(!ps.idx - of_int n)

let advance (ps:pstate) : ML L.token =
  let t = peek ps in
  if SI.(!ps.idx < last_idx ps) then ps.idx := SI.(!ps.idx + one);
  t

let expect (ps:pstate) (k:token_kind) : ML L.token =
  if is ps k then advance ps else fail ps

let accept (ps:pstate) (k:token_kind) : ML bool =
  if is ps k then (ignore (advance ps); true) else false

(* Run [f]; if it fails, restore the input position and the gensym
   counter, so that a failed alternative leaves no trace. *)
let attempt (#a:Type) (ps:pstate) (f:unit -> ML a) : ML (option a) =
  let i = !ps.idx in
  let g = GS.get_gensym_state () in
  try Some (f ()) with
  | Fail ->
    ps.idx := i;
    GS.set_gensym_state g;
    None

(* Does [f] succeed here? Always rewinds the input, the furthest-failure
   position and the gensym counter. *)
let lookahead (ps:pstate) (f:unit -> ML unit) : ML bool =
  let i = !ps.idx in
  let g = GS.get_gensym_state () in
  let fu = !ps.furthest in
  let ok = try f (); true with Fail -> false in
  ps.idx := i;
  ps.furthest := fu;
  GS.set_gensym_state g;
  ok

(* Positions and ranges, following Menhir's conventions: a span
   [i0, i1) of tokens starts at the start of token i0 and ends at the
   end of token i1-1; an empty span sits at the end of the previous
   token. *)
let prev_end (ps:pstate) (i:pos) : R.pos =
  if SI.(i <= zero) then ps.start_pos else (tok_at ps SI.(i - one)).ep

let span_start (ps:pstate) (i0 i1:pos) : R.pos =
  if SI.(i1 > i0) then (tok_at ps i0).sp else prev_end ps i0

let span_end (ps:pstate) (i0 i1:pos) : R.pos =
  if SI.(i1 > i0) then (tok_at ps SI.(i1 - one)).ep else prev_end ps i0

let rng (ps:pstate) (i0 i1:pos) : R.range =
  R.mk_range ps.fname (span_start ps i0 i1) (span_end ps i0 i1)

(* From the start of span [a0,a1) to the end of span [b0,b1) *)
let rng2 (ps:pstate) (a0 a1 b0 b1:pos) : R.range =
  R.mk_range ps.fname (span_start ps a0 a1) (span_end ps b0 b1)

(* The range of everything consumed since [i0] *)
let loc (ps:pstate) (i0:pos) : ML R.range = rng ps i0 !ps.idx

(* Menhir quirk: when a production starts with an inlined [ioption] that
   is empty, [$startpos] is the end of the previous token. *)
let eps_loc (ps:pstate) (i0:pos) : ML R.range =
  R.mk_range ps.fname (prev_end ps i0) (span_end ps i0 !ps.idx)

let tok_rng (ps:pstate) (t:L.token) : R.range = R.mk_range ps.fname t.sp t.ep

(* ---------------------------------------------------------------------- *)
(* Pratt parsing                                                          *)
(* ---------------------------------------------------------------------- *)

(* Parameters of a term position that are not captured by a precedence:

   - [noref]: the base terms are applications without record arguments,
     refinements [x:t{phi}], or fun/quantifiers (appTermNoRecordExp in
     the Menhir grammar), as in the types of binders, where a following
     [{ phi }] is the refinement of the binder.

   - [dom]: the precedence of the domains of arrows. Precedences strictly
     between the arrow and [dom] are disabled: [tmArrow(tmNoEq)], used for
     type ascriptions, does not allow [=] or tuples in its domains. *)
type ctx = {
  noref      : bool;
  dom        : int;
  paren_doms : bool; (* whether (#x:t) -> ... is allowed *)
}

noeq type leading_rule = {
  l_name    : string;
  l_allowed : int;
  l_level   : int;
  l_guard   : pstate -> ctx -> ML bool;
  l_run     : pstate -> ctx -> ML term;
}

(* [t_run ps ctx lhs i0] is called with the operator as the next token;
   [i0] is the index of the first token of [lhs]. *)
noeq type trailing_rule = {
  t_name    : string;
  t_level   : int;
  t_lhs_min : int;
  t_guard   : pstate -> ctx -> term -> pos -> ML bool;
  t_run     : pstate -> ctx -> term -> pos -> ML term;
}

(* Rules indexed by token kind: an array indexed by [kind_index] for the
   fixed kinds, and a map for the keywords of language extensions. *)
noeq type rules (a:Type) = {
  by_kind    : A.t (list a);
  by_keyword : M.t (list a);
}

noeq type grammar = {
  leading  : rules leading_rule;
  trailing : rules trailing_rule;
  (* Terms of maximal precedence (applications, atoms), used when no
     leading rule applies. *)
  base     : pstate -> ctx -> ML term;
  base_level : int;
}

let empty_rules (a:Type) : rules a =
  let rec go (n:int) : list (list a) = if n <= 0 then [] else [] :: go (n - 1) in
  { by_kind = A.of_list (go num_kinds); by_keyword = M.empty () }

let empty_grammar (base : pstate -> ctx -> ML term) (base_level:int) : grammar =
  { leading = empty_rules _; trailing = empty_rules _; base = base; base_level = base_level }

let add_to (#a:Type) (rs:rules a) (k:token_kind) (x:a) : ML (rules a) =
  match k with
  | KEYWORD s ->
    let l = match M.try_find rs.by_keyword s with Some l -> l | None -> [] in
    { rs with by_keyword = M.add rs.by_keyword s (FStar.List.Tot.append l [x]) }
  | _ ->
    let i = kind_index k in
    let rec go (j:int) : list (list a) =
      if j >= num_kinds then []
      else
        let l = SI.array_index rs.by_kind (SI.of_int j) in
        (if j = i then FStar.List.Tot.append l [x] else l) :: go (j + 1)
    in
    { rs with by_kind = A.of_list (go 0) }

(* Register rules. Rules for the same kind are tried in order. *)
let add_leading (g:grammar) (k:token_kind) (r:leading_rule) : ML grammar =
  { g with leading = add_to g.leading k r }

let add_trailing (g:grammar) (k:token_kind) (r:trailing_rule) : ML grammar =
  { g with trailing = add_to g.trailing k r }

let cur_grammar : ref (option grammar) = mk_ref None

let get_grammar () : ML grammar =
  match !cur_grammar with
  | Some g -> g
  | None -> failwith "Pratt: no grammar installed"

let with_grammar (#a:Type) (g:grammar) (f:unit -> ML a) : ML a =
  let saved = !cur_grammar in
  cur_grammar := Some g;
  let r = try f () with e -> cur_grammar := saved; raise e in
  cur_grammar := saved;
  r

let lookup (#a:Type) (rs:rules a) (t:L.token) : list a =
  match t.kind with
  | KEYWORD s -> (match M.try_find rs.by_keyword s with Some l -> l | None -> [])
  | k -> SI.array_index rs.by_kind (SI.of_int (kind_index k))

let in_gap (ctx:ctx) (l:int) : bool = 30 < l && l < ctx.dom

let rec find_leading (ps:pstate) (ctx:ctx) (min:int) (rs:list leading_rule) : ML (option leading_rule) =
  match rs with
  | [] -> None
  | r :: rs ->
    if min <= r.l_allowed && not (in_gap ctx r.l_level) && r.l_guard ps ctx
    then Some r
    else find_leading ps ctx min rs

let rec find_trailing (ps:pstate) (ctx:ctx) (min lvl:int) (lhs:term) (i0:pos) (rs:list trailing_rule)
  : ML (option trailing_rule) =
  match rs with
  | [] -> None
  | r :: rs ->
    if min <= r.t_level && lvl >= r.t_lhs_min && not (in_gap ctx r.t_level) && r.t_guard ps ctx lhs i0
    then Some r
    else find_trailing ps ctx min lvl lhs i0 rs

(* Can a leading rule start a term at precedence [min] here? (Does not
   consider the base parser.) *)
let has_leading (ps:pstate) (ctx:ctx) (min:int) : ML bool =
  let g = get_grammar () in
  Some? (find_leading ps ctx min (lookup g.leading (peek ps)))

(* Parse a term of precedence at least [min] *)
let rec term_at (ps:pstate) (ctx:ctx) (min:int) : ML term =
  let g = get_grammar () in
  let i0 = !ps.idx in
  let lhs, lvl =
    match find_leading ps ctx min (lookup g.leading (peek ps)) with
    | Some r -> r.l_run ps ctx, r.l_level
    | None -> g.base ps ctx, g.base_level
  in
  trailing_loop ps ctx min i0 lhs lvl

and trailing_loop (ps:pstate) (ctx:ctx) (min:int) (i0:pos) (lhs:term) (lvl:int) : ML term =
  let g = get_grammar () in
  match find_trailing ps ctx min lvl lhs i0 (lookup g.trailing (peek ps)) with
  | None -> lhs
  | Some r ->
    let lhs = r.t_run ps ctx lhs i0 in
    trailing_loop ps ctx min i0 lhs r.t_level
