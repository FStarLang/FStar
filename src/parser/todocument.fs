(*
   Copyright 2016 Microsoft Research

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
#light "off"

(** Convert Parser.Ast to Pprint.document for prettyprinting. *)
module FStar.Parser.ToDocument

open FStar
open FStar.Util
open FStar.Parser.AST
open FStar.Ident
open FStar.Const
open FStar.Pprint

module C = FStar.Syntax.Const

// VALS_HACK_HERE


(* TODO : everything is printed under the assumption of the universe option *)

// abbrev
let str s = document_of_string s

// lib
let default_or_map n f x =
  match x with
  | None -> n
  | Some x' -> f x'

(* changing PPrint's ^//^ to ^/+^ since '//' wouldn't work in F# *)
let (^/+^) prefix_ body =
  prefix 2 1 prefix_ body

let jump2 body =
  jump 2 1 body

let break1 =
  break_ 1

let parens_with_nesting contents =
  surround 2 0 lparen contents rparen

let braces_with_nesting contents =
  surround 2 1 lbrace contents rbrace

let brackets_with_nesting contents =
  surround 2 1 lbracket contents rbracket

let doc_of_fsdoc (comment,keywords) =
  group (concat [
    str comment; space;
    separate_map comma (fun (k,v) ->
      concat [str k; rarrow; str v]
    ) keywords
  ])


// Really specific functions to retro-engineer the desugaring
let is_unit e =
    match e.tm with
        | Const Const_unit -> true
        | _ -> false

let matches_var t x =
    match t.tm with
        | Var y -> Ident.lid_equals x y
        | _ -> false

let is_tuple_constructor = FStar.Syntax.is_tuple_data_lid'
let is_dtuple_constructor = FStar.Syntax.is_dtuple_data_lid'

let is_list_structure cons_lid nil_lid =
  let rec aux e = match e.tm with
    | Construct (lid, []) -> lid_equals lid nil_lid
    | Construct (lid, [ _ ; e2]) -> lid_equals lid cons_lid && is_list e2
    | _ -> false
  in aux

let is_list = is_list_structure C.cons_lid C.nil_lid
let is_lex_list = is_list_structure C.lexcons_lid C.lextop_lid

(* [extract_from_list e] assumes that [is_list_structure xxx yyy e] holds and returns the list of terms contained in the list *)
let rec extract_from_list e = match e.tm with
  | Construct (_, []) -> []
  | Construct (_, [e1 ; e2]) -> e1 :: extract_from_list e2
  | _ -> failwith "Not a list"

let rec is_ref_set e = match e.tm with
    | Var maybe_empty_lid -> lid_equals maybe_empty_lid C.tset_empty
    | App ({tm=Var maybe_singleton_lid}, {tm=App(Var maybe_ref_lid, e, Nothing)}, Nothing) ->
        lid_equals maybe_singleton_lid C.tset_singleton && lid_equals maybe_ref_lid C.heap_ref
    | App({tm=App({tm=Var maybe_union_lid}, e1, Nothing)}, e2, Nothing) ->
        lid_equals maybe_union_lid C.tset_union && is_ref_set e1 && is_ref_set e2
    | _ -> false

(* [extract_from_ref_set e] assumes that [is_ref_set e] holds and returns the list of terms contained in the set *)
let rec extract_from_ref_set e = match e.tm with
  | Var _ -> []
  | App ({tm=Var _}, {tm=App(Var _, e, Nothing)}, Nothing) -> [e]
  | App({tm = App({tm=Var _}, e1, Nothing)}, e2, Nothing) ->
      extract_ref_set e1 @ extract_ref_set e2
  | _ -> failwith "Not a ref set"


(* Automatic level assignment *)
(* would be perfect with a little of staging... *)

type associativity =
    | Left
    | Right
    | NonAssoc

(* A token is either a character c representing any string beginning with c or a complete string *)
type token = either<FStar.Char.char, string>

type associativity_level = associativity * list<token>

let matches_token (s:string) = function
    | Inl c -> s.[0] = c
    | Inr s' -> s = s'

let matches_level s (assoc_levels, tokens) =
    List.existsb (matches_token s) tokens

let assign_levels (token_associativity_spec : list<associativity_level>) : string -> int * int * int =
    in
    function s ->
        match List.find (matches_level s) level_table with
            | Some (assoc_levels, _) -> assoc_levels
            | _ -> failwith ("Unrecognized operator " ^ s)

(* Precedence and associativity levels, taken from ../src/parse.mly *)
let opinfix4 = Right, [Inr "**"]
// level backtick won't be used here
let opinfix3 = Left,  [Inl '*' ; Inl '/' ; Inl '%']
let opinfix2 = Left,  [Inl '+' ; Inl '-' ]
let minus = Left, [Inr "-"] // Sublevel of opinfix2, not a level on its own !!!
let opinfix1 = Right, [Inl '@' ; Inl '^']
let pipe_right = Left,  [Inr "|>"]
let opinfix0d = Left,  [Inl '$']
let opinfix0c = Left,  [Inl '=' ; Inl '<' ; Inl '>']
let equal = Left, [Inr "="] // Sublevel of opinfix0c, not a level on its own !!!
let opinfix0b = Left,  [Inl '&']
let opinfix0a = Left,  [Inl '|']
let colon_equals = NonAssoc, [Inr ":="]
let amp = Right, [Inr "&"]
let colon_colon = Right, [Inr "::"]

(* The latter the element, the tighter it binds *)
let level_associativity_spec =
  [
    colon_colon ;
    amp ;
    colon_equals ;
    opinfix0a ;
    opinfix0b ;
    opinfix0c ;
    opinfix0d ;
    pipe_right ;
    opinfix1 ;
    opinfix2 ;
    opinfix3 ;
    opinfix4
  ]

let level_table =
  let levels_from_associativity (l:int) = function
    | Left -> l, l, l-1
    | Right -> l-1, l, l
    | NonAssoc -> l, l, l
  in
  List.mapi (fun i (assoc, tokens) -> (levels_from_associativity i assoc, tokens)) level_associativity_spec

let max_level l =
  let find_level_and_max n level =
    match List.find (fun (_, tokens) -> tokens = snd level) level_table with
      | Some ((_,l,_), _) -> max n l
      | None -> failwith "Undefined associativity level"
  in List.fold_left find_level_and_max 0 l

let level_of_operator = assign_levels spec

let is_operatorInfix0ad12 =
    let opinfix0ad12 = [opinfix0a ; opinfix0b ; opinfix0c ; opinfix0d ; opinfix1 ; opinfix2 ] in
    fun op -> List.existsb (matches_level op) opinfix0ad12


// printer really begins here

let doc_of_let_qualifier = function
  | NoLetQualifier -> empty
  | Rec -> str "rec"
  | Mutable -> str "mutable"

(* TODO: we should take into account FsTypApp to be able to beautify the source
 * of the compiler itself *)
let doc_of_imp = function
  | Hash -> str "#"
  | UnivApp -> str "u#"
  | Nothing | FsTypApp -> empty

let rec p_term e = match e.tm with
  | Seq (e1, e2) ->
      group (p_noSeqTerm e1 ^^ semi) ^/^ p_term e2
  | e ->
      group (p_noSeqTerm e)

and p_noSeqTerm e = match e.tm with
  | Ascribed (e, t) ->
      group (p_tmIff e ^/^ str "<:" ^/^ p_typ t)
  | Op (op, [ e1; e2; e3 ]) when op = ".()<-" ->
      group (
        group (p_atomicTermNotQUident e1 ^^ dot ^^ parens_with_nesting (p_term e2)
          ^^ space ^^ larrow) ^^ jump2 (p_noSeqTerm e3))
  | Op (op, [ e1; e2; e3 ]) when op = ".[]<-" ->
      group (
        group (p_atomicTermNotQUident e1 ^^ dot ^^ brackets_with_nesting (p_term e2)
          ^^ space ^^ larrow) ^^ jump2 (p_noSeqTerm e3))
  | Requires (e, wtf) ->
      assert (wtf = None);
      group (str "requires" ^/^ p_typ e)
  | Ensures (e, wtf) ->
      assert (wtf = None);
      group (str "ensures" ^/^ p_typ e)
  | Attributes es ->
      group (str "attributes" ^/^ separate_map break1 p_atomicTerm es)
  | If (e1, e2, e3) ->
      if is_unit e3
      then group ((str "if" ^/+^ p_noSeqTerm e1) ^/^ (str "then" ^/+^ p_noSeqTerm e2))
      else
          let e2_doc =
              match e2.tm with
                  | If (_,_,e3) when is_unit e3 ->
                      parens_with_nesting (p_noSeqTerm e2)
                  | _ -> p_noSeqTerm e2
           in group (
               (str "if" ^/+^ p_noSeqTerm e1) ^/^
               (str "then" ^/+^ e2_doc) ^/^
               (str "else" ^/+^ p_noSeqTerm e3))
  | TryWith(e, branches) ->
      group (prefix2 (str "try") (p_noSeqTerm e) ^/^ str "with" ^/^ jump2 (concat_map p_patternBranch branches))
  | Match (e, branches) ->
      group (prefix2 (str "match") (p_noSeqTerm e) ^/^ str "with" ^/^ jump2 (concat_map p_patternBranch branches))
  | LetOpen (uid, e) ->
      group (str "let open" ^/^ doc_of_lid uid ^/^ str "in")
  | Let(q, hd::tl, e) ->
      group (p_letbinding (str "let" ^^ p_letqualifier q) hd ^/^ concat_map (p_letbinding (str "and")) tl)
  | Abs([{tm=PatVar(x, typ_opt)}], {tm=Match(maybe_x, branches)}) when matches_var maybe_x x ->
      str "function" ^/+^ (concat_map p_patternBranch branches)
  | Assign (id, e) ->
      group (p_lident id ^/^ larrow ^/^ p_noSeqTerm e)
  | e -> p_typ e

and p_typ e = match e.tm with
  | QForall (bs, trigger, e1)
  | QExists (bs, trigger, e1) ->
      group (
          group (p_quantifier e ^/^ binders ^^ dot ^/^ p_trigger trigger) ^/^
          p_noSeqTerm e1)
  | e -> p_simpleTerm e

and p_quantifier e = match e.tm with
    | QForall _ -> str "forall"
    | QExists _ -> str "exists"

and p_trigger pats =
    lbrace ^^ colon ^/^ jump2 (p_disjunctivePats pats) ^/^ rbrace

and p_disjunctivePats pats =
    separate_map (str "\\/") p_conjunctivePats pats

and p_conjunctivePats pats =
    group (separate_map semicolon p_appTerm pats)

and p_simpleTerm e = match e.tm with
    | Abs(pats, e) ->
        (str "fun" ^/+^ concat_map p_patternOrMultibinder pats ^/^ rarrow) ^/+^ p_term e
    | e -> p_tmIff e

and p_maybeFocusArrow b =
    if b then str "~>" else rarrow

(* slight modification here : a patternBranch always begins with a `|` *)
and p_patternBranch (focus, (pat, when_opt, e)) =
    pipe ^^ space ^^ p_disjunctivePattern pat ^/^ p_maybeWhen when_opt ^^ p_maybeFocusArrow ^/^ p_term e

and p_maybeWhen = function
    | None -> empty
    | Some e -> str "when" ^/+^ p_tmFormula e ^^ space  (*always immediately followed by an arrow*)

and p_tmIff e = match e.tm with
    | Op("<==>", [e1;e2]) -> group (p_tmImplies e1 ^/^ str "<==>" ^/^ p_tmIff e2)
    | e -> p_tmImplies e

and p_tmImplies e = match e.tm with
    | Op("==>", [e1;e2]) -> group (p_tmArrow p_tmFormula e1 ^/^ str "==>" ^/^ p_tmImplies e2)
    | e -> p_tmArrow p_tmFormula e1

and p_tmArrow p_Tm e = match e with
  | Product(bs, tgt) ->
      (* TODO : Not finished yet ! how do we print the binders bs ? *)
      group (p_tmArrowDomain p_Tm   ^^ space ^^ rarrow ^/^ p_tmArrow p_Tm tgt)
  | e -> p_Tm e

and p_tmFormula e = match e.tm with
  | Op("\\/", [e1;e2]) ->
      group (p_tmFormula e1 ^/^ str "\\/" ^/^ p_tmConjunction e2)
  | e -> p_tmConjunction e

and p_tmConjunction e = match e with
  | Op("/\\", [e1;e2]) ->
      group (p_tmConjunction e1 ^/^ str "/\\" p_tmTuple e2)
  | e -> p_tmTuple e

and p_tmTuple e = match e with
  | Construct (lid, args) when is_tuple_constructor lid ->
      separate_map comma p_tmEq args
  | e -> p_tmEq e

and paren_if curr mine doc =
  if mine <= curr then
    doc
  else
    group (lparen ^^ doc ^^ rparen)

and p_tmEq =
  let n = 6 in
  fun e -> p_tmEq' n e

and levels op =
  (* Note: it might seem surprising that we're not special-casing, say, '*' to
   * be 6, 6, 6; the user, however, may shadow the ( * ) operator with a custom
   * operator that is not associative; so, we adopt a strict (correct) behavior
   * which will result in [1*(2*3)] printed back the same way. *)
  match op.[0] with
  | '*' | '/' | '%' ->
      6, 6, 5
  | '+' | '-' ->
      5, 5, 4
  | '@' | '^' ->
      3, 4, 4
  | _ when op = "|>" ->
      3, 3, 2
  | '$' ->
      2, 2, 1
  | '=' | '<' | '>' ->
      1, 1, 0
  | '&' ->
      0, 0, -1
  | '|' ->
      -1, -1, -2
  | _ ->
      failwith ("invalid first character for infix operator " ^ op)

and p_tmEq' curr e = match e.tm with
    (* We don't have any information to print `infix` aplication *)
  | Op (op, [ e1; e2]) when is_operatorInfix0ad12 op || op = "=" || op = "|>" ->
      let left, mine, right = levels op in
      paren_if curr mine (p_tmEq' left e1 ^/^ str op ^/^ p_tmEq' right e2)
  | Op (":=", [ e1; e2 ]) ->
      group (p_tmEq e1 ^^ space ^^ equals ^^ jump2 (p_tmEq e2))
  | e -> p_tmNoEq e

and p_tmNoEq =
  let n = max_level [colon_colon ; amp ; minus ; opinfix3 ; opinfix4] in
  fun e -> p_tmNoEq' n e

and p_tmNoEq' curr e = match e.tm with
  | Construct (lid, [e1 ; e2]) when lid_equals lid C.cons_lid ->
      let op = "::" in
      let left, mine, right = levels op in
      paren_if curr mine (p_tmNoEq' left e1 ^/^ str op ^/^ p_tmNoEq' right e2)
  | Sum(binders, res) ->
      let op = "&" in
      let left, mine, right = levels op in
      let p_dsumfst b = (* TODO : how to print the binder ? *) p_binder b ^^ space ^^ str "&" in
      paren_if curr mine (concat_map p_dsumfst binders ^/^ p_tmNoEq' right e2)
  | Op (op, [ e1; e2]) when is_opinfx34 op -> // also takes care of infix '-'
      let left, mine, right = levels op in
      paren_if curr mine (p_tmNoEq' left e1 ^/^ str op ^/^ p_tmNoEq' right e2)
  | Op("-", [e]) ->
      let left, mine, right = levels "-" in
      minus ^/^ p_tmNoEq' mine e
  | NamedTyp(lid, e) ->
      group (p_lidentOrUnderscore lid ^/^ colon ^/^ p_appTerm e)
  | Refine(b, phi) ->
      (* TODO : how to print refined binder ? *)
      p_refinedBinder b phi
  | Record(with_opt, record_fields) ->
      braces_with_nesting ( default_or_map empty p_with_clause with_opt ^/^
                            separate_map semicolon p_simpleDef record_fields )
  | Op("~", [e]) ->
      group (str "~" ^/^ p_atomicTerm e)
  | e -> p_appTerm e

and p_refinedBinder b phi =
    (* TODO : complete-me !!! *)

and p_simpleDef (lid, e) =
  group (p_qlident lid ^/^ equals ^/^ p_simpleTerm e)

and p_appTerm e =
  | App (head, arg, imp) ->
      p_appTerm head ^/^ p_argTerm (arg, imp)
  | Construct (lid, args) when not (is_dtuple_constructor lid) -> (* dependent tuples are handled below *)
      p_quident lid ^/^ separate_map space p_argTerm args
  | e ->
      p_indexingTerm e

and p_argTerm arg_imp = match arg_imp with
  | (Uvar id, UnivApp) -> p_univar id
  | (u, UnivApp) -> str "u#" ^^ p_universe u
  | (e, FsTypApp) -> surround 2 1 (str "<") p_indexingTerm e (str ">")
  | (e, Hash) -> str "#" ^^ p_indexingTerm e
  | (e, Nothing) -> p_indexingTerm e

and indexingTerm_aux exit e = match e.tm with
  | Op(".()", [e1 ; e2]) ->
        group (p_indexingTerm p_atomicTermNotQUident e1 ^^ dot ^^ parens_with_nesting (p_term e2))
  | Op(".[]", [e1; e2]) ->
        group (p_indexingTerm p_atomicTermNotQUident ^^ dot ^^ brackets_with_nesting (p_term e2))
  | e ->
      exit e
and indexingTerm = indexingTerm p_atomicTerm

(* p_atomicTermQUident is merged with p_atomicTerm *)
and p_atomicTerm e = match e with
  (* already handled higher in the hierarchy *)
  | LetOpen (lid, e) ->
      p_quident lid ^^ dot ^^ parens_with_nesting (p_term e)
  | Name lid ->
      p_quident lid
  | Op(op, [e]) ->
      str op ^^ p_atomicTerm e
  | e -> p_atomicTermNotQUident

and p_atomicTermNotQUident e = match e.tm with
  | Wild -> underscore
  | Var lid when text_of_lid lid = "assert" ->
      str "assert"
  | TVar tv -> p_tvar tv
  | Const c -> p_constant c
  | Name lid when text_of_lid lid = "True" ->
      str "True"
  | Name lid when text_of_lid lid = "False" ->
      str "False"
  | Op(op, [e]) ->
    str op ^^ p_atomicTermNotQUident e
  | Op(op, []) ->
      lparen ^^ space ^^ str op ^^ space ^^ rparen
  | Construct (lid, args) when is_dependent_tuple_constructor lid ->
      surround 2 1 (lparen ^^ pipe) (separate_map comma p_tmEq args) (pipe ^^ rparen)
  | Project (e, lid) ->
      group (p_atomicTermNotQUident e ^/^ dot ^^ p_qlident lid)
  | e ->
      p_projectionLHS e
  (* BEGIN e END skipped *)

and p_projectionLHS e = match e.tm with
  | Var lid ->
      p_qlident lid
    (* fsType application skipped *)
  | Projector (constr_lid, field_lid) ->
      p_quident constr_lid ^^ dot ^^ str "?" ^^ p_lident field_lid
  | Discrim constr_lid ->
      p_quident constr_lid ^^ str "?"
  (* Should we drop this constructor ? *)
  | Paren e ->
      parens_with_nesting (p_term e)
   (* TODO : these case should not be captured above *)
  | App (Var lid, [l]) when lid_equals lid C.array_mk_array_lid && is_list l ->
      let es = extract_from_list l in
      surround 2 1 (lbracket ^^ pipe) (separate_map semicolon p_noSeqTerm es) (pipe ^^ rbracket)
  | l when is_list l ->
      brackets_with_nesting (separate_map semicolon p_noSeqTerm (extract_from_list l))
  | l when is_lex_list l ->
      surround 2 1 (percent ^^ lbracket) (separate_map semicolon p_noSeqTerm (extract_from_list l)) rbracket
  | e when is_ref_set e ->
      let es = extract_from_ref_set e in
      surrond 2 1 (bang ^^ lbrace) (separate_map comma p_appTerm es) rbrace
  (* All the cases are explicitly listed below so that a modification of the ast doesn't lead to a loop *)
  (* We must also make sure that all the constructors listed below are handled somewhere *)
  | Wild        (* p_atomicTermNotQUident *)
  | Const _     (* p_atomicTermNotQUident *)
  | Op _        (* what about 3+ args ? are all possible labels caught somewhere ? *)
  | Tvar _
  | Uvar _      (* p_arg *)
  | Var _       (* p_projectionLHS *)
  | Name _      (* p_atomicTerm *)
  | Construct _ (* p_appTerm *)
  | Abs _       (* p_simpleTerm *)
  | App _       (* p_appTerm *)
  | Let _       (* p_noSeqTerm *)
  | LetOpen _   (* p_noSeqTerm *)
  | Seq _       (* p_term *)
  | If _        (* p_noSeqTerm *)
  | Match _     (* p_noSeqTerm *)
  | TryWith _   (* p_noSeqTerm *)
  | Ascribed _  (* p_noSeqTerm *)
  | Record _    (* p_termNoEq *)
  | Project _   (* p_atomicTermNotQUident *)
  | Product _   (* p_tmArrow *)
  | Sum _       (* p_tmNoEq *)
  | QForall _   (* p_typ *)
  | QExists _   (* p_typ *)
  | Refine _    (* p_tmNoEq *)
  | NamedTyp _  (* p_tmNoEq *)
  | Requires _  (* p_noSeqTerm *)
  | Ensures _   (* p_noSeqTerm *)
  | Labeled _   (* TODO : Not handled anywhere, only used in desugar.fs *)
  | Assign _    (* p_noSeqTerm *)
  | Attributes _(* p_noSeqTerm *)
    -> parens_with_nesting (p_term e)

and p_constant = function
  | Const_effect -> str "Effect"
  | Const_unit -> str "()"
  | Const_bool b -> doc_of_bool b
  | Const_float x -> str (Util.string_of_float x)
  | Const_char x -> squotes (document_of_char x )
  | Const_string(bytes, _) -> dquotes (str (Util.string_of_bytes bytes))
  | Const_bytearray(bytes,_) -> dquotes (str (Util.string_of_bytes bytes)) ^^ str "B"
  | Const_int (repr, sign_width_opt) ->
      let signedness = function
          | Unsigned -> str "u"
          | Signed -> empty
      in
      let width = function
          | Int8 -> str "y"
          | Int16 -> str "s"
          | Int32 -> str "l"
          | Int64 -> str "L"
      in
      let ending = default_or_map empty (fun (s, w) -> signedness ^^ width w) in
      str repr ^^ ending
  | Const_range r -> str (Range.string_of_range r)
  | Const_reify -> str "reify"
  | Const_reflect lid -> p_quident lid ^^ str "?." ^^ str "reflect"

(* JP, KM: tweaked up to here *)

let doc_of_const x = match x with
  | Const_effect -> str "eff"
  | Const_unit -> str "()"
  | Const_bool b -> doc_of_bool b
  | Const_float x ->  str (Util.string_of_float x)
  | Const_char x ->   squotes (document_of_char x )
  | Const_string(bytes, _) -> dquotes (str (Util.string_of_bytes bytes))
  | Const_bytearray _  ->  str "<bytearray>"
  | Const_int (x, _) -> str x
  | Const_range r -> str (Range.string_of_range r)
  | Const_reify
  | Const_reflect _ -> str "unsupported constant"

// SI: maybe do nesting for terms with args?
let rec doc_of_term (x:term) = match x.tm with
  | Wild -> underscore
  | Requires (t, _) ->
        group (brackets (concat [(str "requires"); space; (doc_of_term t)]))
  | Ensures (t, _) ->
        group (brackets (concat [(str "ensures"); space; (doc_of_term t)]))
  | Labeled (t, l, _) ->
        group (brackets (concat [(str "labeled"); space; (str l); (doc_of_term t)]))
  | Const c -> group (doc_of_const c)
  | Op(s, xs) ->
        group (concat [(str s); (brackets (separate_map (str ", ") doc_of_term xs))])
  | Tvar id -> group (str id.idText)
  | Var l
  | Name l -> group (str l.str)
  | Construct (l, args) ->
        group (brackets (
                concat [(str l.str); space;
                        (separate_map space (fun (a,imp) -> concat [(doc_of_imp imp); (doc_of_term a)]) args)]))
  | Abs(pats, t) ->
        group (brackets (
                concat [(str "fun"); space;
                        (separate_map space doc_of_pat pats);
                        space; (str "->"); space;
                        (doc_of_term t)]))
  | App(t1, t2, imp) ->
        group (concat [
                    (doc_of_term t1); space;
                    (doc_of_imp imp); (doc_of_term t2)])
  | Let (Rec, lbs, body) ->
        group (concat [(str "let rec"); space;
                        (separate_map (str " and ") (fun (p,b) -> concat [(doc_of_pat p); equals; (doc_of_term b)]) lbs);
                        space; (str "in"); space;
                        (doc_of_term body)])
  | Let (q, [(pat,tm)], body) ->
        group (concat [(str "let"); space;
                       (doc_of_let_qualifier q); space;
                       (doc_of_pat pat); space;
                       equals; space;
                       (doc_of_term tm);
                       space; (str "in"); space;
                       (doc_of_term body)])
  | Seq(t1, t2) ->
        group (concat [doc_of_term t1; semi; space; doc_of_term t2])
  | If(t1, t2, t3) ->
        group (concat [(str "if"); space; (doc_of_term t1); space; (str "then"); space;
                       (nest 2 (doc_of_term t2));
                       (str "else"); space;
                       (nest 2 (doc_of_term t3))])
  | Match(t, branches) ->
       group (concat
                [(str "match"); space; (doc_of_term t); space; (str "with"); space;
                 (separate_map hardline
                     (fun (p,w,e) -> concat [(str " | ");
                                             (doc_of_pat p); space;
                                             (match w with | None -> empty | Some e -> concat [str "when "; (doc_of_term e)]);
                                             space; (str "->"); space;
                                             (doc_of_term e)])
                     branches)])
  | Ascribed(t1, t2) ->
        group (concat [doc_of_term t1; space; colon; space; doc_of_term t2])
  | Record(Some e, fields) ->
        group (concat [
                    lbrace; (doc_of_term e); space; str "with"; space;
                    separate_map space
                        (fun (l,e) -> concat [str l.str; equals; doc_of_term e])
                        fields;
                    rbrace])
  | Record(None, fields) ->
        group (concat [
                    lbrace;
                    separate_map space
                        (fun (l,e) -> concat [(str l.str); equals; (doc_of_term e)])
                        fields;
                    rbrace
                    ])
  | Project(e,l) ->
        group (concat [doc_of_term e; dot; str l.str])
  | Product([], t) ->
        group (doc_of_term t)
  | Product(b::hd::tl, t) ->
        group (doc_of_term (mk_term (Product([b], mk_term (Product(hd::tl, t)) x.range x.level)) x.range x.level))
  | Product([b], t) when (x.level = Type) ->
        group (concat [(doc_of_binder b); space; str "->"; space; (doc_of_term t)])
  | Product([b], t) when (x.level = Kind) ->
        group (concat [(doc_of_binder b); space; str "=>"; space; (doc_of_term t)])
  | Sum(binders, t) ->
        group (concat [(separate_map (str " * ") doc_of_binder binders);
                       space; str "*"; space;
                       doc_of_term t])
  | QForall(bs, pats, t) ->
        group (concat [
                    str "forall"; space;
                    separate_map space doc_of_binder bs;
                    dot; lbrace; colon; str "pattern"; space;
                    // TODO: should the separator be /\ here?
                    separate_map (str " \/ ") (separate_map (concat [semi; space]) doc_of_term) pats;
                    rbrace; space;
                    doc_of_term t])
  | QExists(bs, pats, t) ->
        group (concat [
                    str "exists"; space;
                    separate_map space doc_of_binder bs;
                    dot; lbrace; colon; str "pattern"; space;
                    separate_map (str " \/ ") (separate_map (concat [semi; space]) doc_of_term) pats;
                    rbrace; space;
                    doc_of_term t])


  | Refine(b, t) ->
        group (concat [
                    doc_of_binder b;
                    colon;
                    lbrace; doc_of_term t; rbrace])
  | NamedTyp(x, t) ->
        group (concat [str x.idText; colon; doc_of_term t])
  | Paren t -> group (parens (doc_of_term t))
  | Product(bs, t) ->
        group (concat [
                    str "Unidentified product: [";
                    separate_map comma doc_of_binder bs;
                    str "]"; space;
                    doc_of_term t])
  | t -> underscore

and doc_of_binder x =
  let s = match x.b with
  | Variable i -> str i.idText
  | TVariable i -> concat [str i.idText; colon; underscore]
  | TAnnotated(i,t)
  | Annotated(i,t) -> concat [str i.idText; colon; doc_of_term t]
  | NoName t -> doc_of_term t in
  concat [doc_of_aqual x.aqual;  s]

and doc_of_aqual = function
   | Some Equality -> str "$"
   | Some Implicit -> str "#"
   | _ -> empty

and doc_of_pat x = match x.pat with
  | PatWild -> underscore
  | PatConst c -> doc_of_const c
  | PatApp(p, ps) ->
        group (parens (concat [(doc_of_pat p); space; (separate_map space doc_of_pat ps)]))
  | PatTvar (i, aq)
  | PatVar (i,  aq) ->
        group (concat [(doc_of_aqual aq); (str i.idText)])
  | PatName l -> str l.str
  | PatList l -> group (brackets (separate_map (concat [semi; space]) doc_of_pat l))
  | PatTuple (l, false) -> group (parens (separate_map (concat [semi; space]) doc_of_pat l))
  | PatTuple (l, true) -> group (parens (concat [bar; (separate_map (concat [comma; space]) doc_of_pat l); bar]))
  | PatRecord l ->
        group (braces (separate_map (concat [semi; space]) (fun (f,e) -> concat [(str f.str); equals; (doc_of_pat e)]) l))
  | PatOr l ->  separate_map (concat [bar; hardline; space]) doc_of_pat l
  | PatOp op ->  parens (str op)
  | PatAscribed(p,t) -> group (parens (concat [doc_of_pat p; colon; doc_of_term t]))

let rec head_id_of_pat p = match p.pat with
        | PatName l -> [l]
        | PatVar (i, _) -> [Ident.lid_of_ids [i]]
        | PatApp(p, _) -> head_id_of_pat p
        | PatAscribed(p, _) -> head_id_of_pat p
        | _ -> []

let lids_of_let defs =  defs |> List.collect (fun (p, _) -> head_id_of_pat p)

// TODO: check with parser re how these are printed.
let doc_of_tycon = function
  | TyconAbstract(i, bb, k) ->
        group (concat [str "abstract"; space;
                       (separate_map space doc_of_binder bb); space;
                       default_or_map empty doc_of_term k; space;
                       hardline
                       ])
  // TODO bb, k, t, flds, vars
  | TyconAbbrev(i, bb, k, t) -> group (str i.idText)
  | TyconRecord(i, bb, k, flds) ->
        group (concat [str i.idText; space; equals; space;
                       (separate_map space doc_of_binder bb); space;
                       default_or_map empty doc_of_term k; space;
                       braces ((separate_map (concat [space; semi; space])
                                    (fun (i,t,d) -> concat [str i.idText; space; colon; space; doc_of_term t])
                                    flds))])
  | TyconVariant(i, bb, k, vars) -> group (str i.idText)

let doc_of_decl (d:decl) = match d.d with
  | TopLevelModule l ->
      group (str "module" ^/^ str l.str)
  | Open l ->
      group (str "open" ^/^ str l.str)
  | ModuleAbbrev (i, l) ->
      group (str "module" ^/^ str i.idText ^/^ equals ^/^ str l.str)
  | KindAbbrev(i, bb, k) ->
        group (concat [(str "kind"); space; (str i.idText);
                        (separate_map space
                            (fun b -> doc_of_binder b)
                            bb);
                        space; equals; space; (doc_of_term k);  hardline])
  | TopLevelLet(qq, lq, pats_terms) ->
        // TODO: qq, lq.
        let head_ids = List.collect (fun (p,_) -> head_id_of_pat p) pats_terms in
        group (concat [(str "let"); space;
                       (separate_map (str ", ")
                            (fun l -> str l.str)
                            head_ids);
                       hardline] )
  | Main e -> group (concat [str "main"; space; doc_of_term e])
  | Assume(q, i, t) ->
    // TODO: q, i.
        group (concat [ (str "assume"); space; (str i.idText); hardline])
  | Tycon(q, tys) ->
    // TODO: q. Also, print "type" here, or in doc_of_tycon?
        group (concat [(str "type"); space;
                        (separate_map (str ", ")
                            // TODO: d
                            (fun (x,d) -> doc_of_tycon x)
                            tys);
                        hardline ])
  | Val(_, i, _) -> concat [(str "val "); (str i.idText); hardline]
  | Exception(i, _) -> concat [(str "exception "); (str i.idText); hardline]
  | NewEffect(_, DefineEffect(i, _, _, _, _))
  | NewEffect(_, RedefineEffect(i, _, _)) -> concat [(str "new_effect) "); (str i.idText); hardline]
  | NewEffectForFree(_, DefineEffect(i, _, _, _, _))
  | NewEffectForFree(_, RedefineEffect(i, _, _)) -> concat [(str "new_effect_for_free "); (str i.idText); hardline]
  | SubEffect l -> str "sub_effect"
  | Pragma p -> str "pragma"
  | Fsdoc d -> group (concat [doc_of_fsdoc d; hardline])

// SI: go straight to decls (might have to change if TopLevel is not the first decl).
let doc_of_modul (m:modul) =
  match m with
  | Module (_, decls)
  | Interface (_, decls, _) ->
      decls |> List.map doc_of_decl |> separate hardline


