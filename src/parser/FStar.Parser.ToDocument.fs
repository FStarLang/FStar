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
open FStar.Pervasives
open FStar.ST
open FStar.All

open FStar
open FStar.Util
open FStar.Parser.AST
open FStar.Ident
open FStar.Const
open FStar.Pprint
open FStar.Range

module C = FStar.Parser.Const
module BU = FStar.Util



(* !!! SIDE EFFECT WARNING !!! *)
(* There are 3 uses of global side-effect in the printer for : *)
(* - Printing F# style type application [should_print_fs_typ_app] *)
(* - Printing the comments [comment_stack] *)

let maybe_unthunk t =
    match t.tm with
    | Abs ([_], body) -> body
    | _ -> t

let min x y = if x > y then y else x
let max x y = if x > y then x else y

// VD: copied over from NBE, should both probably go in FStar.List
let map_rev (f: 'a -> 'b) (l: list<'a>): list<'b> =
  let rec aux (l:list<'a>) (acc:list<'b>) =
    match l with
    | [] -> acc
    | x :: xs -> aux xs (f x :: acc)
  in
  aux l []

let map_if_all (f: 'a -> option<'b>) (l: list<'a>): option<list<'b>> =
  let rec aux l acc =
    match l with
    | [] -> acc
    | x :: xs ->
      (match f x with
       | Some r -> aux xs (r :: acc)
       | None -> [])
  in
  let r = aux l [] in
  if List.length l = List.length r then
    Some r
  else None

let rec all (f: 'a -> bool) (l: list<'a>): bool =
  match l with
  | [] -> true
  | x :: xs -> if f x then all f xs else false

let all1_explicit (args:list<(term*imp)>) : bool =
    not (List.isEmpty args) &&
    BU.for_all (function
                | (_, Nothing) -> true
                | _ -> false) args

(* [should_print_fs_typ_app] is set when encountering a [LightOff] pragma and *)
(* reset at the end of each module. If you are using individual print function you *)
(* should wrap them in [with_fs_typ_app] *)
let should_print_fs_typ_app = BU.mk_ref false

(* Tuples which come from a resugared AST, via term_to_document are already flattened *)
(* This reference is set to false in term_to_document and checked in p_tmNoEqWith'    *)
let unfold_tuples = BU.mk_ref true

let with_fs_typ_app b printer t =
  let b0 = !should_print_fs_typ_app in
  should_print_fs_typ_app := b ;
  let res = printer t in
  should_print_fs_typ_app := b0 ;
  res


// abbrev
let str s = doc_of_string s

// lib
let default_or_map n f x =
  match x with
  | None -> n
  | Some x' -> f x'

// changing PPrint's ^//^ to ^/+^ since '//' wouldn't work in F#
let prefix2 prefix_ body = prefix 2 1 prefix_ body

let prefix2_nonempty prefix_ body =
  if body = empty then prefix_ else prefix2 prefix_ body

let ( ^/+^ ) prefix_ body = prefix2 prefix_ body

let jump2 body =
  jump 2 1 body

let infix2 = infix 2 1
let infix0 = infix 0 1

let break1 =
  break_ 1


(* [separate_break_map sep f l] has the following
  [(f l[0]) sep (f l[1]) ... sep (f l[n])]
  and the following non flat layout
  [(f l[0]) sep
  (f l[1]) sep
  ...
  (f l[n])]
*)
let separate_break_map sep f l =
    group (separate_map (space ^^ sep ^^ break1) f l)

(* [precede_break_separate_map prec sep f l] has the flat layout

  [prec (f l[0]) sep (f l[1]) ... sep (f l[n])]

  and the following non flat layout

  [prec (f l[0])
    sep (f l[1])
    ...
    sep (f l[n])]
*)
let precede_break_separate_map prec sep f l =
    precede (prec ^^ space) (List.hd l |> f)  ^^ concat_map (fun x -> break1 ^^ sep ^^ space ^^ f x) (List.tl l)

let concat_break_map f l = group (concat_map (fun x -> f x ^^ break1) l)

let parens_with_nesting contents =
  surround 2 0 lparen contents rparen

let soft_parens_with_nesting contents =
  soft_surround 2 0 lparen contents rparen

let braces_with_nesting contents =
  surround 2 1 lbrace contents rbrace

let soft_braces_with_nesting contents =
  soft_surround 2 1 lbrace contents rbrace

let soft_braces_with_nesting_tight contents =
  soft_surround 2 0 lbrace contents rbrace

let brackets_with_nesting contents =
  surround 2 1 lbracket contents rbracket

let soft_brackets_with_nesting contents =
  soft_surround 2 1 lbracket contents rbracket

let soft_begin_end_with_nesting contents =
  soft_surround 2 1 (str "begin") contents (str "end")

let separate_map_last sep f es =
  let l = List.length es in
  let es = List.mapi (fun i e -> f (i <> l - 1) e) es in
  separate sep es

let separate_break_map_last sep f l =
    group (separate_map_last (space ^^ sep ^^ break1) f l)

let separate_map_or_flow sep f l =
    if List.length l < 10
    then separate_map sep f l
    else flow_map sep f l

let flow_map_last sep f es =
  let l = List.length es in
  let es = List.mapi (fun i e -> f (i <> l - 1) e) es in
  flow sep es

let separate_map_or_flow_last sep f l =
    if List.length l < 10
    then separate_map_last sep f l
    else flow_map_last sep f l

let separate_or_flow sep l = separate_map_or_flow sep id l

let surround_maybe_empty n b doc1 doc2 doc3 =
  if doc2 = empty then
    group (doc1 ^/^ doc3)
  else
    surround n b doc1 doc2 doc3

let soft_surround_separate_map n b void_ opening sep closing f xs =
  if xs = []
  then void_
  else soft_surround n b opening (separate_map sep f xs) closing

let soft_surround_map_or_flow n b void_ opening sep closing f xs =
  if xs = []
  then void_
  else soft_surround n b opening (separate_map_or_flow sep f xs) closing


// Really specific functions to retro-engineer the desugaring
let is_unit e =
    match e.tm with
        | Const Const_unit -> true
        | _ -> false

let matches_var t x =
    match t.tm with
        | Var y -> (string_of_id x) = string_of_lid y
        | _ -> false

let is_tuple_constructor = C.is_tuple_data_lid'
let is_dtuple_constructor = C.is_dtuple_data_lid'

let is_list_structure cons_lid nil_lid =
  let rec aux e = match e.tm with
    | Construct (lid, []) -> lid_equals lid nil_lid
    | Construct (lid, [ _ ; e2, _]) -> lid_equals lid cons_lid && aux e2
    | _ -> false
  in aux

let is_list = is_list_structure C.cons_lid C.nil_lid

(* [extract_from_list e] assumes that [is_list_structure xxx yyy e] holds *)
(* and returns the list of terms contained in the list *)
let rec extract_from_list e = match e.tm with
  | Construct (_, []) -> []
  | Construct (_, [e1,Nothing ; e2, Nothing]) -> e1 :: extract_from_list e2
  | _ -> failwith (Util.format1 "Not a list %s" (term_to_string e))

let is_array e = match e.tm with
    (* TODO check that there is no implicit parameters *)
    | App ({tm=Var lid}, l, Nothing) -> lid_equals lid C.array_of_list_lid && is_list l
    | _ -> false

let rec is_ref_set e = match e.tm with
    | Var maybe_empty_lid -> lid_equals maybe_empty_lid C.set_empty
    | App ({tm=Var maybe_singleton_lid}, {tm=App({tm=Var maybe_addr_of_lid}, e, Nothing)}, Nothing) ->
        lid_equals maybe_singleton_lid C.set_singleton && lid_equals maybe_addr_of_lid C.heap_addr_of_lid
    | App({tm=App({tm=Var maybe_union_lid}, e1, Nothing)}, e2, Nothing) ->
        lid_equals maybe_union_lid C.set_union && is_ref_set e1 && is_ref_set e2
    | _ -> false

(* [extract_from_ref_set e] assumes that [is_ref_set e] holds and returns the list of terms contained in the set *)
let rec extract_from_ref_set e = match e.tm with
  | Var _ -> []
  | App ({tm=Var _}, {tm=App({tm=Var _}, e, Nothing)}, Nothing) -> [e]
  | App({tm = App({tm=Var _}, e1, Nothing)}, e2, Nothing) ->
      extract_from_ref_set e1 @ extract_from_ref_set e2
  | _ -> failwith (Util.format1 "Not a ref set %s" (term_to_string e))

let is_general_application e =
  not (is_array e || is_ref_set e)

let is_general_construction e =
  not (is_list e)

let is_general_prefix_op op =
  let op_starting_char =  char_at (Ident.string_of_id op) 0 in
  op_starting_char = '!' || op_starting_char = '?' ||
  (op_starting_char = '~' && Ident.string_of_id op <> "~")

(* might already exist somewhere *)
let head_and_args e =
  let rec aux e acc = match e.tm with
  | App (head, arg, imp) -> aux head ((arg,imp)::acc)
  | _ -> e, acc
  in aux e []


(* Automatic level assignment *)
(* would be perfect with a little of staging... *)
(* TODO : see if we can plug in the menhir inspection API so that *)
(* the level_associativity_spec table below is produced by the parser *)

type associativity =
    | Left
    | Right
    | NonAssoc

(* A token is either a character c representing any string beginning with c or a complete string *)
type token = either<FStar.Char.char, string>

type associativity_level = associativity * list<token>

let token_to_string = function
    | Inl c -> string_of_char c ^ ".*"
    | Inr s -> s

let matches_token (s:string) = function
    | Inl c -> FStar.String.get s 0 = c
    | Inr s' -> s = s'

let matches_level s (assoc_levels, tokens) =
    List.tryFind (matches_token s) tokens <> None

// GM 05/10/18, TODO: This still needs to be heavily annotated with the new unifier:

(* Precedence and associativity levels, taken from ../src/parse.mly *)
let opinfix4 : associativity_level = Right, [Inr "**"]
// level backtick won't be used here
let opinfix3 : associativity_level = Left,  [Inl '*' ; Inl '/' ; Inl '%']
let opinfix2 : associativity_level = Left,  [Inl '+' ; Inl '-' ]
let minus_lvl : associativity_level = Left, [Inr "-"] // Sublevel of opinfix2, not a level on its own !!!
let opinfix1 : associativity_level = Right, [Inl '@' ; Inl '^']
let pipe_right : associativity_level = Left,  [Inr "|>"]
let opinfix0d : associativity_level = Left,  [Inl '$']
let opinfix0c : associativity_level = Left,  [Inl '=' ; Inl '<' ; Inl '>']
let equal : associativity_level = Left, [Inr "="] // Sublevel of opinfix0c, not a level on its own !!!
let opinfix0b : associativity_level = Left,  [Inl '&']
let opinfix0a : associativity_level = Left,  [Inl '|']
let colon_equals : associativity_level = NonAssoc, [Inr ":="]
let amp : associativity_level = Right, [Inr "&"]
let colon_colon : associativity_level = Right, [Inr "::"]

(* The latter the element, the tighter it binds *)
let level_associativity_spec : list<associativity_level> =
  [
    opinfix4 ;
    opinfix3 ;
    opinfix2 ;
    opinfix1 ;
    pipe_right ;
    opinfix0d ;
    opinfix0c ;
    opinfix0b ;
    opinfix0a ;
    colon_equals ;
    amp ;
    colon_colon ;
  ]

let level_table =
  let levels_from_associativity (l:int) = function
    | Left -> l, l, l-1
    | Right -> l-1, l, l
    | NonAssoc -> l - 1, l, l - 1
  in
  List.mapi (fun i (assoc, tokens) -> (levels_from_associativity i assoc, tokens)) level_associativity_spec

let assign_levels (token_associativity_spec : list<associativity_level>) (s:string) : int * int * int =
    match List.tryFind (matches_level s) level_table with
        | Some (assoc_levels, _) -> assoc_levels
        | _ -> failwith ("Unrecognized operator " ^ s)

let max_level l =
  let find_level_and_max n level =
    match List.tryFind (fun (_, tokens) -> tokens = snd level) level_table with
      | Some ((_,l,_), _) -> max n l
      | None -> failwith (Util.format1 "Undefined associativity level %s"
                                      (String.concat "," (List.map token_to_string (snd level))))
  in List.fold_left find_level_and_max 0 l

let levels op =
  (* See comment in parse.fsy: tuples MUST be parenthesized because [t * u * v]
   * is not the same thing as [(t * u) * v]. So, we are conservative and make an
   * exception for the "*" operator and treat it as, really, non-associative. If
   * the AST comes from the user, then the Paren node was there already and no
   * extra parentheses are added. If the AST comes from some client inside of
   * the F* compiler that doesn't know about this quirk, then it forces it to be
   * parenthesized properly. In case the user overrode * to be a truly
   * associative operator (e.g. multiplication) then we're just being a little
   * conservative because, unlike ToSyntax.fs, we don't have lexical context to
   * help us determine which operator this is, really. *)
  let left, mine, right = assign_levels level_associativity_spec op in
  if op = "*" then
    left - 1, mine, right
  else
    left, mine, right

let operatorInfix0ad12 = [opinfix0a ; opinfix0b ; opinfix0c ; opinfix0d ; opinfix1 ; opinfix2 ]

let is_operatorInfix0ad12 op =
    List.tryFind (matches_level <| Ident.string_of_id op) operatorInfix0ad12 <> None

let is_operatorInfix34 =
    let opinfix34 = [ opinfix3 ; opinfix4 ] in
    fun op -> List.tryFind (matches_level <| Ident.string_of_id op) opinfix34 <> None

let handleable_args_length (op:ident) =
  let op_s = Ident.string_of_id op in
  if is_general_prefix_op op || List.mem op_s [ "-" ; "~" ] then 1
  else if (is_operatorInfix0ad12 op ||
    is_operatorInfix34 op ||
    List.mem op_s ["<==>" ; "==>" ; "\\/" ; "/\\" ; "=" ; "|>" ; ":=" ; ".()" ; ".[]"])
  then 2
  else if (List.mem op_s [".()<-" ; ".[]<-"]) then 3
  else 0

let handleable_op op args =
  match List.length args with
  | 0 -> true
  | 1 -> is_general_prefix_op op || List.mem (Ident.string_of_id op) [ "-" ; "~" ]
  | 2 ->
    is_operatorInfix0ad12 op ||
    is_operatorInfix34 op ||
    List.mem (Ident.string_of_id op) ["<==>" ; "==>" ; "\\/" ; "/\\" ; "=" ; "|>" ; ":=" ; ".()" ; ".[]"]
  | 3 -> List.mem (Ident.string_of_id op) [".()<-" ; ".[]<-"]
  | _ -> false


// Style choice for type signatures. Depending on available space, they
// can be printed in one of three ways:
//   (1) all on the same line
//   (2) all on the same line, except the computation type, which is
//   pushed on a new line
//   (3) keyword and identifier on one line, then every binder and the
//   computation type on separate lines; binders can also be spread over
//   multiple lines
// In case (2), the first parameter controls indentation for the
// computation type. In case (3), first parameter is indentation for each
// of the binders, second parameter is indendation for the computation
// type.
// The third parameter in Binders controls whether each binder is
// paranthesised
type annotation_style =
  | Binders of int * int * bool // val f (x1:t1) ... (xn:tn) : C
  | Arrows of int * int //  val f : x1:t1 -> ... -> xn:tn -> C

// decide whether a type signature can be printed in the format
//   val f (x1:t1) ... (xn:tn) : C
// it can't if either not all args are annotated binders or if it has no
// arguments, in which case it will be printed using the colon + arrows style
let all_binders_annot e =
  let is_binder_annot b =
    match b.b with
    | Annotated _ -> true
    | _ -> false
  in
  let rec all_binders e l =
    match e.tm with
    | Product(bs, tgt) ->
      if List.for_all is_binder_annot bs then
        all_binders tgt (l+ List.length bs)
      else
        (false, 0)
    | _ -> (true, l+1)
  in
  let b, l = all_binders e 0 in
  if b && l > 1 then true else false

type catf = document -> document -> document
let cat_with_colon x y = x ^^ colon ^/^ y


(* ****************************************************************************)
(*                                                                            *)
(*                   Taking care of comments                                  *)
(*                                                                            *)
(* ****************************************************************************)

(* Comments are not part of the AST but can be collected by the lexer so that we *)
(* can try to reinstate them when printing. Since they are not inside the AST, we *)
(* need to find some valid place to place them back. *)

(* We assume that comments are tagged by their original position (a range) and *)
(* that they are given in the order they appear. Then we use the range information *)
(* inside the printed AST to reinstate the comments. *)

(* The rules for placing comments are : *)
(* 1. There is at most one comment per line *)
(* 2. Line feeds between comments occuring between two toplevel declarations are *)
(*    preserved *)
(* 3. A comment is printed just before some AST node if it has not been printed *)
(*    before and its range ends before the end of the line where the AST node *)
(*    was originally *)
(* 4. Left-over comments are always printed even if the position could be meaningless *)
(* 5. The AST node on which comments can be attached are the one using the *)
(*    [with_comment] function defined just below *)

(* Since comments are using side effects to be printed in the correct order it is important *)
(* that all printed AST nodes that could eventually contain a comment are printed in the *)
(* sequential order of the document. *)

let comment_stack : ref<(list<(string*range)>)>= BU.mk_ref []

(* some meta-information that informs spacing and the placement of comments around a declaration *)
type decl_meta =
    {r: range;
     has_qs: bool; //has quantifiers
     has_attrs: bool; //has attributes
     }
let dummy_meta = {r = dummyRange; has_qs = false; has_attrs = false}

// TODO: rewrite in terms of with_comment_sep (some tricky issues with spacing)
let with_comment printer tm tmrange =
  let rec comments_before_pos acc print_pos lookahead_pos =
    match !comment_stack with
    | [] -> acc, false
    | (c, crange) :: cs ->
      let comment = str c ^^ hardline in
      if range_before_pos crange print_pos
      then begin
        comment_stack := cs ;
        comments_before_pos (acc ^^ comment) print_pos lookahead_pos
      end
      else acc, range_before_pos crange lookahead_pos
  in
  let comments, has_lookahead =
      comments_before_pos empty (end_of_line ( start_of_range tmrange)) (end_of_range tmrange)
  in
  let printed_e = printer tm in
  let comments =
      if has_lookahead
      then
        let pos = end_of_range tmrange in
        fst (comments_before_pos comments pos pos)
      else comments
  in
  if comments = empty then
    printed_e
  else
    group (comments ^^ printed_e)

let with_comment_sep printer tm tmrange =
  let rec comments_before_pos acc print_pos lookahead_pos =
    match !comment_stack with
    | [] -> acc, false
    | (c, crange) :: cs ->
      let comment = str c in
      if range_before_pos crange print_pos
      then begin
        comment_stack := cs ;
        comments_before_pos (if acc = empty then comment else acc ^^ hardline ^^ comment) print_pos lookahead_pos
      end
      else acc, range_before_pos crange lookahead_pos
  in
  let comments, has_lookahead =
      comments_before_pos empty (end_of_line ( start_of_range tmrange)) (end_of_range tmrange)
  in
  let printed_e = printer tm in
  let comments =
      if has_lookahead
      then
        let pos = end_of_range tmrange in
        fst (comments_before_pos comments pos pos)
      else comments
  in
  comments, printed_e


(* [place_comments_until_pos k lbegin pos doc r init] appends to doc all the comments present in *)
(* [comment_stack] whose range is before pos and separate each comments by as many lines *)
(* as indicated by the range information (at least [k]) using [lbegin] as the last line of *)
(* [doc] in the original document. Between 2 comments [k] is set to [1] *)
(* r is true if this is a recursive call (i.e. a comment has been placed) *)
(* init is true when placing the initial comment *)
let rec place_comments_until_pos (k: int) (lbegin: int) pos meta_decl doc (r: bool) (init: bool) =
  match !comment_stack with
  | (comment, crange) :: cs when range_before_pos crange pos ->
    comment_stack := cs ;
    let lnum = max k (line_of_pos (start_of_range crange) - lbegin) in
    let lnum = min 2 lnum in
    let doc = doc ^^ repeat lnum hardline ^^ str comment in
    place_comments_until_pos 1 (line_of_pos (end_of_range crange)) pos meta_decl doc true init
  | _ ->
    if doc = empty then
      empty
    else
      // lnum is initially (approximately) the number of newlines between the end of the previous declaration
      // and the beginning of the one currently being printed, in the original source file (which may change
      // during prettyprinting), not accounting for qualifiers and attributes; as a consequence,
      // we have to massage this number in the following steps in order to achieve some sensible spacing and
      // to keep prettyprinting idempotent
      let lnum = line_of_pos pos - lbegin in

      // limit the number of newlines between declarations to 3 (2 empty lines in between)
      let lnum = min 3 lnum in

      // range information does not include qualifiers or attributes (the start position is at "let"),
      // so we need to account for (at least) one extra line
      let lnum = if meta_decl.has_qs || meta_decl.has_attrs then lnum - 1 else lnum in

      // make sure lnum is not smaller than k
      let lnum = max k lnum in

      // if the declaration has both qualifiers and attributes (which each go on a separate line)
      // force exactly 2 spaces; this compromise will mean that the following declaration is always
      // separated by exactly 1 empty line
      let lnum = if meta_decl.has_qs && meta_decl.has_attrs then 2 else lnum in

      // if the module begins with a comment, force exactly 2 newlines between it and the following declaration
      let lnum = if init then 2 else lnum in

      doc ^^ repeat lnum hardline


(* [separate_map_with_comments prefix sep f xs extract_meta] is the document *)
(*                                                                            *)
(*   prefix (f xs[0]) *)
(*   comments[0] *)
(*   sep (f xs[1]) *)
(*   comments[1] *)
(*   ... *)
(*   sep (f xs[n]) *)
(*                                                                            *)
(* where comments[_] are obtained by successive calls to [place_comments_until_pos] *)
(* using the range and metainformation provided by [extract_meta] and the comments in *)
(* [comment_stack]. [xs] must contain at least one element. There is no break *)
(* inserted after [prefix] and [sep]. *)
let separate_map_with_comments prefix sep f xs extract_meta =
  let fold_fun (last_line, doc) x =
    let meta_decl = extract_meta x in
    let r = meta_decl.r in
    let doc = place_comments_until_pos 1 last_line (start_of_range r) meta_decl doc false false in
    line_of_pos (end_of_range r), doc ^^ sep ^^ f x
  in
  let x, xs = List.hd xs, List.tl xs in
  let init =
    let meta_decl = extract_meta x in
    line_of_pos (end_of_range meta_decl.r), prefix ^^ f x
  in
  snd (List.fold_left fold_fun init xs)

(* [separate_map_with_comments_kw prefix sep f xs extract_meta] is the same  *)
(* as separate_map_with_comments but the keyword is also passed as an         *)
(* argument to f, resulting in                                                *)
(*                                                                            *)
(*   (f prefix xs[0]) *)
(*   comments[0] *)
(*   f spe xs[1]) *)
(*   comments[1] *)
(*   ... *)
(*   (f sep xs[n]) *)
let separate_map_with_comments_kw prefix sep f xs extract_meta =
  let fold_fun (last_line, doc) x =
    let meta_decl = extract_meta x in
    let r = meta_decl.r in
    let doc = place_comments_until_pos 1 last_line (start_of_range r) meta_decl doc false false in
    line_of_pos (end_of_range r), doc ^^ f sep x
  in
  let x, xs = List.hd xs, List.tl xs in
  let init =
    let meta_decl = extract_meta x in
    line_of_pos (end_of_range meta_decl.r), f prefix x
  in
  snd (List.fold_left fold_fun init xs)


(* ****************************************************************************)
(*                                                                            *)
(*                        Printing declarations                               *)
(*                                                                            *)
(* ****************************************************************************)
let rec p_decl (d: decl): document =
  let qualifiers=
    (* Don't push 'assume' on a new line when it used as a keyword *)
    match (d.quals, d.d) with
    | ([Assumption], Assume(id, _)) ->
      if char_at (string_of_id id) 0 |> is_upper then
        p_qualifier Assumption ^^ space
      else
        p_qualifiers d.quals
    | _ -> p_qualifiers d.quals
  in
  p_attributes d.attrs ^^
  qualifiers ^^
  p_rawDecl d

and p_attributes attrs =
    match attrs with
    | [] -> empty
    | _ -> lbracket ^^ str "@@ " ^^
             align ((flow (str "; ") (List.map (p_noSeqTermAndComment false false) attrs)) ^^ rbracket) ^^ hardline

and p_justSig d = match d.d with
  | Val (lid, t) ->
      (str "val" ^^ space ^^ p_lident lid ^^ space ^^ colon) ^^ p_typ false false t
  | TopLevelLet (_, lbs) ->
      separate_map hardline (fun lb -> group (p_letlhs (str "let") lb false)) lbs
  | _ ->
      empty

and p_list f sep l =
    let rec p_list' = function
        | [] -> empty
        | [x] -> f x
        | x::xs -> f x ^^ sep ^^ p_list' xs
    in
    str "[" ^^ p_list' l ^^ str "]"

and p_rawDecl d = match d.d with
  | Open uid ->
    group (str "open" ^/^ p_quident uid)
  | Include uid ->
    group (str "include" ^/^ p_quident uid)
  | Friend uid ->
    group (str "friend" ^/^ p_quident uid)
  | ModuleAbbrev (uid1, uid2) ->
    (str "module" ^^ space ^^ p_uident uid1 ^^ space ^^ equals) ^/+^ p_quident uid2
  | TopLevelModule uid ->
    group(str "module" ^^ space ^^ p_quident uid)
  | Tycon(true, _, [TyconAbbrev(uid, tpars, None, t)]) ->
    let effect_prefix_doc = str "effect" ^^ space ^^ p_uident uid in
    surround 2 1 effect_prefix_doc (p_typars tpars) equals ^/+^ p_typ false false t
  | Tycon(false, tc, tcdefs) ->
    let s = if tc then str "class" else str "type" in
    (p_typeDeclWithKw s (List.hd tcdefs)) ^^
      (concat_map (fun x -> break1 ^^ p_typeDeclWithKw (str "and") x) <| List.tl tcdefs)
  | TopLevelLet(q, lbs) ->
    let let_doc = str "let" ^^ p_letqualifier q in
    separate_map_with_comments_kw let_doc (str "and") p_letbinding lbs
      (fun (p, t) ->
        { r = Range.union_ranges p.prange t.range;
          has_qs = false;
          has_attrs = false; })
  | Val(lid, t) ->
    group <| str "val" ^^ space ^^ p_lident lid ^^ (sig_as_binders_if_possible t false)
    (* KM : not exactly sure which one of the cases below and above is used for 'assume val ..'*)
  | Assume(id, t) ->
    let decl_keyword =
      if char_at (string_of_id id) 0 |> is_upper
      then empty
      else str "val" ^^ space
    in
    decl_keyword ^^ p_ident id ^^ group (colon ^^ space ^^ (p_typ false false t))
  | Exception(uid, t_opt) ->
    str "exception" ^^ space ^^ p_uident uid ^^ optional (fun t -> break1 ^^ str "of" ^/+^ p_typ false false t) t_opt
  | NewEffect(ne) ->
    str "new_effect" ^^ space ^^ p_newEffect ne
  | SubEffect(se) ->
    str "sub_effect" ^^ space ^^ p_subEffect se
  | LayeredEffect(ne) ->
    str "layered_effect" ^^ space ^^ p_newEffect ne
  | Polymonadic_bind (l1, l2, l3, t) ->
    (str "polymonadic_bind")
          ^^ lparen ^^ p_quident l1 ^^ comma ^^ break1 ^^ p_quident l2 ^^ rparen
          ^^ (str "|>") ^^ p_quident l3 ^^ equals ^^ p_simpleTerm false false t
  | Pragma p ->
    p_pragma p
  | Tycon(true, _, _) ->
    failwith "Effect abbreviation is expected to be defined by an abbreviation"
  | Splice (ids, t) ->
    str "%splice" ^^ p_list p_uident (str ";") ids ^^ space ^^ p_term false false t

(* !!! Side-effect !!! : When a [#light "off"] is printed it activates the fs_typ_app *)
and p_pragma = function
  | SetOptions s -> str "#set-options" ^^ space ^^ dquotes (str s)
  | ResetOptions s_opt -> str "#reset-options" ^^ optional (fun s -> space ^^ dquotes (str s)) s_opt
  | PushOptions s_opt -> str "#push-options" ^^ optional (fun s -> space ^^ dquotes (str s)) s_opt
  | PopOptions -> str "#pop-options"
  | RestartSolver -> str "#restart-solver"
  | LightOff ->
      should_print_fs_typ_app := true ;
      str "#light \"off\""

(* TODO : needs to take the F# specific type instantiation *)
and p_typars (bs: list<binder>): document = p_binders true bs

and p_typeDeclWithKw kw typedecl =
  let comm, decl, body, pre = p_typeDecl kw typedecl in
  if comm = empty then
    decl ^^ pre body
  else
    group <| ifflat
      (decl ^^ pre body ^/^ comm)
      (decl ^^ nest 2 (hardline ^^ comm ^^ hardline ^^ body))

(* [p_typeDecl pre decl] takes a prefix and a declaration and returns a comment associated with the *)
(* declaration, the formatted declaration, its body, and a spacing function which should be applied to *)
(* the body in order to correctly space it from the declaration if there is no comment present or if *)
(* the comment can be inlined after the body *)
and p_typeDecl pre = function
  | TyconAbstract (lid, bs, typ_opt) ->
    empty, p_typeDeclPrefix pre false lid bs typ_opt, empty, id
  | TyconAbbrev (lid, bs, typ_opt, t) ->
    let comm, doc = p_typ_sep false false t in
    comm, p_typeDeclPrefix pre true lid bs typ_opt, doc, jump2
  | TyconRecord (lid, bs, typ_opt, record_field_decls) ->
    let p_recordField (ps: bool) (lid, aq, attrs, t) =
      let comm, field =
        with_comment_sep (p_recordFieldDecl ps) (lid, aq, attrs, t)
                         (extend_to_end_of_line t.range) in
      let sep = if ps then semi else empty in
      inline_comment_or_above comm field sep
    in
    let p_fields = braces_with_nesting (
        separate_map_last hardline p_recordField record_field_decls)
    in
    empty, p_typeDeclPrefix pre true lid bs typ_opt, p_fields, (fun d -> space ^^ d)
  | TyconVariant (lid, bs, typ_opt, ct_decls) ->
    let p_constructorBranchAndComments (uid, t_opt, use_of) =
        let range = extend_to_end_of_line (dflt (range_of_id uid) (map_opt t_opt (fun t -> t.range))) in
        let comm, ctor = with_comment_sep p_constructorBranch (uid, t_opt, use_of) range in
        inline_comment_or_above comm ctor empty
    in
    (* Beware of side effects with comments printing *)
    let datacon_doc =
        separate_map hardline p_constructorBranchAndComments ct_decls
    in
    empty, p_typeDeclPrefix pre true lid bs typ_opt, datacon_doc, jump2

and p_typeDeclPrefix kw eq lid bs typ_opt =
  let with_kw cont =
    let lid_doc = p_ident lid in
    let kw_lid = group (kw ^/^ lid_doc) in
    cont kw_lid
  in
  let typ =
    let maybe_eq = if eq then equals else empty in
    match typ_opt with
    | None -> maybe_eq
    | Some t -> colon ^^ space ^^ (p_typ false false t) ^/^ maybe_eq
  in
  if bs = []
  then
    with_kw (fun n -> prefix2 n typ)
  else
    let binders = p_binders_list true bs in
    with_kw (fun n -> prefix2 (prefix2 n (flow break1 binders)) typ)

and p_recordFieldDecl ps (lid, aq, attrs, t) =
  group (optional p_aqual aq ^^ p_attributes attrs ^^ p_lident lid ^^ colon ^^ p_typ ps false t)

and p_constructorBranch (uid, t_opt, use_of) =
  let sep = if use_of then str "of" else colon in
  let uid_doc = group (bar ^^ space ^^ p_uident uid) in
  default_or_map uid_doc (fun t -> (group (uid_doc ^^ space ^^ sep ^^ space ^^ p_typ false false t))) t_opt

and p_letlhs kw (pat, _) inner_let =
  (* TODO : this should be refined when head is an applicative pattern (function definition) *)
  let pat, ascr =
    // if the let binding was written in arrow style, the arguments will be in t
    // if it was written in binders style then they will be in pat
    match pat.pat with
    | PatAscribed (pat, (t, None)) -> pat, Some (t, empty)
    | PatAscribed (pat, (t, Some tac)) -> pat, Some (t, group (space ^^ str "by" ^^ space ^^ p_atomicTerm (maybe_unthunk tac)))
    | _ -> pat, None
  in
  match pat.pat with
  | PatApp ({pat=PatVar (lid, _, _)}, pats) ->
      (* has binders *)
      let ascr_doc =
        (match ascr with
         | Some (t, tac) -> (sig_as_binders_if_possible t true) ^^ tac
         | None -> empty)
      in
      let terms, style =
        // VD: should we indent inner lets less?
        if inner_let then
          let bs, style = pats_as_binders_if_possible pats in
          bs @ [ascr_doc], style
        else
          let bs, style = pats_as_binders_if_possible pats in
          bs @ [ascr_doc], style
      in
      group <| kw ^^ space ^^ p_lident lid ^^ (format_sig style terms true true)
  | _ ->
      (* doesn't have binders *)
      let ascr_doc =
        (match ascr with
         | Some (t, tac) -> group (colon ^^ p_typ_top (Arrows (2, 2)) false false t) ^^ tac
         | None -> empty)
      in
      group (group (kw ^/^ p_tuplePattern pat) ^^ ascr_doc)

and p_letbinding kw (pat, e) =
  let doc_pat = p_letlhs kw (pat, e) false in
  let comm, doc_expr = p_term_sep false false e in
  let doc_expr = inline_comment_or_above comm doc_expr empty in
  ifflat (doc_pat ^/^ equals ^/^ doc_expr) (doc_pat ^^ space ^^ group (equals ^^ jump2 doc_expr))

and p_term_list ps pb l =
    let rec aux = function
        | [] -> empty
        | [x] -> p_term ps pb x
        | x::xs -> p_term ps pb x ^^ str ";" ^^ aux xs
    in
    str "[" ^^ aux l ^^ str "]"


(* ****************************************************************************)
(*                                                                            *)
(*                          Printing effects                                  *)
(*                                                                            *)
(* ****************************************************************************)

and p_newEffect = function
  | RedefineEffect (lid, bs, t) ->
    p_effectRedefinition lid bs t
  | DefineEffect (lid, bs, t, eff_decls) ->
    p_effectDefinition lid bs t eff_decls

and p_effectRedefinition uid bs t =
    surround_maybe_empty 2 1 (p_uident uid) (p_binders true bs) (prefix2 equals (p_simpleTerm false false t))

and p_effectDefinition uid bs t eff_decls =
  let binders = p_binders true bs in
  braces_with_nesting (
    group (surround_maybe_empty 2 1 (p_uident uid) (p_binders true bs) (prefix2 colon (p_typ false false t))) ^/^
    (str "with") ^^ hardline ^^ space ^^ space ^^ (separate_map_last (hardline ^^ semi ^^ space) p_effectDecl eff_decls))

and p_effectDecl ps d = match d.d with
  | Tycon(false, _, [TyconAbbrev(lid, [], None, e)]) ->
      prefix2 (p_lident lid ^^ space ^^ equals) (p_simpleTerm ps false e)
  | _ ->
      failwith (Util.format1 "Not a declaration of an effect member... or at least I hope so : %s"
                              (decl_to_string d))

and p_subEffect lift =
  let lift_op_doc =
    let lifts =
      match lift.lift_op with
        | NonReifiableLift t -> ["lift_wp", t]
        | ReifiableLift (t1, t2) -> ["lift_wp", t1 ; "lift", t2]
        | LiftForFree t -> ["lift", t]
    in
    let p_lift ps (kwd, t) = prefix2 (str kwd ^^ space ^^ equals) (p_simpleTerm ps false t) in
    separate_break_map_last semi p_lift lifts
  in
  prefix2 (p_quident lift.msource ^^ space ^^ str "~>") (p_quident lift.mdest) ^^
    space ^^ braces_with_nesting lift_op_doc


(* ****************************************************************************)
(*                                                                            *)
(*                     Printing qualifiers, tags                              *)
(*                                                                            *)
(* ****************************************************************************)

and p_qualifier = function
  | Private -> str "private"
  | Noeq -> str "noeq"
  | Unopteq -> str "unopteq"
  | Assumption -> str "assume"
  | DefaultEffect -> str "default"
  | TotalEffect -> str "total"
  | Effect_qual -> empty
  | New -> str "new"
  | Inline -> str "inline"
  | Visible -> empty
  | Unfold_for_unification_and_vcgen -> str "unfold"
  | Inline_for_extraction -> str "inline_for_extraction"
  | Irreducible -> str "irreducible"
  | NoExtract -> str "noextract"
  | Reifiable -> str "reifiable"
  | Reflectable -> str "reflectable"
  | Opaque -> str "opaque"
  | Logic -> str "logic"

and p_qualifiers qs =
  match qs with
  | [] -> empty
  | [q] -> (p_qualifier q) ^^ hardline
  | _ -> flow break1 (List.map p_qualifier qs) ^^ hardline

(* Skipping focus since it cannot be recoverred at printing *)

and p_letqualifier = function
  | Rec -> space ^^ str "rec"
  | NoLetQualifier -> empty

and p_aqual = function
  | Implicit -> str "#"
  | Equality -> str "$"
  | Meta t ->
    let t =
      match t.tm with
      | Abs (_ ,e) -> e
      | _ -> mk_term (App (t, unit_const t.range, Nothing)) t.range Expr
    in
    str "#[" ^^ p_term false false t ^^ str "]" ^^ break1

(* ****************************************************************************)
(*                                                                            *)
(*                     Printing patterns and binders                          *)
(*                                                                            *)
(* ****************************************************************************)

and p_disjunctivePattern p = match p.pat with
  | PatOr pats ->
    group (separate_map (break1 ^^ bar ^^ space) p_tuplePattern pats)
  | _ -> p_tuplePattern p

and p_tuplePattern p = match p.pat with
  | PatTuple (pats, false) ->
      group (separate_map (comma ^^ break1) p_constructorPattern pats)
  | _ ->
      p_constructorPattern p

and p_constructorPattern p = match p.pat with
  | PatApp({pat=PatName maybe_cons_lid}, [hd ; tl]) when lid_equals maybe_cons_lid C.cons_lid ->
      infix0 (colon ^^ colon) (p_constructorPattern hd) (p_constructorPattern tl)
  | PatApp ({pat=PatName uid}, pats) ->
      prefix2 (p_quident uid) (separate_map break1 p_atomicPattern pats)
  | _ ->
      p_atomicPattern p

and p_atomicPattern p = match p.pat with
  | PatAscribed (pat, (t, None)) ->
    (* This inverts the first rule of atomicPattern (LPAREN tuplePattern COLON
     * simpleArrow RPAREN). *)
    begin match pat.pat, t.tm with
    | PatVar (lid, aqual, attrs), Refine({b = Annotated(lid', t)}, phi)
      when (string_of_id lid) = (string_of_id lid') ->
      (* p_refinement jumps into p_appTerm for the annotated type; this is
       * tighter than simpleArrow (which is what the parser uses), meaning that
       * this printer may conservatively insert parentheses. TODO fix, but be
       * aware that there are multiple callers to p_refinement and that
       * p_appTerm is probably the lower bound of all expected levels. *)
      soft_parens_with_nesting (p_refinement aqual attrs (p_ident lid) t phi)
    | PatWild (aqual, attrs), Refine({b = NoName t}, phi) ->
      soft_parens_with_nesting (p_refinement aqual attrs underscore t phi)
    | _ ->
        (* TODO implement p_simpleArrow *)
        soft_parens_with_nesting (p_tuplePattern pat ^^ colon ^/^ p_tmEqNoRefinement t)
    end
  | PatList pats ->
    surround 2 0 lbracket (separate_break_map semi p_tuplePattern pats) rbracket
  | PatRecord pats ->
    let p_recordFieldPat (lid, pat) = infix2 equals (p_qlident lid) (p_tuplePattern pat) in
    soft_braces_with_nesting (separate_break_map semi p_recordFieldPat pats)
  | PatTuple(pats, true) ->
    surround 2 1 (lparen ^^ bar) (separate_break_map comma p_constructorPattern pats) (bar ^^ rparen)
  | PatTvar (tv, arg_qualifier_opt, attrs) ->
    assert (arg_qualifier_opt = None) ;
    assert (attrs = []);
    p_tvar tv
  | PatOp op ->
    lparen ^^ space ^^ str (Ident.string_of_id op) ^^ space ^^ rparen
  | PatWild (aqual, attrs) ->
    optional p_aqual aqual ^^ p_attributes attrs ^^ underscore
  | PatConst c ->
    p_constant c
  | PatVar (lid, aqual, attrs) ->
    optional p_aqual aqual ^^ p_attributes attrs ^^ p_lident lid
  | PatName uid ->
      p_quident uid
  | PatOr _ -> failwith "Inner or pattern !"
  | PatApp ({pat = PatName _}, _)
  | PatTuple (_, false) ->
      soft_parens_with_nesting (p_tuplePattern p)
  | _ -> failwith (Util.format1 "Invalid pattern %s" (pat_to_string p))

(* Skipping patternOrMultibinder since it would need retro-engineering the flattening of binders *)

and is_typ_tuple e = match e.tm with
  | Op(id, _) when string_of_id id = "*" -> true
  | _ -> false

and is_meta_qualifier aq =
  match aq with
  | Some (Meta _) -> true
  | _ -> false

and p_binder is_atomic b =
  let b', t', catf = p_binder' is_atomic b in
  match t' with
  | Some typ -> catf b' typ
  | None -> b'

(* is_atomic is true if the binder must be parsed atomically *)
and p_binder' (is_atomic: bool) (b: binder): document * option<document> * catf =
  match b.b with
  | Variable lid -> optional p_aqual b.aqual ^^ p_lident lid, None, cat_with_colon
  | TVariable lid -> p_lident lid, None, cat_with_colon
  | Annotated (lid, t) ->
      let b', t' =
        match t.tm with
        | Refine ({b = Annotated (lid', t)}, phi) when (string_of_id lid) = (string_of_id lid') ->
          p_refinement' b.aqual b.battributes (p_lident lid) t phi
        | _ ->
          let t' = if is_typ_tuple t then
            soft_parens_with_nesting (p_tmFormula t)
          else
            p_tmFormula t
          in
          optional p_aqual b.aqual ^^ p_lident lid, t'
        in
        let catf =
          if is_atomic || (is_meta_qualifier b.aqual) then
            (fun x y -> group (lparen ^^ (cat_with_colon x y) ^^ rparen))
          else
            (fun x y -> group (cat_with_colon x y))
        in
        b', Some t', catf
  | TAnnotated _ -> failwith "Is this still used ?"
  | NoName t ->
    begin match t.tm with
      | Refine ({b = NoName t}, phi) ->
        let b', t' = p_refinement' b.aqual b.battributes underscore t phi in
        b', Some t', cat_with_colon
      | _ ->
        if is_atomic
        then p_atomicTerm t, None, cat_with_colon (* t is a type but it might need some parenthesis *)
        else p_appTerm t, None, cat_with_colon (* This choice seems valid (used in p_tmNoEq') *)
    end

and p_refinement aqual_opt attrs binder t phi =
  let b, typ = p_refinement' aqual_opt attrs binder t phi in
  cat_with_colon b typ

and p_refinement' aqual_opt attrs binder t phi =
  let is_t_atomic =
    match t.tm with
    | Construct _
    | App _
    | Op _ -> false
    | _ -> true
    in
  let comm, phi = p_noSeqTerm false false phi in
  let phi = if comm = empty then phi else comm ^^ hardline ^^ phi in
  (* If t is atomic, don't put a space between t and phi
   * If t can be displayed on a single line, tightly surround it with braces,
   * otherwise pad with a space. *)
  let jump_break = if is_t_atomic then 0 else 1 in
  (optional p_aqual aqual_opt ^^ p_attributes attrs ^^ binder),
    (p_appTerm t ^^
      (jump 2 jump_break (group ((ifflat
        (soft_braces_with_nesting_tight phi) (soft_braces_with_nesting phi))))))

(* TODO : we may prefer to flow if there are more than 15 binders *)
(* Note: also skipping multiBinder here. *)
and p_binders_list (is_atomic: bool) (bs: list<binder>): list<document> = List.map (p_binder is_atomic) bs

and p_binders (is_atomic: bool) (bs: list<binder>): document = separate_or_flow break1 (p_binders_list is_atomic bs)


(* ****************************************************************************)
(*                                                                            *)
(*                Printing identifiers and module paths                       *)
(*                                                                            *)
(* ****************************************************************************)

and string_of_id_or_underscore lid =
  if starts_with (string_of_id lid) reserved_prefix && not (Options.print_real_names ())
  then underscore
  else str (string_of_id lid)

and text_of_lid_or_underscore lid =
  if starts_with (string_of_id (ident_of_lid lid)) reserved_prefix && not (Options.print_real_names ())
  then underscore
  else str (string_of_lid lid)

and p_qlident lid =
  text_of_lid_or_underscore lid

and p_quident lid =
  text_of_lid_or_underscore lid

and p_ident lid =
  string_of_id_or_underscore lid

and p_lident lid =
  string_of_id_or_underscore lid

and p_uident lid =
  string_of_id_or_underscore lid

and p_tvar lid =
  string_of_id_or_underscore lid

(* ****************************************************************************)
(*                                                                            *)
(*                     Printing terms and types                               *)
(*                                                                            *)
(* ****************************************************************************)

(* The grammar has shift-reduce conflicts, meaning that the printer, in addition
 * to following the structure of the parser, must have extra machinery.
 * Shift-reduce conflicts arise from two situations:
 * - e1; e2 where e1 ends with a greedy construct that swallows semicolons (for
 *   instance, MATCH, LET, an operator that ends with LARROW are greedy -- IF is
 *   not)
 * - ... -> e1 | ... -> ... where e1 ends with a greedy construct that swallows
 *   bars (MATCH, TRY, FUNCTION); note that FUN is not a greedy construct in
 *    this context; also note that this does not apply to the last branch...
 *
 * To deal with this issue, we keep two flags in our series of recursive calls;
 * "ps" (protect semicolons) and "pb" (protect branches). Whenever we enter a
 * greedy construct, we wrap it with parentheses to make it non-greedy.
 *
 * This is convenient: at every call-site, we need to understand whether we need
 * to prevent swallowing semicolons or not. For instance, in a record field, we
 * do. *)

and paren_if (b:bool) =
  if b then
    soft_parens_with_nesting
  else
    fun x -> x

and inline_comment_or_above comm doc sep =
    if comm = empty then
      group (doc ^^ sep)
    else
      group <| ifflat (group (doc ^^ sep ^^ break1 ^^ comm)) (comm ^^ hardline ^^ doc ^^ sep)

and p_term (ps:bool) (pb:bool) (e:term) = match e.tm with
  | Seq (e1, e2) ->
      (* Don't swallow semicolons on the left-hand side of a semicolon! Note:
       * the `false` for pb is kind of useless because there is no construct
       * that swallows branches but not semicolons (meaning ps implies pb). *)
      let comm, t1 = p_noSeqTerm true false e1 in
      (inline_comment_or_above comm t1 semi) ^^ hardline ^^ p_term ps pb e2

  | Bind(x, e1, e2) ->
      group ((p_lident x ^^ space ^^ long_left_arrow) ^/+^
      (p_noSeqTermAndComment true false e1 ^^ space ^^ semi)) ^/^ p_term ps pb e2
  | _ ->
      group (p_noSeqTermAndComment ps pb e)

and p_term_sep (ps:bool) (pb:bool) (e:term) = match e.tm with
  | Seq (e1, e2) ->
      (* Don't swallow semicolons on the left-hand side of a semicolon! Note:
       * the `false` for pb is kind of useless because there is no construct
       * that swallows branches but not semicolons (meaning ps implies pb). *)
      let comm, t1 = p_noSeqTerm true false e1 in
      comm, group (t1 ^^ semi) ^^ hardline ^^ p_term ps pb e2
  | Bind(x, e1, e2) ->
      empty, group ((p_lident x ^^ space ^^ long_left_arrow) ^/+^
      (p_noSeqTermAndComment true false e1 ^^ space ^^ semi)) ^/^ p_term ps pb e2
  | _ ->
     p_noSeqTerm ps pb e

and p_noSeqTerm ps pb e = with_comment_sep (p_noSeqTerm' ps pb) e e.range

and p_noSeqTermAndComment ps pb e = with_comment (p_noSeqTerm' ps pb) e e.range

and p_noSeqTerm' ps pb e = match e.tm with
  | Ascribed (e, t, None) ->
      group (p_tmIff e ^/^ langle ^^ colon ^/^ p_typ ps pb t)
  | Ascribed (e, t, Some tac) ->
      group (p_tmIff e ^/^ langle ^^ colon ^/^ p_typ false false t ^/^ str "by" ^/^ p_typ ps pb (maybe_unthunk tac))
  | Op (id, [ e1; e2; e3 ]) when string_of_id id = ".()<-" ->
      group (
        group (p_atomicTermNotQUident e1 ^^ dot ^^ soft_parens_with_nesting (p_term false false e2)
          ^^ space ^^ larrow) ^^ jump2 (p_noSeqTermAndComment ps pb e3))
  | Op (id, [ e1; e2; e3 ]) when string_of_id id = ".[]<-" ->
      group (
        group (p_atomicTermNotQUident e1 ^^ dot ^^ soft_brackets_with_nesting (p_term false false e2)
          ^^ space ^^ larrow) ^^ jump2 (p_noSeqTermAndComment ps pb e3))
  | Requires (e, wtf) ->
      assert (wtf = None);
      group (str "requires" ^/^ p_typ ps pb e)
  | Ensures (e, wtf) ->
      assert (wtf = None);
      group (str "ensures" ^/^ p_typ ps pb e)
  | WFOrder (rel, e) ->
    p_dec_wf ps pb rel e
  | LexList l ->
      group (str "%" ^^ p_term_list ps pb l)
  | Decreases (e, wtf) ->
      assert (wtf = None);
      group (str "decreases" ^/^ p_typ ps pb e)
  | Attributes es ->
      group (str "attributes" ^/^ separate_map break1 p_atomicTerm es)
  | If (e1, ret_opt, e2, e3) ->
      (* No need to wrap with parentheses here, since if e1 then e2; e3 really
       * does parse as (if e1 then e2); e3 -- the IF does not swallow
       * semicolons. We forward our caller's [ps] parameter, though, because
       * something in [e2] may swallow. *)
      if is_unit e3
      then group ((str "if" ^/+^ p_noSeqTermAndComment false false e1) ^/^ (str "then" ^/+^ p_noSeqTermAndComment ps pb e2))
      else
           let e2_doc =
              match e2.tm with
                  (* Not protecting, since an ELSE follows. *)
                  | If (_,_, _,e3) when is_unit e3 ->
                      (* Dangling else *)
                      soft_parens_with_nesting (p_noSeqTermAndComment false false e2)
                  | _ -> p_noSeqTermAndComment false false e2
          in 
          (match ret_opt with
           | None ->
             group (
               (str "if" ^/+^ p_noSeqTermAndComment false false e1) ^/^
               (str "then" ^/+^ e2_doc) ^/^
               (str "else" ^/+^ p_noSeqTermAndComment ps pb e3))
           | Some ret ->
              group (
                (str "if" ^/+^ p_noSeqTermAndComment false false e1) ^/^
                (str "ret" ^/+^ p_tmIff ret) ^/^
                (str "then" ^/+^ e2_doc) ^/^
                (str "else" ^/+^ p_noSeqTermAndComment ps pb e3)))
  | TryWith(e, branches) ->
      paren_if (ps || pb) (
          group (prefix2 (str "try") (p_noSeqTermAndComment false false e) ^/^ str "with" ^/^
              separate_map_last hardline p_patternBranch branches))
  | Match (e, ret_opt, branches) ->
      paren_if (ps || pb) (

      (match ret_opt with
       | None ->
        group (surround 2 1 (str "match") (p_noSeqTermAndComment false false e) (str "with"))
       | Some ret ->
        group (surround 2 1 (str "match")
                            ((p_noSeqTermAndComment false false e) ^/+^ (str "returns" ^/+^ p_tmIff ret))
                            (str "with")))
        
      ^/^
       
      separate_map_last hardline p_patternBranch branches)
  | LetOpen (uid, e) ->
      paren_if ps (
        group (surround 2 1 (str "let open") (p_quident uid) (str "in") ^/^ p_term false pb e)
      )
  | LetOpenRecord (r, rty, e) ->
      paren_if ps (
        group (surround 2 1 (str "let open") (p_term false pb r) (str "as") ^/^ (p_term false pb rty)
               ^/^ str "in" ^/^ p_term false pb e)
      )
  | Let(q, lbs, e) ->
    (* We wish to print let-bindings as follows.
     *
     * [@ attribute ]
     * let x = foo
     * and x =
     *   too long to fit on one line
     * in
     * ... *)
    let p_lb q (a, (pat, e)) is_last =
      let attrs = p_attrs_opt a in
      let doc_let_or_and = match q with
        | Some Rec -> group (str "let" ^/^ str "rec")
        | Some NoLetQualifier -> str "let"
        | _ -> str "and"
      in
      let doc_pat = p_letlhs doc_let_or_and (pat, e) true in
      let comm, doc_expr = p_term_sep false false e in
     let doc_expr = inline_comment_or_above comm doc_expr empty in
     attrs ^^
      (if is_last then
       surround 2 1 (flow break1 [doc_pat; equals]) doc_expr (str "in")
      else
        hang 2 (flow break1 [doc_pat; equals; doc_expr]))
    in
    let l = List.length lbs in
    let lbs_docs = List.mapi (fun i lb ->
      if i = 0 then
        group (p_lb (Some q) lb (i = l - 1))
      else
        group (p_lb None lb (i = l - 1))
    ) lbs in
    let lbs_doc = group (separate break1 lbs_docs) in
    paren_if ps (group (lbs_doc ^^ hardline ^^ p_term false pb e))

  | Abs([{pat=PatVar(x, typ_opt, _)}], {tm=Match(maybe_x, None, branches)}) when matches_var maybe_x x ->
    paren_if (ps || pb) (
      group (str "function" ^/^ separate_map_last hardline p_patternBranch branches))
  | Quote (e, Dynamic) ->
    group (str "quote" ^/^ p_noSeqTermAndComment ps pb e)
  | Quote (e, Static) ->
    group (str "`" ^^ p_noSeqTermAndComment ps pb e)
  | VQuote e ->
    group (str "`%" ^^ p_noSeqTermAndComment ps pb e)
  | Antiquote ({ tm = Quote (e, Dynamic) }) ->
    group (str "`@" ^^ p_noSeqTermAndComment ps pb e)
  | Antiquote e ->
    group (str "`#" ^^ p_noSeqTermAndComment ps pb e)
  | CalcProof (rel, init, steps) ->
    let head = str "calc" ^^ space ^^ p_noSeqTermAndComment false false rel ^^ space ^^ lbrace in
    let bot = rbrace in
    enclose head (hardline ^^ bot)
         (nest 2 <| hardline
                    ^^ p_noSeqTermAndComment false false init ^^ str ";" ^^ hardline
                    ^^ separate_map_last hardline p_calcStep steps)
  | _ -> p_typ ps pb e

and p_dec_wf ps pb rel e =
  group (str "{:well-founded " ^^ p_typ ps pb rel ^/^ p_typ ps pb e ^^ str " }")


and p_calcStep _ (CalcStep (rel, just, next)) =
  group (p_noSeqTermAndComment false false rel ^^ space ^^ lbrace ^^ space ^^ p_noSeqTermAndComment false false just ^^ space ^^ rbrace ^^ hardline
         ^^ p_noSeqTermAndComment false false next ^^ str ";")

and p_attrs_opt = function
  | None -> empty
  | Some terms ->
    group (str "[@@" ^/^
           (separate_map (str "; ")
                         (p_noSeqTermAndComment false false)
                         terms) ^/^
           str "]")

and p_typ ps pb e = with_comment (p_typ' ps pb) e e.range

and p_typ_sep ps pb e = with_comment_sep (p_typ' ps pb) e e.range

and p_typ' ps pb e = match e.tm with
  | QForall (bs, (_, trigger), e1)
  | QExists (bs, (_, trigger), e1) ->
      let binders_doc = p_binders true bs in
      let term_doc = p_noSeqTermAndComment ps pb e1 in
      //VD: We could dispense with this pattern matching if we removed trailing whitespace after the fact
      (match trigger with
       | [] ->
         prefix2
          (soft_surround 2 0 (p_quantifier e ^^ space) binders_doc dot) term_doc
       | pats ->
         prefix2 (group (prefix2
           (soft_surround 2 0 (p_quantifier e ^^ space) binders_doc dot)
            (p_trigger trigger))) term_doc)
  | _ -> p_simpleTerm ps pb e

and p_typ_top style ps pb e = with_comment (p_typ_top' style ps pb) e e.range

and p_typ_top' style ps pb e = p_tmArrow style true p_tmFormula e

and sig_as_binders_if_possible t extra_space =
  let s = if extra_space then space else empty in
  if all_binders_annot t then
    (s ^^ p_typ_top (Binders (4, 0, true)) false false t)
  else
    group (colon ^^ s ^^ p_typ_top (Arrows (2, 2)) false false t)

and collapse_pats (pats: list<(document * document)>): list<document> =
  let fold_fun (bs: list<(list<document> * document)>) (x: document * document) =
    let b1, t1 = x in
    match bs with
    | [] -> [([b1], t1)]
    | hd::tl ->
      let b2s, t2 = hd in
      if t1 = t2 then
        (b2s @ [b1], t1) :: tl
      else
        ([b1], t1) :: hd :: tl
  in
  let p_collapsed_binder (cb: list<document> * document): document =
    let bs, typ = cb in
    match bs with
    | [] -> failwith "Impossible" // can't have dangling type
    | [b] -> cat_with_colon b typ
    | hd::tl -> cat_with_colon (List.fold_left (fun x y -> x ^^ space ^^ y) hd tl) typ
  in
  let binders = List.fold_left fold_fun [] (List.rev pats) in
  map_rev p_collapsed_binder binders

and pats_as_binders_if_possible pats =
  let all_binders p = match p.pat with
  | PatAscribed(pat, (t, None)) ->
    (match pat.pat, t.tm  with
     | PatVar (lid, aqual, attrs), Refine({b = Annotated(lid', t)}, phi)
       when (string_of_id lid) = (string_of_id lid') ->
         Some (p_refinement' aqual attrs (p_ident lid) t phi)
     | PatVar (lid, aqual, attrs), _ ->
       Some (optional p_aqual aqual ^^ p_attributes attrs ^^  p_ident lid, p_tmEqNoRefinement t)
     | _ -> None)
  | _ -> None
  in
  let all_unbound p = match p.pat with
  | PatAscribed _ -> false
  | _ -> true
  in
  match map_if_all all_binders pats with
  | Some bs ->
      collapse_pats bs, Binders (4, 0, true)
  | None ->
      List.map p_atomicPattern pats, Binders (4, 0, false)

and p_quantifier e = match e.tm with
    | QForall _ -> str "forall"
    | QExists _ -> str "exists"
    | _ -> failwith "Imposible : p_quantifier called on a non-quantifier term"

and p_trigger = function
    | [] -> empty
    | pats ->
        group (lbrace ^^ colon ^^ str "pattern" ^/^ jump 2 0 (p_disjunctivePats pats) ^^ rbrace)

and p_disjunctivePats pats =
    separate_map (str "\\/") p_conjunctivePats pats

and p_conjunctivePats pats =
    group (separate_map (semi ^^ break1) p_appTerm pats)

and p_simpleTerm ps pb e = match e.tm with
    | Abs(pats, e) ->
        let comm, doc = p_term_sep false pb e in
        let prefix = str "fun" ^/+^ separate_map break1 p_atomicPattern pats ^/^ rarrow in
        paren_if ps (
          if comm <> empty then
            prefix ^^ hardline ^^ comm ^^ hardline ^^ doc
          else
            group (prefix ^/+^ doc)
        )
    | _ -> p_tmIff e

and p_maybeFocusArrow b =
    if b then str "~>" else rarrow

(* slight modification here : a patternBranch always begins with a `|` *)
(* TODO : can we recover the focusing *)
and p_patternBranch pb (pat, when_opt, e) =
  (* p_patternBranch is always called immediately underneath a paren_if; if ps
   * was true, then we parenthesized and there's a closing parenthesis coming
   * up, meaning we're not at risk of swallowing a semicolon; if ps was false,
   * then we can recursively call p_term with false. *)
  let one_pattern_branch p =
    let branch =
      match when_opt with
      | None -> group (bar ^^ space ^^ (p_tuplePattern p) ^^ space ^^ rarrow)
      | Some f ->
        hang 2 (bar ^^ space ^^ (group ((p_tuplePattern p) ^/^ (str "when"))) ^/^
         (flow break1 [(p_tmFormula f); rarrow]))
    in
    let comm, doc = p_term_sep false pb e in
    // we need to be careful here because an inlined comment on the last branch could eat
    // any following parenthesis; to prevent this, we never inline a comment on the last branch
    if pb then
      if comm = empty then
        group (branch ^/+^ doc)
      else
        group (
          ifflat
            (group (branch ^/+^ doc ^^ break1 ^^ comm))
            (branch ^^ jump2 (inline_comment_or_above comm doc empty))
          )
    else
      if comm <> empty then
        branch ^/+^ (comm ^^ hardline ^^ doc)
      else branch ^/+^ doc
  in
  match pat.pat with
  | PatOr pats ->
    (match List.rev pats with
     | hd::tl ->
       (* group the last pattern with the branch so, if possible, they are kept on the same line in case of the disjunctive
          pattern group being broken *)
       let last_pat_branch = one_pattern_branch hd in
       group (bar ^^ space ^^ (separate_map (break1 ^^ bar ^^ space) p_tuplePattern (List.rev tl)) ^/^ last_pat_branch)
     | [] -> failwith "Impossible: disjunctive pattern can't be empty")
  | _ ->
    one_pattern_branch pat

(* Nothing underneath tmIff is at risk of swallowing a semicolon. *)
and p_tmIff e = match e.tm with
    | Op(id, [e1;e2]) when string_of_id id = "<==>" ->
        infix0 (str "<==>") (p_tmImplies e1) (p_tmIff e2)
    | _ -> p_tmImplies e

and p_tmImplies e = match e.tm with
    | Op(id, [e1;e2]) when string_of_id id = "==>" ->
        infix0 (str "==>") (p_tmArrow (Arrows (2, 2)) false p_tmFormula e1) (p_tmImplies e2)
    | _ -> p_tmArrow (Arrows (2, 2)) false p_tmFormula e

// This function is somewhat convoluted because it is used in a few
// different contexts and it is trying to properly indent for each of
// them. For signatures, it is trying to print the whole arrow on one
// line. If this fails, it tries to print everything except the
// computation type on the same line and push the computation type on a
// new line. If this fails, it prints every term on a separate line. A
// trailing space may sometimes be introduced, which we should trim.
// It also needs to make adjustments depending on which style a signature
// is to be printed in. For more details see the `annotation_style` type
// definition.
and format_sig style terms no_last_op flat_space =
  let terms', last = List.splitAt (List.length terms - 1) terms in
  let n, last_n, terms', sep, last_op =
    match style with
    | Arrows (n, ln)->
        n, ln, terms', space ^^ rarrow ^^ break1, rarrow ^^ space
    | Binders (n, ln, parens) ->
        n, ln,
        (if parens then List.map soft_parens_with_nesting terms' else terms'),
        break1, colon ^^ space
  in
  let last = List.hd last in
  let last_op = if List.length terms > 1 && (not no_last_op) then last_op else empty in
  let one_line_space = if not (last = empty) || not no_last_op then space else empty in
  let single_line_arg_indent = repeat n space in
  let fs = if flat_space then space else empty in
  match List.length terms with
  | 1 -> List.hd terms
  | _ -> group (ifflat (fs ^^ (separate sep terms') ^^ one_line_space ^^ last_op ^^ last)
           (prefix n 1 (group ((ifflat (fs ^^ separate sep terms')
             (jump2 ((single_line_arg_indent ^^ separate (sep ^^ single_line_arg_indent) (List.map (fun x -> align (hang 2 x)) terms')))))))
               (align (hang last_n (last_op ^^ last)))))

and p_tmArrow style flat_space p_Tm e =
  let terms =
    match style with
    | Arrows _ -> p_tmArrow' p_Tm e
    | Binders _ -> collapse_binders p_Tm e
  in
  format_sig style terms false flat_space

and p_tmArrow' p_Tm e =
  match e.tm with
  | Product(bs, tgt) -> (List.map (fun b -> p_binder false b) bs) @ (p_tmArrow' p_Tm tgt)
  | _ -> [p_Tm e]

// When printing in `Binders` style, collapse binders which have the same
// type, so instead of printing
//    val f (a: t) (b: t) (c: t) : Tot nat
// print
//    val f (a b c: t) : Tot nat
// For this, we use the generalised version of p_binder, which returns
// the binder, its type (as an optional) and a function which
// concatenates them.
and collapse_binders (p_Tm: term -> document) (e: term): list<document> =
  let rec accumulate_binders p_Tm e: list<(document * option<document> * catf)> =
    match e.tm with
    | Product(bs, tgt) -> (List.map (fun b -> p_binder' false b) bs) @ (accumulate_binders p_Tm tgt)
    | _ -> [(p_Tm e, None, cat_with_colon)]
  in
  let fold_fun (bs: list<(list<document> * option<document> * catf)>) (x: document * option<document> * catf) =
    let b1, t1, f1 = x in
    match bs with
    | [] -> [([b1], t1, f1)]
    | hd::tl ->
      let b2s, t2, _ = hd in
      match (t1, t2) with
      | (Some typ1, Some typ2) ->
        if typ1 = typ2 then
          (b2s @ [b1], t1, f1) :: tl
        else
          ([b1], t1, f1) :: hd :: tl
      | _ -> ([b1], t1, f1) :: bs
  in
  let p_collapsed_binder (cb: list<document> * option<document> * catf): document =
    let bs, t, f = cb in
    match t with
    | None -> begin
      match bs with
      | [b] -> b
      | _ -> failwith "Impossible" // can't have dangling type or collapse unannotated binders
    end
    | Some typ -> begin
      match bs with
      | [] -> failwith "Impossible" // can't have dangling type
      | [b] -> f b typ
      | hd::tl -> f (List.fold_left (fun x y -> x ^^ space ^^ y) hd tl) typ
    end
  in
  let binders = List.fold_left fold_fun [] (accumulate_binders p_Tm e) in
  map_rev p_collapsed_binder binders

and p_tmFormula e =
    let conj = space ^^ (str "/\\") ^^ break1 in
    let disj = space ^^ (str "\\/") ^^ break1 in
    let formula = p_tmDisjunction e in
    flow_map disj (fun d -> flow_map conj (fun x -> group x) d) formula

and p_tmDisjunction e = match e.tm with
  | Op(id, [e1;e2]) when string_of_id id = "\\/" ->
      (p_tmDisjunction e1) @ [p_tmConjunction e2]
  | _ -> [p_tmConjunction e]

and p_tmConjunction e = match e.tm with
  | Op(id, [e1;e2]) when string_of_id id = "/\\" ->
      (p_tmConjunction e1) @ [p_tmTuple e2]
  | _ -> [p_tmTuple e]

and p_tmTuple e = with_comment p_tmTuple' e e.range

and p_tmTuple' e = match e.tm with
  | Construct (lid, args) when is_tuple_constructor lid && all1_explicit args ->
      separate_map (comma ^^ break1) (fun (e, _) -> p_tmEq e) args
  | _ -> p_tmEq e

and paren_if_gt curr mine doc =
  if mine <= curr then
    doc
  else
    group (lparen ^^ doc ^^ rparen)

and p_tmEqWith p_X e =
  (* TODO : this should be precomputed but F* complains about a potential ML effect *)
  let n = max_level ([colon_equals ; pipe_right] @ operatorInfix0ad12) in
  p_tmEqWith' p_X n e

and p_tmEqWith' p_X curr e = match e.tm with
  (* We don't have any information to print `infix` aplication *)
  | Op (op, [e1; e2]) when (* Implications and iffs are handled specially by the parser *)
                           not (Ident.string_of_id op = "==>"
                                || Ident.string_of_id op = "<==>")
                           && (is_operatorInfix0ad12 op
                               || Ident.string_of_id op = "="
                               || Ident.string_of_id op = "|>") ->
      let op = Ident.string_of_id op in
      let left, mine, right = levels op in
      paren_if_gt curr mine (infix0 (str <| op) (p_tmEqWith' p_X left e1) (p_tmEqWith' p_X right e2))
  | Op(id, [ e1; e2 ]) when string_of_id id = ":=" ->
      group (p_tmEqWith p_X e1 ^^ space ^^ colon ^^ equals ^/+^ p_tmEqWith p_X e2)
  | Op(id, [e]) when string_of_id id = "-" ->
      let left, mine, right = levels "-" in
      minus ^/^ p_tmEqWith' p_X mine e
  | _ -> p_tmNoEqWith p_X e

and p_tmNoEqWith p_X e =
  (* TODO : this should be precomputed but F* complains about a potential ML effect *)
  let n = max_level [colon_colon ; amp ; opinfix3 ; opinfix4] in
  p_tmNoEqWith' false p_X n e

and p_tmNoEqWith' inside_tuple p_X curr e = match e.tm with
  | Construct (lid, [e1, _ ; e2, _]) when lid_equals lid C.cons_lid && not (is_list e) ->
      let op = "::" in
      let left, mine, right = levels op in
      paren_if_gt curr mine (infix0 (str op) (p_tmNoEqWith' false p_X left e1) (p_tmNoEqWith' false p_X right e2))
  | Sum(binders, res) ->
      let op = "&" in
      let left, mine, right = levels op in
      let p_dsumfst bt =
        match bt with
        | Inl b -> p_binder false b ^^ space ^^ str op ^^ break1
        | Inr t -> p_tmNoEqWith' false p_X left t ^^ space ^^ str op ^^ break1
      in
      paren_if_gt curr mine (concat_map p_dsumfst binders ^^ p_tmNoEqWith' false p_X right res)
  | Op(id, [e1; e2]) when string_of_id id = "*" && !unfold_tuples ->
      let op = "*" in
      let left, mine, right = levels op in
      if inside_tuple then
        infix0 (str op) (p_tmNoEqWith' true p_X left e1) (p_tmNoEqWith' true p_X right e2)
      else
        paren_if_gt curr mine (infix0 (str op) (p_tmNoEqWith' true p_X left e1) (p_tmNoEqWith' true p_X right e2))
  | Op (op, [e1; e2]) when is_operatorInfix34 op ->
      let op = Ident.string_of_id op in
      let left, mine, right = levels op in
      paren_if_gt curr mine (infix0 (str op) (p_tmNoEqWith' false p_X left e1) (p_tmNoEqWith' false p_X right e2))
  | Record(with_opt, record_fields) ->
      braces_with_nesting ( default_or_map empty p_with_clause with_opt ^^
                            separate_map_last (semi ^^ break1) p_simpleDef record_fields )
  | Op(id, [e]) when string_of_id id = "~" ->
      group (str "~" ^^ p_atomicTerm e)
  | Paren p when inside_tuple ->
      (match p.tm with
       | Op(id, [e1; e2]) when string_of_id id = "*" ->
           let op = "*" in
           let left, mine, right = levels op in
           paren_if_gt curr mine (infix0 (str op) (p_tmNoEqWith' true p_X left e1) (p_tmNoEqWith' true p_X right e2))
       | _ -> p_X e)
  | _ -> p_X e

and p_tmEqNoRefinement e = p_tmEqWith p_appTerm e

and p_tmEq e = p_tmEqWith p_tmRefinement e

and p_tmNoEq e = p_tmNoEqWith p_tmRefinement e

and p_tmRefinement e = match e.tm with
  | NamedTyp(lid, e) ->
      group (p_lident lid ^/^ colon ^/^ p_appTerm e)
  | Refine(b, phi) ->
      p_refinedBinder b phi
  | _ -> p_appTerm e

and p_with_clause e = p_appTerm e ^^ space ^^ str "with" ^^ break1

and p_refinedBinder b phi =
    match b.b with
    | Annotated (lid, t) -> p_refinement b.aqual b.battributes (p_lident lid) t phi
    | TAnnotated _ -> failwith "Is this still used ?"
    | Variable _
    | TVariable _
    | NoName _ -> failwith (Util.format1 "Imposible : a refined binder ought to be annotated %s" (binder_to_string b))

(* A simple def can be followed by a ';'. Protect except for the last one. *)
and p_simpleDef ps (lid, e) =
  group (p_qlident lid ^/^ equals ^/^ p_noSeqTermAndComment ps false e)

and p_appTerm e = match e.tm with
  | App _ when is_general_application e ->
      let head, args = head_and_args e in
      (match args with
      | [e1; e2] when snd e1 = Infix ->
        p_argTerm e1 ^/^ group (str "`" ^^ (p_indexingTerm head) ^^ str "`") ^/^ p_argTerm e2
      | _ ->
        let head_doc, args =
          if !should_print_fs_typ_app
          then
            let fs_typ_args, args = BU.take (fun (_,aq) -> aq = FsTypApp) args in
            p_indexingTerm head ^^
            soft_surround_map_or_flow 2 0 empty langle (comma ^^ break1) rangle p_fsTypArg fs_typ_args,
            args
          else p_indexingTerm head, args
        in
        group (soft_surround_map_or_flow 2 0 head_doc (head_doc ^^ space) break1 empty p_argTerm args)
      )

  (* (explicit) dependent tuples are handled below *)
  | Construct (lid, args) when is_general_construction e
        && not (is_dtuple_constructor lid && all1_explicit args) ->
    begin match args with
      | [] -> p_quident lid
      | [arg] -> group (p_quident lid ^/^ p_argTerm arg)
      | hd::tl ->
          group (
              group (prefix2 (p_quident lid) (p_argTerm hd)) ^^
                    jump2 (separate_map break1 p_argTerm tl))
    end
  | _ ->
      p_indexingTerm e

and p_argTerm arg_imp = match arg_imp with
  | (u, UnivApp) -> p_universe u
  | (e, FsTypApp) ->
      (* This case should not happen since it might lead to badly formed type applications (e.g t<a><b>)*)
      Errors.log_issue e.range (Errors.Warning_UnexpectedFsTypApp, "Unexpected FsTypApp, output might not be formatted correctly.") ;
      surround 2 1 langle (p_indexingTerm e) rangle
  | (e, Hash) -> str "#" ^^ p_indexingTerm e
  | (e, HashBrace t) -> str "#[" ^^ p_indexingTerm t ^^ str "]" ^^ p_indexingTerm e
  | (e, Infix)
  | (e, Nothing) -> p_indexingTerm e


and p_fsTypArg (e, _) = p_indexingTerm e

and p_indexingTerm_aux exit e = match e.tm with
  | Op(id, [e1 ; e2]) when string_of_id id = ".()" ->
        group (p_indexingTerm_aux p_atomicTermNotQUident e1 ^^ dot ^^
        soft_parens_with_nesting (p_term false false e2))
  | Op(id, [e1; e2]) when string_of_id id = ".[]" ->
        group (p_indexingTerm_aux p_atomicTermNotQUident e1 ^^ dot ^^
        soft_brackets_with_nesting (p_term false false e2))
  | _ ->
      exit e
and p_indexingTerm e = p_indexingTerm_aux p_atomicTerm e

(* p_atomicTermQUident is merged with p_atomicTerm *)
and p_atomicTerm e = match e.tm with
  | LetOpen (lid, e) ->
      (* The second form of let open which is atomic, because it's delimited
       * with parentheses. *)
      p_quident lid ^^ dot ^^ soft_parens_with_nesting (p_term false false e)
  | Name lid ->
      p_quident lid
  | Op(op, [e]) when is_general_prefix_op op ->
      str (Ident.string_of_id op) ^^ p_atomicTerm e
  | _ -> p_atomicTermNotQUident e

and p_atomicTermNotQUident e = match e.tm with
  | Wild -> underscore
  | Var lid when lid_equals lid C.assert_lid -> str "assert"
  | Var lid when lid_equals lid C.assume_lid -> str "assume"
  | Tvar tv -> p_tvar tv
  | Const c ->
    begin match c with
    | Const.Const_char x  when x = '\n' ->
       str "0x0Az"
    | _ -> p_constant c
    end
  | Name lid when lid_equals lid C.true_lid ->
    str "True"
  | Name lid when lid_equals lid C.false_lid ->
    str "False"
  | Op(op, [e]) when is_general_prefix_op op ->
    str (Ident.string_of_id op) ^^ p_atomicTermNotQUident e
  | Op(op, []) ->
    lparen ^^ space ^^ str (Ident.string_of_id op) ^^ space ^^ rparen
  | Construct (lid, args) when is_dtuple_constructor lid && all1_explicit args ->
      surround 2 1 (lparen ^^ bar)
        (separate_map (comma ^^ break1) (fun (e, _) -> p_tmEq e) args)
                   (bar ^^ rparen)
  | Project (e, lid) ->
    group (prefix 2 0 (p_atomicTermNotQUident e)  (dot ^^ p_qlident lid))
  | _ ->
    p_projectionLHS e
  (* BEGIN e END skipped *)

and p_projectionLHS e = match e.tm with
  | Var lid ->
    p_qlident lid
    (* fsType application skipped *)
  | Projector (constr_lid, field_lid) ->
    p_quident constr_lid ^^ qmark ^^ dot ^^ p_lident field_lid
  | Discrim constr_lid ->
    p_quident constr_lid ^^ qmark
  | Paren e ->
    (* Adding required parentheses for tuple disambiguation in ToSyntax.fs --
     * see comment in parse.mly *)
    let comm, t = p_term_sep false false e in
    let doc = soft_parens_with_nesting t in
    if comm = empty then
      doc
    else
      comm ^^ hardline ^^ doc
  | _ when is_array e ->
    let es = extract_from_list e in
    surround 2 0 (lbracket ^^ bar) (separate_map_or_flow_last (semi ^^ break1) (fun ps -> p_noSeqTermAndComment ps false) es) (bar ^^ rbracket)
  | _ when is_list e ->
    surround 2 0 lbracket (separate_map_or_flow_last (semi ^^ break1) (fun ps -> p_noSeqTermAndComment ps false) (extract_from_list e)) rbracket
  | _ when is_ref_set e ->
    let es = extract_from_ref_set e in
    surround 2 0 (bang ^^ lbrace) (separate_map_or_flow (comma ^^ break1) p_appTerm es) rbrace

  (* KM : I still think that it is wrong to print a term that's not parseable... *)
  (* VD: Not parsable, but it can be called with a Labeled term via term_to_string *)
  | Labeled (e, s, b) ->
      str ("(*" ^ s ^ "*)") ^/^ p_term false false e

  (* Failure cases : these cases are not handled in the printing grammar since *)
  (* they are considered as invalid AST. We try to fail as soon as possible in order *)
  (* to prevent the pretty printer from looping *)
  | Op (op, args) when not (handleable_op op args) ->
    failwith ("Operation " ^ Ident.string_of_id op ^ " with " ^ string_of_int (List.length args) ^
              " arguments couldn't be handled by the pretty printer")
  | Uvar id ->
    failwith "Unexpected universe variable out of universe context"

  (* All the cases are explicitly listed below so that a modification of the ast doesn't lead to a loop *)
  (* We must also make sure that all the constructors listed below are handled somewhere *)
  | Wild        (* p_atomicTermNotQUident *)
  | Const _     (* p_atomicTermNotQUident *)
  | Op _        (* All handleable cases should be caught in the recursion loop *)
  | Tvar _      (* p_atomicTermNotQUident *)
  | Var _       (* p_projectionLHS *)
  | Name _      (* p_atomicTerm *)
  | Construct _ (* p_appTerm *)
  | Abs _       (* p_simpleTerm *)
  | App _       (* p_appTerm *)
  | Let _       (* p_noSeqTerm *)
  | LetOpen _   (* p_noSeqTerm *)
  | LetOpenRecord _ (* p_noSeqTerm *)
  | Seq _       (* p_term *)
  | Bind _      (* p_term *)
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
  | Decreases _ (* p_noSeqTerm *)
  | Attributes _(* p_noSeqTerm *)
  | Quote _     (* p_noSeqTerm *)
  | VQuote _    (* p_noSeqTerm *)
  | Antiquote _ (* p_noSeqTerm *)
  | CalcProof _ (* p_noSeqTerm *)
    -> soft_parens_with_nesting (p_term false false e)
  | LexList l -> group (str "%" ^^ p_term_list false false l)
  | WFOrder (rel, e) ->
    p_dec_wf false false rel e

and p_constant = function
  | Const_effect -> str "Effect"
  | Const_unit -> str "()"
  | Const_bool b -> doc_of_bool b
  | Const_real r -> str (r ^"R")
  | Const_float x -> str (Util.string_of_float x)
  | Const_char x -> doc_of_char x
  | Const_string(s, _) -> dquotes (str (FStar.String.escaped s))
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
      let ending = default_or_map empty (fun (s, w) -> signedness s ^^ width w) sign_width_opt in
      str repr ^^ ending
  | Const_range_of -> str "range_of"
  | Const_set_range_of -> str "set_range_of"
  | Const_range r -> str (Range.string_of_range r)
  | Const_reify -> str "reify"
  | Const_reflect lid -> p_quident lid ^^ qmark ^^ dot ^^ str "reflect"

and p_universe u = str "u#" ^^ p_atomicUniverse u

and p_universeFrom u = match u.tm with
  | Op(id, [u1 ; u2]) when string_of_id id = "+" ->
    group (p_universeFrom u1 ^/^ plus ^/^ p_universeFrom u2)
  | App _ ->
    let head, args = head_and_args u in
    begin match head.tm with
      | Var maybe_max_lid when lid_equals maybe_max_lid C.max_lid ->
        group (p_qlident C.max_lid ^/+^
              separate_map space (fun (u,_) -> p_atomicUniverse u) args)
      | _ ->
        (* TODO : refine the failwiths with informations *)
        failwith (Util.format1 ("Invalid term in universe context %s") (term_to_string u))
    end
  | _ -> p_atomicUniverse u

and p_atomicUniverse u = match u.tm with
  | Wild -> underscore
  | Const (Const_int (r, sw)) -> p_constant (Const_int (r, sw))
  | Uvar id -> str (string_of_id id)
  | Paren u -> soft_parens_with_nesting (p_universeFrom u)
  | App _ -> soft_parens_with_nesting (p_universeFrom u)
  | Op(id, [_ ; _]) when string_of_id id = "+" -> soft_parens_with_nesting (p_universeFrom u)
  | _ -> failwith (Util.format1 "Invalid term in universe context %s" (term_to_string u))

let term_to_document e =
  unfold_tuples := false;
  p_term false false e

let signature_to_document e = p_justSig e

let decl_to_document e = p_decl e

let pat_to_document p = p_disjunctivePattern p

let binder_to_document b = p_binder true b

let modul_to_document (m:modul) =
  should_print_fs_typ_app := false ;
  let res =
    match m with
    | Module (_, decls)
    | Interface (_, decls, _) ->
        decls |> List.map decl_to_document |> separate hardline
  in  should_print_fs_typ_app := false ;
  res

let comments_to_document (comments : list<(string * FStar.Range.range)>) =
    separate_map hardline (fun (comment, range) -> str comment) comments

let extract_decl_range (d: decl): decl_meta =
  (* take newline for qualifiers into account *)
  let has_qs =
    match (d.quals, d.d) with
    | ([Assumption], Assume(id, _)) -> false
    | ([], _) -> false
    | _ -> true
  in
  { r = d.drange;
    has_qs = has_qs;
    has_attrs = not (List.isEmpty d.attrs); }

(* [modul_with_comments_to_document m comments] prints the module [m] trying *)
(* to insert the comments from [comments]. The list comments is composed of *)
(* pairs of a raw string and a position which is used to place the comment *)
(* not too far from its original position. The rules for placing comments *)
(* are described in the ``Taking care of comments`` section *)
let modul_with_comments_to_document (m:modul) comments =
  let decls = match m with
    | Module (_, decls)
    | Interface (_, decls, _) -> decls
  in
  should_print_fs_typ_app := false ;
  match decls with
    | [] -> empty, comments
    | d :: ds ->
      (* KM : Hack to fix the inversion that is happening in FStar.Parser.ASTs.as_frag *)
      (* '#light "off"' is supposed to come before 'module ..' but it is swapped there *)
      let decls, first_range =
        match ds with
        | { d = Pragma LightOff } :: _ ->
            let d0 = List.hd ds in
            d0 :: d :: List.tl ds, d0.drange
        | _ -> d :: ds, d.drange
      in
      comment_stack := comments ;
      let initial_comment = place_comments_until_pos 0 1 (start_of_range first_range) dummy_meta empty false true in
  let doc = separate_map_with_comments empty empty p_decl decls extract_decl_range in
  let comments = !comment_stack in
  comment_stack := [] ;
  should_print_fs_typ_app := false ;
  (initial_comment ^^ doc, comments)
