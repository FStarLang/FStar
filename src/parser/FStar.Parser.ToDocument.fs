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
(* - Removing the original parens of the ast [should_unparen] *)
(* - Printing the comments [comment_stack] *)






(* [should_print_fs_typ_app] is set when encountering a [LightOff] pragma and *)
(* reset at the end of each module. If you are using individual print function you *)
(* should wrap them in [with_fs_typ_app] *)
let should_print_fs_typ_app = BU.mk_ref false

let with_fs_typ_app b printer t =
  let b0 = !should_print_fs_typ_app in
  should_print_fs_typ_app := b ;
  let res = printer t in
  should_print_fs_typ_app := b0 ;
  res

(* TODO : Unparenthesizing the ast should be put as an option until we get rid of the Paren node *)
let should_unparen = BU.mk_ref true

(* Unparen the ast to check that we are not relying on user inputed parens *)
let rec unparen t =
  if not !should_unparen then t
  else match t.tm with
  | Paren t -> unparen t
  | _ -> t

(* TODO : everything is printed under the assumption of the universe option *)

// abbrev
let str s = doc_of_string s

// lib
let default_or_map n f x =
  match x with
  | None -> n
  | Some x' -> f x'

(* changing PPrint's ^//^ to ^/+^ since '//' wouldn't work in F# *)
let prefix2 prefix_ body = prefix 2 1 prefix_ body

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

let brackets_with_nesting contents =
  surround 2 1 lbracket contents rbracket

let soft_brackets_with_nesting contents =
  soft_surround 2 1 lbracket contents rbracket

let soft_begin_end_with_nesting contents =
  soft_surround 2 1 (str "begin") contents (str "end")

let separate_map_or_flow sep f l =
    if List.length l < 10
    then separate_map sep f l
    else flow_map sep f l

let soft_surround_separate_map n b void_ opening sep closing f xs =
  if xs = []
  then void_
  else soft_surround n b opening (separate_map sep f xs) closing

let doc_of_fsdoc (comment,keywords) =
  group (concat [
    str comment; space;
    separate_map comma (fun (k,v) ->
      concat [str k; rarrow; str v]
    ) keywords
  ])

// Really specific functions to retro-engineer the desugaring
let is_unit e =
    match (unparen e).tm with
        | Const Const_unit -> true
        | _ -> false

let matches_var t x =
    match (unparen t).tm with
        | Var y -> x.idText = text_of_lid y
        | _ -> false

let is_tuple_constructor = C.is_tuple_data_lid'
let is_dtuple_constructor = C.is_dtuple_data_lid'

let is_list_structure cons_lid nil_lid =
  let rec aux e = match (unparen e).tm with
    | Construct (lid, []) -> lid_equals lid nil_lid
    | Construct (lid, [ _ ; e2, _]) -> lid_equals lid cons_lid && aux e2
    | _ -> false
  in aux

let is_list = is_list_structure C.cons_lid C.nil_lid
let is_lex_list = is_list_structure C.lexcons_lid C.lextop_lid

(* [extract_from_list e] assumes that [is_list_structure xxx yyy e] holds *)
(* and returns the list of terms contained in the list *)
let rec extract_from_list e = match (unparen e).tm with
  | Construct (_, []) -> []
  | Construct (_, [e1,Nothing ; e2, Nothing]) -> e1 :: extract_from_list e2
  | _ -> failwith (Util.format1 "Not a list %s" (term_to_string e))

let is_array e = match (unparen e).tm with
    (* TODO check that there is no implicit parameters *)
    | App ({tm=Var lid}, l, Nothing) -> lid_equals lid C.array_mk_array_lid && is_list l
    | _ -> false

let rec is_ref_set e = match (unparen e).tm with
    | Var maybe_empty_lid -> lid_equals maybe_empty_lid C.tset_empty
    | App ({tm=Var maybe_singleton_lid}, {tm=App({tm=Var maybe_ref_lid}, e, Nothing)}, Nothing) ->
        lid_equals maybe_singleton_lid C.tset_singleton && lid_equals maybe_ref_lid C.heap_ref
    | App({tm=App({tm=Var maybe_union_lid}, e1, Nothing)}, e2, Nothing) ->
        lid_equals maybe_union_lid C.tset_union && is_ref_set e1 && is_ref_set e2
    | _ -> false

(* [extract_from_ref_set e] assumes that [is_ref_set e] holds and returns the list of terms contained in the set *)
let rec extract_from_ref_set e = match (unparen e).tm with
  | Var _ -> []
  | App ({tm=Var _}, {tm=App({tm=Var _}, e, Nothing)}, Nothing) -> [e]
  | App({tm = App({tm=Var _}, e1, Nothing)}, e2, Nothing) ->
      extract_from_ref_set e1 @ extract_from_ref_set e2
  | _ -> failwith (Util.format1 "Not a ref set %s" (term_to_string e))

let is_general_application e =
  not (is_array e || is_ref_set e)

let is_general_construction e =
  not (is_list e || is_lex_list e)

let is_general_prefix_op op =
  let op_starting_char =  char_at (Ident.text_of_id op) 0 in
  op_starting_char = '!' || op_starting_char = '?' ||
  (op_starting_char = '~' && Ident.text_of_id op <> "~")

(* might already exist somewhere *)
let head_and_args e =
  let rec aux e acc = match (unparen e).tm with
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

(* Precedence and associativity levels, taken from ../src/parse.mly *)
let opinfix4 = Right, [Inr "**"]
// level backtick won't be used here
let opinfix3 = Left,  [Inl '*' ; Inl '/' ; Inl '%']
let opinfix2 = Left,  [Inl '+' ; Inl '-' ]
let minus_lvl = Left, [Inr "-"] // Sublevel of opinfix2, not a level on its own !!!
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
    | NonAssoc -> l, l, l
  in
  List.mapi (fun i (assoc, tokens) -> (levels_from_associativity i assoc, tokens)) level_associativity_spec

let assign_levels (token_associativity_spec : list<associativity_level>) (s:string) : int * int * int =
    match List.tryFind (matches_level s) level_table with
        | Some (assoc_levels, _) -> assoc_levels
        | _ -> failwith ("Unrecognized operator " ^ s)

let max k1 k2 = if k1 > k2 then k1 else k2

let max_level l =
  let find_level_and_max n level =
    match List.tryFind (fun (_, tokens) -> tokens = snd level) level_table with
      | Some ((_,l,_), _) -> max n l
      | None -> failwith (Util.format1 "Undefined associativity level %s"
                                      (String.concat "," (List.map token_to_string (snd level))))
  in List.fold_left find_level_and_max 0 l

let levels = assign_levels level_associativity_spec

let operatorInfix0ad12 = [opinfix0a ; opinfix0b ; opinfix0c ; opinfix0d ; opinfix1 ; opinfix2 ]

let is_operatorInfix0ad12 =
    fun op -> List.tryFind (matches_level <| Ident.text_of_id op) operatorInfix0ad12 <> None

let is_operatorInfix34 =
    let opinfix34 = [ opinfix3 ; opinfix4 ] in
    fun op -> List.tryFind (matches_level <| Ident.text_of_id op) opinfix34 <> None

let handleable_args_length (op:ident) =
  let op_s = Ident.text_of_id op in
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
  | 1 -> is_general_prefix_op op || List.mem (Ident.text_of_id op) [ "-" ; "~" ]
  | 2 ->
    is_operatorInfix0ad12 op ||
    is_operatorInfix34 op ||
    List.mem (Ident.text_of_id op) ["<==>" ; "==>" ; "\\/" ; "/\\" ; "=" ; "|>" ; ":=" ; ".()" ; ".[]"]
  | 3 -> List.mem (Ident.text_of_id op) [".()<-" ; ".[]<-"]
  | _ -> false

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

let with_comment printer tm tmrange =
  let rec comments_before_pos acc print_pos lookahead_pos =
    match !comment_stack with
    | [] -> acc, false
    | (comment, crange) :: cs ->
      if range_before_pos crange print_pos
      then begin
        comment_stack := cs ;
        comments_before_pos (acc ^^ str comment ^^ hardline) print_pos lookahead_pos
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
  group (comments ^^ printed_e)

(* [place_comments_until_pos k lbegin pos doc] appends to doc all the comments present in *)
(* [comment_stack] whose range is before pos and separate each comments by as much lines *)
(* as indicated by the range information (at least [k]) using [lbegin] as the last line of *)
(* [doc] in the original document. Between 2 comments [k] is set to [1] *)
let rec place_comments_until_pos k lbegin pos_end doc =
  match !comment_stack with
  | (comment, crange) :: cs when range_before_pos crange pos_end ->
    comment_stack := cs ;
    let lnum = max k (line_of_pos (start_of_range crange) - lbegin) in
    let doc = doc ^^ repeat lnum hardline ^^ str comment in
    place_comments_until_pos 1 (line_of_pos (end_of_range crange)) pos_end doc
  | _ ->
    let lnum = max 1 (line_of_pos pos_end - lbegin) in
    doc ^^ repeat lnum hardline

(* [separate_map_with_comments prefix sep f xs extract_range] is the document *)
(*                                                                            *)
(*   prefix (f xs[0]) *)
(*   comments[0] *)
(*   sep (f xs[1]) *)
(*   comments[1] *)
(*   ... *)
(*   sep (f xs[n]) *)
(*                                                                            *)
(* where comments[_] are obtained by successive calls to [place_comments_until_pos] *)
(* using the range informations provided by [extract_range] and the comments in *)
(* [comment_stack]. [xs] must contain at least one element. There is no break *)
(* inserted after [prefix] and [sep]. *)
let separate_map_with_comments prefix sep f xs extract_range =
  let fold_fun (last_line, doc) x =
    let r = extract_range x in
    let doc = place_comments_until_pos 1 last_line (start_of_range r) doc in
    line_of_pos (end_of_range r), doc ^^ sep ^^ f x
  in
  let x, xs = List.hd xs, List.tl xs in
  let init =
    line_of_pos (end_of_range (extract_range x)), prefix ^^ f x
  in
  snd (List.fold_left fold_fun init xs)


(* ****************************************************************************)
(*                                                                            *)
(*                        Printing declarations                               *)
(*                                                                            *)
(* ****************************************************************************)

let rec p_decl d =
    group(
        optional p_fsdoc d.doc ^^ p_attributes d.attrs ^^ p_qualifiers d.quals ^^
        (if d.quals = [] then empty else break1) ^^ p_rawDecl d)

and p_attributes attrs =
  soft_surround_separate_map 0 2 empty
                        (lbracket ^^ str "@") space (rbracket ^^ hardline)
                        p_atomicTerm attrs

and p_fsdoc (doc, kwd_args) =
  let kwd_args_doc =
    match kwd_args with
      | [] -> empty
      | kwd_args ->
        let process_kwd_arg (kwd, arg) =
          str "@" ^^ str kwd ^^ space ^^ str arg
        in
        hardline ^^ separate_map hardline process_kwd_arg kwd_args ^^ hardline
  in
  (* TODO : these newlines should not always be there *)
  hardline ^^ lparen ^^ star ^^ star ^^ str doc ^^ kwd_args_doc ^^ star ^^ rparen ^^ hardline

and p_rawDecl d = match d.d with
  | Open uid ->
    group (str "open" ^/^ p_quident uid)
  | Include uid ->
    group (str "include" ^/^ p_quident uid)
  | ModuleAbbrev (uid1, uid2) ->
    (str "module" ^^ space ^^ p_uident uid1 ^^ space ^^ equals) ^/+^ p_quident uid2
  | TopLevelModule uid ->
    group(str "module" ^^ space ^^ p_quident uid)
  | Tycon(true, [TyconAbbrev(uid, tpars, None, t), None]) ->
    let effect_prefix_doc = str "effect" ^^ space ^^ p_uident uid in
    surround 2 1 effect_prefix_doc (p_typars tpars) equals ^/+^ p_typ t
  | Tycon(false, tcdefs) ->
    (* TODO : needs some range information to be able to use this *)
    (* separate_map_with_comments (str "type" ^^ space) (str "and" ^^ space) p_fsdocTypeDeclPairs tcdefs *)
    precede_break_separate_map (str "type") (str "and") p_fsdocTypeDeclPairs tcdefs
  | TopLevelLet(q, lbs) ->
    let let_doc = str "let" ^^ p_letqualifier q ^^ space in
    separate_map_with_comments let_doc (str "and" ^^ space) p_letbinding lbs
      (fun (p, t) -> Range.union_ranges p.prange t.range)
  | Val(lid, t) ->
    (str "val" ^^ space ^^ p_lident lid ^^ space ^^ colon) ^/+^ p_typ t
    (* KM : not exactly sure which one of the cases below and above is used for 'assume val ..'*)
  | Assume(id, t) ->
    let decl_keyword =
      if char_at id.idText 0 |> is_upper
      then empty
      else str "val" ^^ space
    in
    (decl_keyword ^^ p_ident id ^^ space ^^ colon) ^/+^ p_typ t
  | Exception(uid, t_opt) ->
    str "exception" ^^ space ^^ p_uident uid ^^ optional (fun t -> str "of" ^/+^ p_typ t) t_opt
  | NewEffect(ne) ->
    str "new_effect" ^^ space ^^ p_newEffect ne
  | SubEffect(se) ->
    str "sub_effect" ^^ space ^^ p_subEffect se
  | Pragma p ->
    p_pragma p
  | Fsdoc doc ->
    p_fsdoc doc ^^ hardline (* needed so that the comment is treated as standalone *)
  | Main _ ->
    failwith "*Main declaration* : Is that really still in use ??"
  | Tycon(true, _) ->
    failwith "Effect abbreviation is expected to be defined by an abbreviation"

(* !!! Side-effect !!! : When a [#light "off"] is printed it activates the fs_typ_app *)
and p_pragma = function
  | SetOptions s -> str "#set-options" ^^ space ^^ dquotes (str s)
  | ResetOptions s_opt -> str "#reset-options" ^^ optional (fun s -> space ^^ dquotes (str s)) s_opt
  | LightOff ->
      should_print_fs_typ_app := true ;
      str "#light \"off\""

(* TODO : needs to take the F# specific type instantiation *)
and p_typars bs = p_binders true bs

and p_fsdocTypeDeclPairs (typedecl, fsdoc_opt) =
  optional p_fsdoc fsdoc_opt ^^ p_typeDecl typedecl

and p_typeDecl = function
  | TyconAbstract (lid, bs, typ_opt) ->
    let empty' : unit -> document = fun () -> empty in
    p_typeDeclPrefix lid bs typ_opt empty'
  | TyconAbbrev (lid, bs, typ_opt, t) ->
    let f () = prefix2 equals (p_typ t) in
    p_typeDeclPrefix lid bs typ_opt f
  | TyconRecord (lid, bs, typ_opt, record_field_decls) ->
    let p_recordFieldAndComments (lid, t, doc_opt) =
      with_comment p_recordFieldDecl (lid, t, doc_opt) (extend_to_end_of_line t.range)
    in
    let p_fields () =
        equals ^^ space ^^
        braces_with_nesting (
            separate_map (semi ^^ break1) p_recordFieldAndComments record_field_decls
            )
    in
    p_typeDeclPrefix lid bs typ_opt p_fields
  | TyconVariant (lid, bs, typ_opt, ct_decls) ->
    let p_constructorBranchAndComments (uid, t_opt, doc_opt, use_of) =
        let range = extend_to_end_of_line (dflt uid.idRange (map_opt t_opt (fun t -> t.range))) in
        let p_constructorBranch decl = group (bar ^^ space ^^ p_constructorDecl decl) in
        with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of) range
    in
    (* Beware of side effects with comments printing *)
    let datacon_doc () =
      group (separate_map break1 p_constructorBranchAndComments ct_decls)
    in
    p_typeDeclPrefix lid bs typ_opt (fun () -> prefix2 equals (datacon_doc ()))

and p_typeDeclPrefix lid bs typ_opt cont =
  if bs = [] && typ_opt = None
  then p_ident lid ^^ space ^^ cont ()
  else
      let binders_doc =
        p_typars bs ^^ optional (fun t -> break1 ^^ colon ^^ space ^^ p_typ t) typ_opt
      in surround 2 1 (p_ident lid) binders_doc (cont ())

and p_recordFieldDecl (lid, t, doc_opt) =
  (* TODO : Should we allow tagging individual field with a comment ? *)
  group (optional p_fsdoc doc_opt ^^ p_lident lid ^^ colon ^^ p_typ t)

and p_constructorDecl (uid, t_opt, doc_opt, use_of) =
  let sep = if use_of then str "of" else colon in
  let uid_doc = p_uident uid in
  (* TODO : Should we allow tagging individual constructor with a comment ? *)
  optional p_fsdoc doc_opt ^^ break_ 0 ^^  default_or_map uid_doc (fun t -> (uid_doc ^^ space ^^ sep) ^/+^ p_typ t) t_opt

and p_letbinding (pat, e) =
  (* TODO : this should be refined when head is an applicative pattern (function definition) *)
  let pat_doc =
    let pat, ascr_doc =
      match pat.pat with
      | PatAscribed (pat, t) -> pat, break1 ^^ group (colon ^^ space ^^ p_tmArrow p_tmNoEq t)
      | _ -> pat, empty
    in
    match pat.pat with
    | PatApp ({pat=PatVar (x, _)}, pats) ->
        surround 2 1 (p_lident x)
                      (separate_map break1 p_atomicPattern pats ^^ ascr_doc)
                      equals
    | _ -> group (p_tuplePattern pat ^^ ascr_doc ^/^ equals)
  in
  prefix2 pat_doc (p_term e)

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
    surround 2 1 (p_uident uid) (p_binders true bs) (prefix2 equals (p_simpleTerm t))

and p_effectDefinition uid bs t eff_decls =
  braces_with_nesting (
    group (surround 2 1 (p_uident uid) (p_binders true bs)  (prefix2 colon (p_typ t))) ^/^
    prefix2 (str "with") (separate_break_map semi p_effectDecl eff_decls)
    )

and p_effectDecl d = match d.d with
  | Tycon(false, [TyconAbbrev(lid, [], None, e), None]) ->
      prefix2 (p_lident lid ^^ space ^^ equals) (p_simpleTerm e)
  | _ ->
      failwith (Util.format1 "Not a declaration of an effect member... or at least I hope so : %s"
                              (decl_to_string d))

and p_subEffect lift =
  let lift_op_doc =
    let lifts =
      match lift.lift_op with
        | NonReifiableLift t -> ["lift_wp", t]
        | ReifiableLift (t1, t2) -> ["lif_wp", t1 ; "lift", t2]
        | LiftForFree t -> ["lift", t]
    in
    let p_lift (kwd, t) = prefix2 (str kwd ^^ space ^^ equals) (p_simpleTerm t) in
    separate_break_map semi p_lift lifts
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
  | Abstract -> str "abstract"
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
  group (separate_map break1 p_qualifier qs)

(* Skipping focus since it cannot be recoverred at printing *)

and p_letqualifier = function
  | Rec -> space ^^ str "rec"
  | Mutable -> space ^^ str "mutable"
  | NoLetQualifier -> empty

and p_aqual = function
  | Implicit -> str "#"
  | Equality -> str "$"

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
  | PatAscribed (pat, t) ->
    begin match pat.pat, (unparen t).tm with
    | PatVar (lid, aqual), Refine({b = Annotated(lid', t)}, phi)
      when lid.idText = lid'.idText ->
      soft_parens_with_nesting (p_refinement aqual (p_ident lid) t phi)
    | PatWild, Refine({b = NoName t}, phi) ->
      soft_parens_with_nesting (p_refinement None underscore t phi)
    | _ ->
        soft_parens_with_nesting (p_tuplePattern pat ^^ break_ 0 ^^ colon ^^ p_typ t)
    end
  | PatList pats ->
    surround 2 0 lbracket (separate_break_map semi p_tuplePattern pats) rbracket
  | PatRecord pats ->
    let p_recordFieldPat (lid, pat) = infix2 equals (p_qlident lid) (p_tuplePattern pat) in
    soft_braces_with_nesting (separate_break_map semi p_recordFieldPat pats)
  | PatTuple(pats, true) ->
    surround 2 1 (lparen ^^ bar) (separate_break_map comma p_constructorPattern pats) (bar ^^ rparen)
  | PatTvar (tv, arg_qualifier_opt) ->
    assert (arg_qualifier_opt = None) ;
    p_tvar tv
  | PatOp op ->
    lparen ^^ space ^^ str (Ident.text_of_id op) ^^ space ^^ rparen
  | PatWild ->
    underscore
  | PatConst c ->
    p_constant c
  | PatVar (lid, aqual) ->
    optional p_aqual aqual ^^ p_lident lid
  | PatName uid ->
      p_quident uid
  | PatOr _ -> failwith "Inner or pattern !"
  | PatApp ({pat = PatName _}, _)
  | PatTuple (_, false) ->
      soft_parens_with_nesting (p_tuplePattern p)
  | _ -> failwith (Util.format1 "Invalid pattern %s" (pat_to_string p))

(* Skipping patternOrMultibinder since it would need retro-engineering the flattening of binders *)

(* is_atomic is true if the binder must be parsed atomically *)
(* TODO : try to print refinement with the compact form if possible *)
and p_binder is_atomic b = match b.b with
  | Variable lid -> optional p_aqual b.aqual ^^ p_lident lid
  | TVariable lid -> p_lident lid
  | Annotated (lid, t) ->
      let doc = match (unparen t).tm with
        | Refine ({b = Annotated (lid', t)}, phi) when lid.idText = lid'.idText ->
          p_refinement b.aqual (p_ident lid) t phi
        | _ ->
          optional p_aqual b.aqual ^^ p_lident lid ^^ colon ^^ break_ 0 ^^ p_tmFormula t
      in
      if is_atomic
      then group (lparen ^^ doc ^^ rparen)
      else group doc
  | TAnnotated _ -> failwith "Is this still used ?"
  | NoName t ->
    begin match (unparen t).tm with
      | Refine ({b = NoName t}, phi) ->
        if is_atomic
        then group (lparen ^^ p_refinement b.aqual underscore t phi ^^ rparen)
        else group (p_refinement b.aqual underscore t phi)
      | _ ->
        if is_atomic
        then p_atomicTerm t (* t is a type but it might need some parenthesis *)
        else p_appTerm t (* This choice seems valid (used in p_tmNoEq') *)
    end

and p_refinement aqual_opt binder t phi =
      optional p_aqual aqual_opt ^^ binder ^^ colon ^^
      p_appTerm t ^^ soft_braces_with_nesting (p_noSeqTerm phi)


(* TODO : we may prefer to flow if there are more than 15 binders *)
and p_binders is_atomic bs = separate_map break1 (p_binder is_atomic) bs


(* ****************************************************************************)
(*                                                                            *)
(*                Printing identifiers and module paths                       *)
(*                                                                            *)
(* ****************************************************************************)

(* TODO : should add some defensive checks *)

and p_qlident lid =
  str (text_of_lid lid)

and p_quident lid =
  str (text_of_lid lid)

and p_ident lid =
  str (text_of_id lid)

and p_lident lid =
  str (text_of_id lid)

and p_uident lid =
  str (text_of_id lid)

and p_tvar lid =
  str (text_of_id lid)

and p_lidentOrUnderscore id =
  if starts_with reserved_prefix id.idText
  then underscore
  else p_lident id

(* ****************************************************************************)
(*                                                                            *)
(*                     Printing terms and types                               *)
(*                                                                            *)
(* ****************************************************************************)

and p_term e = match (unparen e).tm with
  | Seq (e1, e2) ->
      group (p_noSeqTerm e1 ^^ semi) ^/^ p_term e2
  | Bind(x, e1, e2) ->
      group ((p_lident x ^^ space ^^ long_left_arrow) ^/+^ (p_noSeqTerm e1 ^^ space ^^ semi)) ^/^ p_term e2
  | _ ->
      group (p_noSeqTerm e)

and p_noSeqTerm e = with_comment p_noSeqTerm' e e.range

and p_noSeqTerm' e = match (unparen e).tm with
  | Ascribed (e, t, None) ->
      group (p_tmIff e ^/^ langle ^^ colon ^/^ p_typ t)
  | Ascribed (e, t, Some tac) ->
      group (p_tmIff e ^/^ langle ^^ colon ^/^ p_typ t ^/^ str "by" ^/^ p_typ tac)
  | Op ({idText = ".()<-"}, [ e1; e2; e3 ]) ->
      group (
        group (p_atomicTermNotQUident e1 ^^ dot ^^ soft_parens_with_nesting (p_term e2)
          ^^ space ^^ larrow) ^^ jump2 (p_noSeqTerm e3))
  | Op ({idText = ".[]<-"}, [ e1; e2; e3 ]) ->
      group (
        group (p_atomicTermNotQUident e1 ^^ dot ^^ soft_brackets_with_nesting (p_term e2)
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
              match (unparen e2).tm with
                  | If (_,_,e3) when is_unit e3 ->
                      soft_parens_with_nesting (p_noSeqTerm e2)
                  | _ -> p_noSeqTerm e2
          in group (
              (str "if" ^/+^ p_noSeqTerm e1) ^/^
              (str "then" ^/+^ e2_doc) ^/^
              (str "else" ^/+^ p_noSeqTerm e3))
  | TryWith(e, branches) ->
      group (prefix2 (str "try") (p_noSeqTerm e) ^/^ str "with" ^/^
            separate_map hardline p_patternBranch branches)
  | Match (e, branches) ->
      group (surround 2 1 (str "match") (p_noSeqTerm e) (str "with") ^/^ separate_map hardline p_patternBranch branches)
  | LetOpen (uid, e) ->
      group (surround 2 1 (str "let open") (p_quident uid) (str "in") ^/^ p_term e)
  | Let(q, lbs, e) ->
    let let_doc = str "let" ^^ p_letqualifier q in
    group (precede_break_separate_map let_doc (str "and") p_letbinding lbs ^/^ str "in") ^/^
      p_term e
  | Abs([{pat=PatVar(x, typ_opt)}], {tm=Match(maybe_x, branches)}) when matches_var maybe_x x ->
    group (str "function" ^/^ separate_map hardline p_patternBranch branches)
  | Assign (id, e) ->
      group (p_lident id ^/^ larrow ^/^ p_noSeqTerm e)
  | _ -> p_typ e

and p_typ e = with_comment p_typ' e e.range

and p_typ' e = match (unparen e).tm with
  | QForall (bs, trigger, e1)
  | QExists (bs, trigger, e1) ->
      prefix2
        (soft_surround 2 0 (p_quantifier e ^^ space) (p_binders true bs) dot)
        (p_trigger trigger ^^ p_noSeqTerm e1)
  | _ -> p_simpleTerm e

and p_quantifier e = match (unparen e).tm with
    | QForall _ -> str "forall"
    | QExists _ -> str "exists"
    | _ -> failwith "Imposible : p_quantifier called on a non-quantifier term"

and p_trigger = function
    | [] -> empty
    | pats ->
        lbrace ^^ colon ^^ str "pattern" ^/^ jump2 (p_disjunctivePats pats) ^/^ rbrace ^^ break1

and p_disjunctivePats pats =
    separate_map (str "\\/") p_conjunctivePats pats

and p_conjunctivePats pats =
    group (separate_map semi p_appTerm pats)

and p_simpleTerm e = match (unparen e).tm with
    | Abs(pats, e) ->
        (str "fun" ^/+^ separate_map break1 p_atomicPattern pats ^/^ rarrow) ^/+^ p_term e
    | _ -> p_tmIff e

and p_maybeFocusArrow b =
    if b then str "~>" else rarrow

(* slight modification here : a patternBranch always begins with a `|` *)
(* TODO : can we recover the focusing *)
and p_patternBranch (pat, when_opt, e) =
  let maybe_paren : document -> document =
    match (unparen e).tm with
    | Match _
    | TryWith _ -> soft_begin_end_with_nesting
    | Abs([{pat=PatVar(x, _)}], {tm=Match(maybe_x, _)}) when matches_var maybe_x x ->
        soft_begin_end_with_nesting
    | _ -> fun x -> x
  in
  group (
      group (bar ^^ space ^^ p_disjunctivePattern pat ^/+^ p_maybeWhen when_opt ^^ rarrow )
      ^/+^ maybe_paren (p_term e))

and p_maybeWhen = function
    | None -> empty
    | Some e -> str "when" ^/+^ p_tmFormula e ^^ space  (*always immediately followed by an arrow*)

and p_tmIff e = match (unparen e).tm with
    | Op({idText = "<==>"}, [e1;e2]) -> infix0 (str "<==>") (p_tmImplies e1) (p_tmIff e2)
    | _ -> p_tmImplies e

and p_tmImplies e = match (unparen e).tm with
    | Op({idText = "==>"}, [e1;e2]) -> infix0 (str "==>") (p_tmArrow p_tmFormula e1) (p_tmImplies e2)
    | _ -> p_tmArrow p_tmFormula e

and p_tmArrow p_Tm e = match (unparen e).tm with
  | Product(bs, tgt) ->
      group (concat_map (fun b -> p_binder false b ^^ space ^^ rarrow ^^ break1) bs ^^ p_tmArrow p_Tm tgt)
  | _ -> p_Tm e

and p_tmFormula e = match (unparen e).tm with
  | Op({idText = "\\/"}, [e1;e2]) ->
      infix0 (str "\\/") (p_tmFormula e1) (p_tmConjunction e2)
  | _ -> p_tmConjunction e

and p_tmConjunction e = match (unparen e).tm with
  | Op({idText = "/\\"}, [e1;e2]) ->
      infix0 (str "/\\") (p_tmConjunction e1) (p_tmTuple e2)
  | _ -> p_tmTuple e

and p_tmTuple e = with_comment p_tmTuple' e e.range

and p_tmTuple' e = match (unparen e).tm with
  | Construct (lid, args) when is_tuple_constructor lid ->
      separate_map (comma ^^ break1) (fun (e, _) -> p_tmEq e) args
  | _ -> p_tmEq e

and paren_if curr mine doc =
  if mine <= curr then
    doc
  else
    group (lparen ^^ doc ^^ rparen)

and p_tmEq e =
  (* TODO : this should be precomputed but F* complains about a potential ML effect *)
  let n = max_level ([colon_equals ; pipe_right] @ operatorInfix0ad12) in
  p_tmEq' n e

and p_tmEq' curr e = match (unparen e).tm with
    (* We don't have any information to print `infix` aplication *)
  | Op (op, [ e1; e2]) when is_operatorInfix0ad12 op || Ident.text_of_id op = "=" || Ident.text_of_id op = "|>" ->
      let op = Ident.text_of_id op in
      let left, mine, right = levels op in
      paren_if curr mine (infix0 (str <| op) (p_tmEq' left e1) (p_tmEq' right e2))
  | Op ({idText = ":="}, [ e1; e2 ]) ->
      group (p_tmEq e1 ^^ space ^^ colon ^^ equals ^/+^ p_tmEq e2)
  | Op({idText = "-"}, [e]) ->
      let left, mine, right = levels "-" in
      minus ^/^ p_tmEq' mine e
  | _ -> p_tmNoEq e

and p_tmNoEq e =
  (* TODO : this should be precomputed but F* complains about a potential ML effect *)
  let n = max_level [colon_colon ; amp ; opinfix3 ; opinfix4] in
  p_tmNoEq' n e

and p_tmNoEq' curr e = match (unparen e).tm with
  | Construct (lid, [e1, _ ; e2, _]) when lid_equals lid C.cons_lid && not (is_list e) ->
      let op = "::" in
      let left, mine, right = levels op in
      paren_if curr mine (infix0 (str op) (p_tmNoEq' left e1) (p_tmNoEq' right e2))
  | Sum(binders, res) ->
      let op = "&" in
      let left, mine, right = levels op in
      let p_dsumfst b = p_binder false b ^^ space ^^ str op ^^ break1 in
      paren_if curr mine (concat_map p_dsumfst binders ^^ p_tmNoEq' right res)
  | Op (op, [ e1; e2]) when is_operatorInfix34 op ->
      let op = Ident.text_of_id op in
      let left, mine, right = levels op in
      paren_if curr mine (infix0 (str op) (p_tmNoEq' left e1) (p_tmNoEq' right e2))
  | NamedTyp(lid, e) ->
      group (p_lidentOrUnderscore lid ^/^ colon ^/^ p_appTerm e)
  | Refine(b, phi) ->
      p_refinedBinder b phi
  | Record(with_opt, record_fields) ->
      braces_with_nesting ( default_or_map empty p_with_clause with_opt ^^
                            separate_map (semi ^^ break1) p_simpleDef record_fields )
  | Op({idText = "~"}, [e]) ->
      group (str "~" ^^ p_atomicTerm e)
  | _ -> p_appTerm e

and p_with_clause e = p_appTerm e ^^ space ^^ str "with" ^^ break1

and p_refinedBinder b phi =
    match b.b with
    | Annotated (lid, t) ->
        soft_parens_with_nesting (p_refinement b.aqual (p_lident lid) t phi)
    | TAnnotated _ -> failwith "Is this still used ?"
    | Variable _
    | TVariable _
    | NoName _ -> failwith (Util.format1 "Imposible : a refined binder ought to be annotated %s" (binder_to_string b))

(* A simple def can be followed by a ';' *)
and p_simpleDef (lid, e) =
  group (p_qlident lid ^/^ equals ^/^ p_tmIff e)

and p_appTerm e = match (unparen e).tm with
  | App _ when is_general_application e ->
      let head, args = head_and_args e in
      let head_doc, args =
        if !should_print_fs_typ_app
        then
          let fs_typ_args, args = BU.take (fun (_,aq) -> aq = FsTypApp) args in
          p_indexingTerm head ^^
          soft_surround_separate_map 2 0 empty langle (comma ^^ break1) rangle p_fsTypArg fs_typ_args,
          args
        else p_indexingTerm head, args
      in
      group (soft_surround_separate_map 2 0 head_doc (head_doc ^^ space) break1 empty p_argTerm args)

  (* dependent tuples are handled below *)
  | Construct (lid, args) when is_general_construction e && not (is_dtuple_constructor lid) ->
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
  | ({tm=Uvar _}, UnivApp) -> p_univar (fst arg_imp)
  | (u, UnivApp) -> p_universe u
  | (e, FsTypApp) ->
      (* This case should not happen since it might lead to badly formed type applications (e.g t<a><b>)*)
      BU.print_warning "Unexpected FsTypApp, output might not be formatted correctly.\n" ;
      surround 2 1 langle (p_indexingTerm e) rangle
  | (e, Hash) -> str "#" ^^ p_indexingTerm e
  | (e, Nothing) -> p_indexingTerm e

and p_fsTypArg (e, _) = p_indexingTerm e

and p_indexingTerm_aux exit e = match (unparen e).tm with
  | Op({idText = ".()"}, [e1 ; e2]) ->
        group (p_indexingTerm_aux p_atomicTermNotQUident e1 ^^ dot ^^ soft_parens_with_nesting (p_term e2))
  | Op({idText = ".[]"}, [e1; e2]) ->
        group (p_indexingTerm_aux p_atomicTermNotQUident e1 ^^ dot ^^ soft_brackets_with_nesting (p_term e2))
  | _ ->
      exit e
and p_indexingTerm e = p_indexingTerm_aux p_atomicTerm e

(* p_atomicTermQUident is merged with p_atomicTerm *)
and p_atomicTerm e = match (unparen e).tm with
  (* already handled higher in the hierarchy *)
  | LetOpen (lid, e) ->
      p_quident lid ^^ dot ^^ soft_parens_with_nesting (p_term e)
  | Name lid ->
      p_quident lid
  | Op(op, [e]) when is_general_prefix_op op ->
      str (Ident.text_of_id op) ^^ p_atomicTerm e
  | _ -> p_atomicTermNotQUident e

and p_atomicTermNotQUident e = match (unparen e).tm with
  | Wild -> underscore
  | Var lid when lid_equals lid C.assert_lid ->
    str "assert"
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
    str (Ident.text_of_id op) ^^ p_atomicTermNotQUident e
  | Op(op, []) ->
    lparen ^^ space ^^ str (Ident.text_of_id op) ^^ space ^^ rparen
  | Construct (lid, args) when is_dtuple_constructor lid ->
    surround 2 1 (lparen ^^ bar) (separate_map (comma ^^ break1) p_tmEq (List.map fst args)) (bar ^^ rparen)
  | Project (e, lid) ->
    group (prefix 2 0 (p_atomicTermNotQUident e)  (dot ^^ p_qlident lid))
  | _ ->
    p_projectionLHS e
  (* BEGIN e END skipped *)

and p_projectionLHS e = match (unparen e).tm with
  | Var lid ->
    p_qlident lid
    (* fsType application skipped *)
  | Projector (constr_lid, field_lid) ->
    p_quident constr_lid ^^ qmark ^^ dot ^^ p_lident field_lid
  | Discrim constr_lid ->
    p_quident constr_lid ^^ qmark
  (* TODO : We should drop this constructor asa this printer works *)
  | Paren e ->
    soft_parens_with_nesting (p_term e)
  | _ when is_array e ->
    let es = extract_from_list e in
    surround 2 0 (lbracket ^^ bar) (separate_map_or_flow (semi ^^ break1) p_noSeqTerm es) (bar ^^ rbracket)
  | _ when is_list e ->
    surround 2 0 lbracket (separate_map_or_flow (semi ^^ break1) p_noSeqTerm (extract_from_list e)) rbracket
  | _ when is_lex_list e ->
    surround 2 1 (percent ^^ lbracket) (separate_map_or_flow (semi ^^ break1) p_noSeqTerm (extract_from_list e)) rbracket
  | _ when is_ref_set e ->
    let es = extract_from_ref_set e in
    surround 2 0 (bang ^^ lbrace) (separate_map_or_flow (comma ^^ break1) p_appTerm es) rbrace

  (* KM : I still think that it is wrong to print a term that's not parseable... *)
  | Labeled (e, s, b) ->
      break_ 0 ^^ str ("(*" ^ s ^ "*)") ^/^ p_term e

  (* Failure cases : these cases are not handled in the printing grammar since *)
  (* they are considered as invalid AST. We try to fail as soon as possible in order *)
  (* to prevent the pretty printer from looping *)
  | Op (op, args) when not (handleable_op op args) ->
    failwith ("Operation " ^ Ident.text_of_id op ^ " with " ^ string_of_int (List.length args) ^
              " arguments couldn't be handled by the pretty printer")
  | Uvar _ -> failwith "Unexpected universe variable out of universe context"

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
  | Assign _    (* p_noSeqTerm *)
  | Attributes _(* p_noSeqTerm *)
    -> soft_parens_with_nesting (p_term e)

and p_constant = function
  | Const_effect -> str "Effect"
  | Const_unit -> str "()"
  | Const_bool b -> doc_of_bool b
  | Const_float x -> str (Util.string_of_float x)
  | Const_char x -> squotes (doc_of_char x )
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
      let ending = default_or_map empty (fun (s, w) -> signedness s ^^ width w) sign_width_opt in
      str repr ^^ ending
  | Const_range r -> str (Range.string_of_range r)
  | Const_reify -> str "reify"
  | Const_reflect lid -> p_quident lid ^^ qmark ^^ dot ^^ str "reflect"

and p_universe u = str "u#" ^^ p_atomicUniverse u

and p_universeFrom u = match (unparen u).tm with
  | Op({idText = "+"}, [u1 ; u2]) ->
    group (p_universeFrom u1 ^/^ plus ^/^ p_universeFrom u2)
  | App _ ->
    let head, args = head_and_args u in
    begin match (unparen head).tm with
      | Var maybe_max_lid when lid_equals maybe_max_lid C.max_lid ->
        group (p_qlident C.max_lid ^/+^
              separate_map space (fun (u,_) -> p_atomicUniverse u) args)
      | _ ->
        (* TODO : refine the failwiths with informations *)
        failwith (Util.format1 ("Invalid term in universe context %s") (term_to_string u))
    end
  | _ -> p_atomicUniverse u

and p_atomicUniverse u = match (unparen u).tm with
    | Wild -> underscore
    | Const (Const_int (r, sw)) -> p_constant (Const_int (r, sw))
    | Uvar _ -> p_univar u
    | Paren u -> soft_parens_with_nesting (p_universeFrom u)
    | Op({idText = "+"}, [_ ; _])
    | App _ -> soft_parens_with_nesting (p_universeFrom u)
      | _ -> failwith (Util.format1 "Invalid term in universe context %s" (term_to_string u))

    and p_univar u = match (unparen u).tm with
        | Uvar id -> str (text_of_id id)
        | _ -> failwith (Util.format1 "Not a universe variable %s" (term_to_string u))


    let term_to_document e = p_term e

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
          (* TODO : take into account the space of the fsdoc (and attributes ?) *)
          let extract_decl_range d = d.drange in
          comment_stack := comments ;
          let initial_comment = place_comments_until_pos 0 1 (start_of_range first_range) empty in
      let doc = separate_map_with_comments empty empty decl_to_document decls extract_decl_range in
      let comments = !comment_stack in
      comment_stack := [] ;
      should_print_fs_typ_app := false ;
      (initial_comment ^^ doc, comments)


