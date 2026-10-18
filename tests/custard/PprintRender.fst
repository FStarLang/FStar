module PprintRender

(* FStar.Pprint is PPrint itself on OCaml and a port of it on Cherry
   (FStar.Pprint-c.cherry.fst); one .out.expected holds both to the same
   layouts. *)

open FStar.All
open FStar.IO
open FStar.Pprint
module F = FStar.Float64

let show (title:string) (width:int) (d:document) : ML unit =
  print_string ("== " ^ title ^ " @" ^ string_of_int width ^ "\n");
  print_string (pretty_string F.one width d);
  print_string "|\n"

let call (f:string) (args:list document) : document =
  group (doc_of_string f ^^ nest 2 (parens (separate (comma ^^ break_ 1) args)))

let words_doc : document =
  flow (break_ 1) (words "  the quick brown fox\tjumps over\nthe lazy dog  ")

let block : document =
  surround 2 1 lbrace
    (separate_map (semi ^^ break_ 1)
      (fun (i:int) -> infix 2 1 equals (doc_of_string ("field" ^ string_of_int i))
                                       (call "f" [doc_of_string "x"; doc_of_string "y"]))
      [1; 2; 3])
    rbrace

let mixed : document =
  group (doc_of_string "let x =" ^^ nest 4 (hardline ^^ doc_of_string "1"))
  ^^ hardline ^^ doc_of_string "trailing" ^^ blank 3 ^^ hardline
  ^^ hang 2 (separate2 (comma ^^ space) (doc_of_string " and ")
                (List.Tot.map doc_of_string ["a"; "b"; "c"]))
  ^^ blank 2

let chars : document =
  separate_map space doc_of_char
    ['a'; '\''; '\\'; '\n'; '\t'; '\r'; FStar.Char.char_of_u32 8ul;
     FStar.Char.char_of_u32 0ul; FStar.Char.char_of_u32 127ul; FStar.Char.char_of_u32 233ul; '~']

let main () : ML unit =
  show "call" 80 (call "function_name" [doc_of_string "argument1"; doc_of_string "argument2"]);
  show "call" 20 (call "function_name" [doc_of_string "argument1"; doc_of_string "argument2"]);
  show "words" 14 words_doc;
  show "block" 80 block;
  show "block" 30 block;
  show "block" 12 block;
  show "soft" 18 (soft_surround 2 1 lbracket
                   (separate (semi ^^ break_ 1) (lines "alpha\nbeta\ngamma\ndelta")) rbracket);
  show "url" 16 (url "https://github.com/FStarLang/FStar/pulls");
  show "mixed" 80 mixed;
  show "chars" 80 chars;
  show "split" 80 (separate bar (split (fun c -> c = ',') "a,,bc,"));
  show "prefix" 10 (prefix 4 1 (doc_of_string "header:") (arbitrary_string "one two\nthree"));
  show "jump" 6 (jump 3 2 (doc_of_string "body") ^^ ifflat (doc_of_string "F") (doc_of_string "B"));
  show "align" 30 (doc_of_string "xs = " ^^ align (separate hardline (words "p q r")));
  show "repeat" 80 (repeat 3 (twice (doc_of_bool true)) ^^ concat [star; minus; underscore]);
  show "opt" 80 (optional doc_of_string (Some "some") ^^ optional doc_of_string None
                 ^^ concat_map doc_of_string ["x"; "y"]
                 ^^ surround_separate 2 0 (doc_of_string "[]") lbracket comma rbracket []
                 ^^ surround_separate_map 2 0 empty lparen comma rparen doc_of_string ["u"; "v"]);
  show "fancy" 6 (group (fancystring "<b>bold</b>" 4 ^/^ substring "abcdef" 1 3
                         ^/^ fancysubstring "abcdef" 2 3 1 ^/^ utf8string "z"));
  (* A ribbon of half the width: the group fits the width but not the ribbon. *)
  print_string (pretty_string (F.of_literal "0.5") 20
                  (nest 4 (doc_of_string "abcd" ^^ hardline
                           ^^ group (doc_of_string "123456" ^/^ doc_of_string "7890"))));
  print_string "|\n";
  print_string (render (flow_map (break_ 1) doc_of_string
                          ["render"; "uses"; "width"; "eighty"; "and"; "a"; "full"; "ribbon";
                           "so"; "this"; "sentence"; "has"; "to"; "wrap"; "somewhere"; "near";
                           "the"; "end"; "of"; "the"; "line"]));
  print_string "|\n"
