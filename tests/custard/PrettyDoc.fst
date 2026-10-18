module PrettyDoc

(* FStar.Pprint: on OCaml the PPrint library, on Cherry the F* implementation
   in ulib/FStar.Pprint-c.cherry.fst.  Both must render the same text.  Each
   line of output ends in '|', so that trailing blanks show. *)

open FStar.All
open FStar.Pprint
module F64 = FStar.Float64

let s (x:string) : document = doc_of_string x

let rec show_lines (out:string) (start:nat) (i:nat{start <= i /\ i <= String.length out}) : ML unit =
  if i >= String.length out then begin
    FStar.IO.print_string (String.sub out start (String.length out - start));
    FStar.IO.print_string "|\n"
  end else if String.index out i = '\n' then begin
    FStar.IO.print_string (String.sub out start (i - start));
    FStar.IO.print_string "|\n";
    show_lines out (i + 1) (i + 1)
  end else show_lines out start (i + 1)

let show_r (name:string) (r:F64.float64) (w:int) (d:document) : ML unit =
  FStar.IO.print_string ("== " ^ name ^ " w=" ^ string_of_int w ^ "\n");
  show_lines (pretty_string r w d) 0 0

let show (name:string) (w:int) (d:document) : ML unit = show_r name F64.one w d

let half = F64.of_literal "0.5"
let quarter = F64.of_literal "0.25"

let main () : ML unit =
  let g = group (s "aaa" ^/^ s "bbb") in
  show "fits" 7 g;
  show "breaks" 6 g;
  show "no-lookahead" 8 (g ^^ s "cccccc");
  show "nest" 3 (group (nest 2 (s "a" ^/^ group (s "b" ^/^ s "c"))));
  show "hardline-in-group" 80 (group (s "a" ^^ hardline ^^ s "b" ^/^ s "c"));
  show "no-trailing-blanks" 80
    (nest 2 (s "a" ^^ blank 3 ^^ hardline ^^ hardline ^^ blank 1 ^^ s "b" ^^ break_ 1));
  show "align" 80 (s "abc" ^^ align (s "x" ^^ hardline ^^ s "y"));
  show "hang" 10 (s "ab" ^^ hang 2 (s "c" ^/^ s "dddddddd" ^/^ s "e"));
  show "ifflat" 8 (group (ifflat (s "flat") (s "broken") ^^ s "1234"));
  show "ifflat" 7 (group (ifflat (s "flat") (s "broken") ^^ s "1234"));
  show_r "ribbon-fits" half 20 (nest 4 (s "x" ^^ hardline ^^ group (s "aaaa" ^/^ s "bbbbb")));
  show_r "ribbon-breaks" (F64.of_literal "0.45") 20
    (nest 4 (s "x" ^^ hardline ^^ group (s "aaaa" ^/^ s "bbbbb")));
  show_r "ribbon-line-start" quarter 40
    (nest 4 (s "x" ^^ hardline ^^ s "zzz" ^^ nest 6 (group (s "aaaa" ^/^ s "bbb"))));
  show "text" 80 (doc_of_char 'a' ^^ doc_of_char '\n' ^^ doc_of_char '\\' ^^ space ^^
                  doc_of_bool true ^^ space ^^ substring "hello world" 6 5 ^^ space ^^
                  fancysubstring "xxhelloxx" 2 5 3 ^^ space ^^ rarrow ^^ larrow ^^
                  long_left_arrow);
  show "utf8" 6 (group (utf8string "\u00e9\u00e9\u00e9" ^/^ s "x"));
  show "bytes" 6 (group (s "\u00e9\u00e9\u00e9" ^/^ s "x"));
  show "fancy" 8 (group (fancystring "<b>ab</b>" 2 ^/^ s "cdef"));
  show "enclose" 80 (squotes (s "a") ^^ dquotes (s "b") ^^ bquotes (s "c") ^^
                     braces (s "d") ^^ parens (s "e") ^^ angles (s "f") ^^
                     brackets (s "g") ^^ enclose bar bar (s "h") ^^
                     precede at (s "i") ^^ terminate semi (s "j"));
  show "repeat" 80 (repeat 3 (s "ab") ^^ repeat 0 (s "x") ^^ twice bang ^^
                    optional s None ^^ optional s (Some "o"));
  show "separate" 80 (separate (comma ^^ space) [s "a"; s "b"; s "c"] ^^ space ^^
                      separate2 (s ", ") (s " and ") [s "a"; s "b"; s "c"] ^^ space ^^
                      concat_map s ["x"; "y"] ^^ space ^^
                      separate_map comma s ["p"; "q"] ^^ separate comma []);
  show "lines" 80 (separate (s "<>") (lines "ab\ncd\n\nef\n"));
  show "words" 80 (separate (s "<>") (words "  ab \t cd\nef\r gh  "));
  show "split" 80 (separate (s "<>") (split (fun c -> c = ',' || c = ';') ",a,,b;c,"));
  show "arbitrary_string" 5 (arbitrary_string "ab\ncd\nef");
  show "arbitrary_string" 80 (group (arbitrary_string "ab\ncd\nef"));
  let ws = words "the quick brown fox jumps over the lazy dog again and again" in
  show "flow" 15 (nest 2 (flow (break_ 1) ws));
  show "flow_map" 15 (flow_map (comma ^^ break_ 1) s ["one"; "two"; "three"; "four"; "five"]);
  show "url" 10 (url "http://www.example.com/a/b.html");
  show "prefix" 10 (prefix 2 1 (s "left") (s "right"));
  show "prefix" 8 (prefix 2 1 (s "a" ^/^ s "b") (s "cccccccc"));
  show "jump" 4 (s "x" ^^ jump 2 1 (s "right"));
  show "infix" 20 (infix 2 2 equals (s "left") (s "right"));
  show "infix" 8 (infix 2 1 equals (s "a" ^/^ s "b") (s "cccccccc"));
  show "surround" 10 (surround 2 1 lbrace (s "a;" ^/^ s "bbbbb") rbrace);
  show "surround" 20 (surround 2 1 lbrace (s "a;" ^/^ s "bbbbb") rbrace);
  show "soft_surround" 12 (soft_surround 2 1 lbrace (s "a;" ^/^ s "bbbbb" ^/^ s "cc") rbrace);
  show "soft_surround" 3 (soft_surround 2 1 lbrace (s "aaaaa") rbrace);
  show "surround_separate" 80
    (surround_separate 2 0 (s "VOID") lbracket (semi ^^ space) rbracket [] ^^ space ^^
     surround_separate_map 2 1 (s "NONE") lbrace comma rbrace s ["x"; "y"]);
  show "surround_separate" 6
    (surround_separate 2 1 (s "VOID") lbracket (semi ^^ break_ 1) rbracket [s "a"; s "b"; s "c"]);
  show "width-0" 0 (group (s "a" ^/^ s "b") ^^ group empty);
  FStar.IO.print_string (render (group (separate_map (comma ^^ break_ 1) s ["render"; "is"; "width"; "80"])));
  FStar.IO.print_string "\n"
