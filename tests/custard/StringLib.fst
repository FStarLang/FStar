module StringLib

(* FStar.String: on OCaml Batteries' UTF-8 functions, on Cherry the F*
   implementation in ulib/FStar.String-c.cherry.fst.  Both must agree. *)

open FStar.All
open FStar.String
module L = FStar.List.Tot

let pr (s:string) : ML unit = FStar.IO.print_string s; FStar.IO.print_string "\n"

let ints (l:list char) : string =
  concat "," (L.map (fun c -> string_of_int (FStar.Char.int_of_char c)) l)

let strs (l:list string) : string = "[" ^ concat "|" l ^ "]"

let sign (n:int) : string = if n < 0 then "-" else if n = 0 then "0" else "+"

let s = "héllo €😀!"

let main () : ML unit =
  assert_norm (length s = 9);
  pr (ints (list_of_string s));
  pr (ints (list_of_string ""));
  pr (string_of_list ['a'; 'é'; '€'; '😀']);
  pr (string_of_list []);
  pr (string_of_int (length s) ^ " " ^ string_of_int (strlen s) ^ " " ^ string_of_int (length ""));
  pr (make 3 '€' ^ "/" ^ make 0 'x' ^ "/" ^ string_of_char 'é');
  pr (strs (split [','] "a,b,,c,"));
  pr (strs (split [','; ';'] "a;b,c;;d"));
  pr (strs (split ['€'] "x€y€€z"));
  pr (strs (split [','] ""));
  pr (strs (split [] "abc"));
  pr (concat ", " ["a"; "b"; "c"] ^ "/" ^ concat ", " [] ^ "/" ^ concat "-" ["x"]);
  pr (sign (compare "abc" "abd") ^ sign (compare "b" "abc") ^ sign (compare "" "")
      ^ sign (compare "ab" "abc") ^ sign (compare "é" "z"));
  pr (lowercase "AbC É" ^ "/" ^ uppercase "aBc é");
  pr (string_of_int (FStar.Char.int_of_char (index s 1)) ^ " "
      ^ string_of_int (FStar.Char.int_of_char (index s 7)));
  pr (string_of_int (index_of s '€') ^ " " ^ string_of_int (index_of s 'l')
      ^ " " ^ string_of_int (index_of s 'z') ^ " " ^ string_of_int (index_of "" 'a'));
  pr (sub s 1 4 ^ "/" ^ sub s 6 2 ^ "/" ^ sub s 3 0);
  pr (collect (fun c -> if c = 'l' then "L" else if c = '€' then "EUR" else string_of_char c) s);
  pr (collect (fun c -> "x") "");
  pr (substring s 6 3 ^ "/" ^ string_of_int (FStar.Char.int_of_char (get s 6)));
  pr (try substring s 7 5 with _ -> "substring out of bounds");
  pr (try string_of_int (FStar.Char.int_of_char (get s (-1))) with _ -> "get out of bounds")
