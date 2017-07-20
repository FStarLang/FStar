module StringNormalization

(* Testing string support in the normalizer *)

open FStar.String
open FStar.Char

let _ = assert_norm("a" ^ "b" == "ab")

let _ = assert_norm(string_of_int 123 == "123")

let _ = assert_norm(string_of_bool true == "true")

let _ = assert_norm(string_of_bool false == "false")

let _ = assert_norm("a" ^ string_of_int 123 ^ "b" ^ string_of_bool true == "a123btrue")

let _ = assert_norm (List.Tot.map int_of_char (list_of_string "") == [])

let _ = assert_norm (list_of_string "a8X" == ['a'; '8'; 'X'])

// int_of_char doesn't reduce, so this fails
//let _ = assert_norm (List.Tot.map int_of_char (list_of_string "a8X") == [97; 56; 88])

let _ = assert_norm (string_of_list ['a'; '8'; 'X'] == "a8X")

let _ = assert_norm (concat "." ["FStar";"Mul";"op_Star"] == "FStar.Mul.op_Star")
