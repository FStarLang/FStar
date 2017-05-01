module StringNormalization

(* Testing string support in the normalizer *)

let _ = assert_norm("a" ^ "b" == "ab")

let _ = assert_norm(string_of_int 123 == "123")

let _ = assert_norm(string_of_bool true == "true")

let _ = assert_norm(string_of_bool false == "false")

let _ = assert_norm("a" ^ string_of_int 123 ^ "b" ^ string_of_bool true == "a123btrue")
