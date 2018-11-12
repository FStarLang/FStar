module Test.Printf

open FStar.Printf

let test_sprintf () = sprintf "%d: Hello %s, sprintf %s %ul" 0 "#fstar-hackery" "works!" 0ul

type something =
  | This
  | That

let something_to_string =
  function
    | This -> "this"
    | That -> "that"

let parse_something : extension_parser =
  function
    | 'S' :: rest -> Some (MkExtension something_to_string, rest)
    | _ -> None

inline_for_extraction
let my_sprintf = ext_sprintf parse_something

let test_ext () = my_sprintf "%d: Hello %s, sprintf %s %ul, with %XS or %XS extensions"
                  0 "#fstar-hackery" "works!" 0ul This That
