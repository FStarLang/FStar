module Part3.Typeclasses
module TC = FStar.Tactics.Typeclasses

class printable (a:Type) =
{
  to_string : a -> string
}

instance printable_bool : printable bool =
{
  to_string = Prims.string_of_bool
}

instance printable_int : printable int =
{
  to_string = Prims.string_of_int
}

let printb (x:bool) = to_string x
let printi (x:int) = to_string x

instance printable_list (#a:Type) (x:printable a) : printable (list a) =
{
  to_string = (fun l -> "[" ^ FStar.String.concat "; " (List.Tot.map to_string l) ^ "]")
}

let printis (l:list int) = to_string l
let printbs (l:list bool) = to_string l

let print_any_list_explicit #a ( _ : printable a ) (l:list a) = to_string l
let _ = print_any_list_explicit printable_int [1;2;3]

let print_any_list #a {| _ : printable a |} (l:list a) = to_string l
let _ex1 = print_any_list [[1;2;3]]
let _ex2 = print_any_list #_ #(printable_list printable_int) [[1;2;3]]

let print_any_list_alt #a {| printable a |} (l:list a) = to_string l

//Define instances to make this work
[@@expect_failure]
let _ = to_string [Inl (0, 1); Inr (Inl (Some true)); Inr (Inr "hello") ]

