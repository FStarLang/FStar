module CherryClosureBorrow

(* A function used as a closure, whose tail calls reach no closure call,
   still borrows its parameters: only the closure's entry point takes them
   owned. *)

open FStar.All

let same (a b:list int) : ML bool = a = b

let count_same (x:list int) (ls:list (list int)) : ML int =
  List.length (List.filter (same x) ls)

let main () : ML unit =
  let x = [1; 2] in
  let ls = [[1; 2]; [3]; [1; 2]] in
  FStar.IO.print_string (string_of_int (count_same x ls) ^ " " ^
                         string_of_bool (same x [1; 2]) ^ "\n")
