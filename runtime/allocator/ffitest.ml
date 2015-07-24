external inspect : 'a -> unit = "inspect";;

external push_frame : int -> unit = "stack_push_frame";;
external pop_frame : unit -> unit = "stack_pop_frame";;

external stack_mkpair : 'a -> 'b -> 'a*'b = "stack_mkpair";;
external stack_mktuple3 : 'a -> 'b -> 'c -> 'a*'b*'c = "stack_mktuple3";;
external stack_mktuple4 : 'a -> 'b -> 'c -> 'd -> 'a*'b*'c*'d = "stack_mktuple4";;

external stack_cons: 'a -> 'a list -> 'a list = "stack_mkpair";;

(*
external stack_string_init: int -> (int -> char) -> string = "stack_init_string";;
*)

push_frame 0;;

let rec mklist n =
  if n = 0 then []
  else
    let l = mklist (n-1) in
    stack_cons n l

let rec string_of_list l p =
  match l with
      [] -> "[]"
    | h::t -> 
      let s = string_of_list t p in 
      (p h)^"::"^s
;;

Printf.printf "List result = %s\n" (string_of_list (mklist 10) string_of_int);;

(*
type mytype =
    A 
  | B of int
  | C
  | D of string
;;

inspect A;;
inspect (B 1);;
inspect C;;
inspect (D "hello");;
*)
pop_frame ();;


(*
push_frame 0;;

external make_string: unit -> string = "make_string";;

let foo x = stack_mkpair x x

let ptuple (x,y) =   Printf.printf "(%d,%d)\n" x y
;;
let ptupletuple (x,y) = ptuple x; ptuple y
;;
let x = foo 0;;
let y = foo 1;;
ptuple x;;
ptuple y;;
let w = foo x;;
ptupletuple w;;
(*
let w = foo (1,2);; (* will fail, since (1,2) is a pointer to the OCaml heap *)
*)

let s = make_string ();;
Printf.printf "The string is |%s|\n" s;;

let rec fib x =
  if x = 0 then (0,1)
  else
    let (y,z) = fib (x-1) in
    (z,y+z)
;;
ptuple (fib 100);;

(* pop_frame ();;  *)

Gc.full_major();;
Gc.compact();;
Gc.print_stat (Pervasives.stdout);;

let z = foo 2;;

Printf.printf "The string is |%s|\n" s;;

ptuple x;;
ptuple y;;
ptuple z;;

inspect 1;;
inspect (1,2);;
inspect [];;
inspect [1;2];;
*)
