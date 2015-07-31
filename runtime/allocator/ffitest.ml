open Camlstack;;

(* DEBUG *)
(*
type recd = { mutable field1: int; mutable field2: int };;

inspect ((1,ref 1));;
inspect ({ field1 = 1; field2 = 2 });;
*)

let doGC() =
  print_mask ();
  Gc.full_major()
  (* Gc.print_stat (Pervasives.stdout) *)
;;

(* LISTS *)

push_frame 0;;

(* allocates a list on the stack, where the list elements point to heap-allocated lists *)
let rec mklist n =
  if n = 0 then []
  else
    let l = mklist (n-1) in
    cons (n::[1;2;3]) l 

(* makes a (heap-allocated) pretty-printed string of a list *)
let rec string_of_list l p =
  match l with
      [] -> "[]"
    | h::t -> 
      let s = string_of_list t p in 
      (p h)^"::"^s
;;

let ex = mklist 10;;

Printf.printf "List result = %s\n" (string_of_list ex (fun l -> "("^(string_of_list l string_of_int)^")"));;
doGC();;
Printf.printf "List result = %s\n" (string_of_list ex (fun l -> "("^(string_of_list l string_of_int)^")"));;

pop_frame ();;

(* REFERENCES *)

push_frame 0;;

let rec mkrefs n =
  if n = 0 then []
  else
    let l = mkrefs (n-1) in
    (mkref [])::l 

let rec modrefs l =
  match l with
      [] -> ()
    | h::t -> h := [1;2]; modrefs t

let ex = mkrefs 10;;
doGC();;
let ex = modrefs ex;;
doGC();;

pop_frame ();;

(* ERROR HANDLING *)

doGC();;

let _ = 
  try 
    ignore(cons "hello" [])
  with Failure s -> 
    Printf.printf "Tried to allocate with no frames pushed\n"
;;

let _ = 
  try 
    ignore(pop_frame ())
  with Failure s -> 
    Printf.printf "Tried to pop a frame with no frames pushed\n"
;;

let _ = 
  try 
    ignore(push_frame (-1))
  with Invalid_argument s -> 
    Printf.printf "Tried to allocate negatively-sized frame\n"
;;
