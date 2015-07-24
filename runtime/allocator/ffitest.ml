(*
external inspect : 'a -> unit = "inspect";;
*)

open Camlstack;;

push_frame 0;;

let rec mklist n =
  if n = 0 then []
  else
    let l = mklist (n-1) in
    cons (n::[1;2;3]) l

let rec string_of_list l p =
  match l with
      [] -> "[]"
    | h::t -> 
      let s = string_of_list t p in 
      (p h)^"::"^s
;;

let ex = mklist 10;;

Printf.printf "List result = %s\n" (string_of_list ex (fun l -> "("^(string_of_list l string_of_int)^")"));;

print_mask ();;

Gc.full_major();;
Gc.print_stat (Pervasives.stdout);;

Printf.printf "List result = %s\n" (string_of_list ex (fun l -> "("^(string_of_list l string_of_int)^")"));;

pop_frame ();;

print_mask ();;

Gc.full_major();;
