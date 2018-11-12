module Bug154

val search : x:int -> l:(list int) -> Tot (b:bool{b = false})
let rec search x l =
  match l with
  | [] -> false
  | n :: l' ->  x = n || (if false then search x l' else false)

(* (\* works but it shouldn't *\) *)
(* val search : x:int -> l:(list int) -> Pure bool (requires True) (ensures (fun r -> r = mem x l)) *)
(* let rec search x l = *)
(*   match l with *)
(*   | [] -> false *)
(*   | n :: l' ->  x = n || (if false then search x l' else false) *)

(* this equivalent thing fails as it should
val search' : x:int -> l:(list int) -> Tot (r:bool{r <==> mem x l})
let rec search' x l =
  match l with
  | [] -> false
  | n :: l' -> x = n || (search' x l' && false)
*)

(* this equivalent thing fails as it should
val search' : x:int -> l:(list int) -> Tot (r:bool{r <==> mem x l})
let search' x l =
  match l with
  | [] -> false
  | n :: l' -> x = n
*)

(* this equivalent thing fails as it should
val search' : x:int -> l:(list int) -> Tot (r:bool{r <==> mem x l})
let rec search' x l =
  match l with
  | [] -> false
  | n :: l' -> if x = n then true else (if false then search' x l' else false)
*)
