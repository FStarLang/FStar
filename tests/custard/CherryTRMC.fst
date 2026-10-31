module CherryTRMC
module U32 = FStar.UInt32
module L = FStar.List.Tot
open FStar.All

(* Tail recursion modulo constructors (cherry.md, "Tail calls"): a recursive
   call whose result is stored into a constructor that is then returned is a
   jump, with the cell written through a destination pointer.  The test runs
   with a 1 MB stack, so each of these would overflow if it recursed. *)

let rec upto (n:nat) (acc:list int) : Tot (list int) (decreases n) =
  if n = 0 then acc else upto (n - 1) (n :: acc)

let rec incr_all (l:list int) : list int =
  match l with
  | [] -> []
  | x :: t -> (x + 1) :: incr_all t

(* A plain tail call next to the modulo-cons one keeps the destination. *)
let rec evens (l:list int) : list int =
  match l with
  | [] -> []
  | x :: t -> if x % 2 = 0 then x :: evens t else evens t

(* A return through a call of another function writes its result. *)
let rec copy_then_rev (l:list int) (rest:list int) : list int =
  match l with
  | [] -> L.rev rest
  | x :: t -> x :: copy_then_rev t rest

(* Two cells per step: the call is under the inner one. *)
let rec dup (l:list int) : list int =
  match l with
  | [] -> []
  | x :: t -> x :: x :: dup t

(* The hole is not the last field. *)
type tree = | Leaf | Node : tree -> int -> tree -> tree

let rec left_spine (n:nat) : tree =
  if n = 0 then Leaf else Node (left_spine (n - 1)) n Leaf

let rec right_spine (n:nat) : tree =
  if n = 0 then Leaf else Node Leaf n (right_spine (n - 1))

let rec left_depth (t:tree) (acc:nat) : nat =
  match t with
  | Leaf -> acc
  | Node l _ _ -> left_depth l (acc + 1)

let rec right_depth (t:tree) (acc:nat) : nat =
  match t with
  | Leaf -> acc
  | Node _ _ r -> right_depth r (acc + 1)

(* A raise part way leaves the cells built so far, which must be freed. *)
exception Stop
let rec until (k:int) (l:list int) : ML (list int) =
  match l with
  | [] -> []
  | x :: t -> if x = k then raise Stop else x :: until k t

let rec map_ml (f:int -> ML int) (l:list int) : ML (list int) =
  match l with
  | [] -> []
  | x :: t -> let y = f x in y :: map_ml f t

let n : nat = 1000000

let main () : ML U32.t =
  let xs = upto n [] in
  let k = 3 in
  let ys = L.map (fun x -> x + k) xs in
  let zs = L.filter (fun x -> x % 2 = 0) ys in
  let ws = L.append zs xs in
  let ok1 = L.length ws = n + n / 2 && L.for_all (fun x -> x > k) ys in
  let ok2 = L.length (incr_all xs) = n && L.length (evens xs) = n / 2 in
  let ok3 = L.length (copy_then_rev xs [1; 2]) = n + 2 in
  let ok4 = L.length (dup xs) = n + n in
  let ok5 = left_depth (left_spine n) 0 = n && right_depth (right_spine n) 0 = n in
  let ok6 = (try let _ = until 500000 xs in false with Stop -> true | _ -> false) in
  let ok7 = L.length (map_ml (fun x -> x + 1) xs) = n in
  let ok8 = (try let _ = map_ml (fun x -> if x = 700000 then raise Stop else x) xs in false
             with Stop -> true | _ -> false) in
  let ok9 = (match incr_all [1; 2; 3] with [2; 3; 4] -> true | _ -> false) &&
            (match dup [1; 2] with [1; 1; 2; 2] -> true | _ -> false) &&
            (match copy_then_rev [1; 2] [3; 4] with [1; 2; 4; 3] -> true | _ -> false) in
  if ok1 && ok2 && ok3 && ok4 && ok5 && ok6 && ok7 && ok8 && ok9 then 0ul
  else begin
    FStar.IO.print_string (string_of_bool ok1 ^ string_of_bool ok2 ^ string_of_bool ok3 ^
      string_of_bool ok4 ^ string_of_bool ok5 ^ string_of_bool ok6 ^ string_of_bool ok7 ^
      string_of_bool ok8 ^ string_of_bool ok9 ^ "\n");
    1ul
  end
