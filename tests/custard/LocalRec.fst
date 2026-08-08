module LocalRec
open FStar.All

let rev1 (#a:Type) (l: list a) : list a =
  let rec aux (l: list a) (acc: list a) : list a =
    match l with
    | [] -> acc
    | x :: xs -> aux xs (x :: acc)
  in
  aux l []

let sum_upto (n: nat) : nat =
  let rec go (i: nat) (acc: nat) : Tot nat (decreases (if i > n then 0 else n - i + 1)) =
    if i > n then acc else go (i + 1) (acc + i)
  in
  go 0 0

(* A mutually recursive local nest, capturing an outer value. *)
let parity (base: bool) (n: nat) : bool =
  let rec even (n: nat) : Tot bool (decreases n) =
    if n = 0 then base else odd (n - 1)
  and odd (n: nat) : Tot bool (decreases n) =
    if n = 0 then not base else even (n - 1)
  in
  even n

let main () : ML unit =
  let l = rev1 [1;2;3] in
  (match l with
   | x :: _ -> FStar.IO.print_string (string_of_int x)
   | [] -> FStar.IO.print_string "empty");
  FStar.IO.print_string " ";
  FStar.IO.print_string (string_of_int (sum_upto 4));
  FStar.IO.print_string " ";
  FStar.IO.print_string (string_of_bool (parity true 3));
  FStar.IO.print_string "\n"
