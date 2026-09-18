module CaptureErase
open FStar.All
open FStar.IO

(* Section 116.  [go] captures [p], which the enclosing declaration erased. *)
let count (p:FStar.Ghost.erased bool) (n:nat) : nat =
  let rec go (q:FStar.Ghost.erased bool) (n:nat) : Tot nat (decreases n) =
    if n = 0 then 0 else 1 + go p (n - 1)
  in go p n

let main () : ML unit =
  print_string (string_of_int (count (FStar.Ghost.hide true) 3));
  print_string "\n"
