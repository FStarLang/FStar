module TailKept

(* [tag] reaches nothing but the recursive call, which passes it unchanged; as
   a loop, the call does not write it, so C sees an unused parameter. *)
let rec drain (tag:string) (n:nat) (acc:int) : Tot int (decreases n) =
  if n = 0 then acc else drain tag (n - 1) (acc + n)

let main () : FStar.All.ML unit =
  FStar.IO.print_string (string_of_int (drain "unused" 10 0) ^ "\n")
