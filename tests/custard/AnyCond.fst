module AnyCond
open FStar.All
open FStar.IO

(* Section 117.1.  [data]'s type depends on [b], so it is laid out as [any];
   the [Pk false] branch binds it and uses it as an [if] condition, which is
   the one expression position the coercion traversal visited with no
   expectation. *)
noeq type pkt = | Pk : b:bool -> data:(if b then int else bool) -> pkt

let get (p:pkt) : ML int =
  match p with
  | Pk true n  -> n + 100
  | Pk false c -> if c then 1 else 0

let main () : ML unit =
  print_string (string_of_int (get (Pk true 42)));  print_string "\n";
  print_string (string_of_int (get (Pk false true))); print_string "\n"
