module MutualTail
open FStar.All

(* Tail calls that are not self calls -- mutual recursion between functions
   of different signatures, with and without a result, and recursion through
   a closure -- run in constant stack under Cherry, as they do in OCaml.  The
   test runs with a 1 MB stack (CHERRY_RUN_MutualTail), which a million
   frames of any of these loops would overflow. *)

let rec ping (n:int) (acc:int) : ML int =
  if n = 0 then acc else pong (n - 1) (acc + 1) "ab"
and pong (n:int) (acc:int) (s:string) : ML int =
  ping n (acc + String.length s)

let count : ref int = alloc 0

let rec tick (n:int) : ML unit =
  if n > 0 then tock n 1
and tock (n:int) (k:int) : ML unit =
  count := !count + k;
  tick (n - k)

let rec step (k:int -> ML int) (n:int) : ML int =
  if n = 0 then 7 else k (n - 1)

let rec around (n:int) : ML int = step around n

(* A tail call returning a struct is not marked: GCC 15 rejects the mark at
   -O2 once [pick] is inlined into its closure's entry point, whose own call
   would be marked too.  The .chgrep rule compiles this at -O2. *)
let rec check (t:int) : Tot (option int) (decreases t) =
  if t > 100 then (match check (t - 100) with Some x -> Some (x + 100) | None -> None)
  else if t > 0 then Some t else None
let pick (a b:option int) : option int =
  match a with
  | None -> b
  | Some x -> check x
let use (f:option int -> option int -> option int) : ML int =
  match f (Some 5) None with Some x -> x | None -> 0

let main () : ML unit =
  FStar.IO.print_string (string_of_int (ping 1000000 0) ^ "\n");
  tick 1000000;
  FStar.IO.print_string (string_of_int !count ^ "\n");
  FStar.IO.print_string (string_of_int (around 1000000) ^ "\n");
  FStar.IO.print_string (string_of_int (use pick) ^ "\n")
