module TryBinder
open FStar.All
open FStar.IO

(* Issue 4931.  A handler [fun e -> match e with ...] whose branches mention
   [e] must keep [e] bound to the caught exception, not to an outer [e]; and
   a branch that re-raises [e] re-raises the caught exception. *)

exception E of int
exception F

let get (e:exn) : int = match e with E k -> k | _ -> 0

let with_default () : ML int =
  let e = E 1 in
  let r = try_with (fun () -> raise (E 2))
            (fun e -> match e with
              | E _ -> get e
              | _ -> 0) in
  r + 10 * get e

let guarded (n:int) : ML int =
  try_with (fun () -> if n = 0 then raise F else raise (E n))
           (fun e -> match e with
             | E _ -> if get e > 5 then get e else 0 - get e
             | _ -> raise e)

let main () : ML unit =
  print_string (string_of_int (with_default ())); print_string " ";
  print_string (string_of_int (guarded 7)); print_string " ";
  print_string (string_of_int (guarded 3)); print_string " ";
  print_string (try_with (fun () -> string_of_int (guarded 0))
                         (fun x -> match x with F -> "F" | _ -> "other"));
  print_string "\n"
