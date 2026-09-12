module Curried
open FStar.All
open FStar.IO

(* [int -> ML (int -> Tot int)]: the effect fires on the *first* arrow, so a
   one-argument call is already impure and may not be dropped, even though the
   function "looks" partially applied (section 7.3). *)
let step (n:int) : ML (int -> Tot int) =
  print_string "step ";
  (fun y -> y + n)

(* The same, reached through a variable: there is no declaration to consult,
   so the effect has to come from the arrow type of the head. *)
let via (h : int -> ML (int -> Tot int)) : ML int =
  let _ = h 7 in
  h 8 9

(* An *explicit* type binder carries nothing at runtime under the uniform
   compilation of types (section 5.0): it must disappear from the signature
   and from the call site alike. *)
let idt (a:Type) (x:a) : a = x

let main () : ML unit =
  let _ = step 1 in
  let k = step 2 in
  print_string (string_of_int (k 10));
  print_string "\n";
  print_string (string_of_int (step 3 100));
  print_string "\n";
  print_string (string_of_int (via step));
  print_string "\n";
  print_string (idt string "explicit");
  print_string "\n"
