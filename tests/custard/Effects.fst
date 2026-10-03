module Effects
open FStar.All
open FStar.IO

(* An unused pure binding is deleted; an unused impure one becomes a
   statement, so its output still appears, in order (section 7.3). *)
let noisy (s:string) : ML int =
  print_string s;
  0

let discipline () : ML unit =
  let _unused_pure = 1 + 1 in
  let _unused_impure = noisy "effect kept\n" in
  print_string "after\n"

(* A divergent function is E_Impure even though it returns a value. *)
let rec countdown (n:int) : Dv int =
  if n <= 0 then 0 else countdown (n - 1)

(* Section 7.2: [box] is not an F* effect, it is a type constructor carrying
   [@@extract_as_impure_effect], exactly as Pulse encodes [stt].  An arrow into
   [box b idx] must extract as an impure arrow returning [b]. *)
[@@FStar.Attributes.extract_as_impure_effect]
let box (a:Type) (idx:int) : Type = unit -> ML a

let boxed (n:int) : box int n = fun () -> (print_string "boxed\n"; n + 1)

let main () : ML unit =
  discipline ();
  print_string (string_of_int (countdown 5));
  print_string "\n";
  let f = boxed 41 in
  print_string (string_of_int (f ()));
  print_string "\n"
