module KeyCollision
open FStar.All
open FStar.IO

(* Section 115.  A specialization key is a string, and a [string] argument
   marked [@@@monomorphize] puts its *value* into that string -- unescaped.
   So the key of [combine "a" "b\"#1=\"c"] and the key of
   [combine "a\"#1=\"b" "c"] were the same text, the second request hit the
   first one's cache entry, and one of the two calls got the other's
   implementation.  Escaping the constant is what keeps the key injective.

   The two strings below are the same characters split differently, which is
   exactly the collision; if it comes back, both lines print the same. *)
let combine ([@@@monomorphize] a:string) ([@@@monomorphize] b:string)
            (suffix:string) : string =
  a ^ "|" ^ b ^ suffix

let main () : ML unit =
  print_string (combine "a" "b\"#1=\"c" "\n");
  print_string (combine "a\"#1=\"b" "c" "\n")
