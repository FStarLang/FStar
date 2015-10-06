(*--build-config
 options: --codegen OCaml
--*)
module M

type t (n:nat) = unit

(* Works *)
type v (n:nat) = 
| C : t n -> v n

type u1 n = t n

(* Works *)
type v1 (n:nat) = 
| C1 : u1 n -> v1 n

type u2 = t

(* Error: with --debug Extreme
datacon M.C2 : (_0:(u2 n) -> Tot (v2 n)) 

Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.
Failure("Substitution must be fully applied")
*)
type v2 (n:nat) = 
| C2 : u2 n -> v2 n 


