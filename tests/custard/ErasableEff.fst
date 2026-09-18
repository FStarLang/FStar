module ErasableEff

open FStar.All


(* Section 125.10.  An effect can carry [@@erasable], which makes every
   computation in it proof-level whatever its result type says.  A definition
   in such an effect extracts to [()], and its declared result type has to
   agree: saying [int] there produced OCaml that did not compile.

   The effect is defined with a representation, so it is *reifiable* too, and
   reifying it produces the representation of a value that does not exist --
   which is why the erasable question has to be asked first. *)

type repr (a:Type) = a
let return (a:Type) (x:a) : repr a = x
let bind (a b:Type) (f:repr a) (g:a -> repr b) : repr b = g f
let lift_PURE (a:Type) (f:unit -> a) : repr a = f ()

total reifiable
effect {
  PLAIN with { repr; return; bind }
}

[@@erasable]
total
effect {
  SPEC with { repr; return; bind }
}

sub_effect PURE ~> PLAIN = lift_PURE
sub_effect PURE ~> SPEC = lift_PURE

effect Plain (a:Type) = PLAIN a
effect Spec (a:Type) = SPEC a

let plain_int () : Plain int = 7
let spec_int () : Spec int = 7

(* Not erasable: the call survives and the result is an [int]. *)
let use_plain () : Plain int = let x = plain_int () in x + 1

(* Erasable despite the [int]: the body is gone and so is the type. *)
let use_spec () : Spec int = let x = spec_int () in x + 1

(* Erasable with an argument that is not, and with a function result: still
   nothing, because what the effect erases is the whole computation. *)
let use_spec_arg (n:int) : Spec (int -> int) = (fun y -> y + n)

(* [Ghost] is the erasable effect F* ships, and answers the same way. *)
let use_ghost () : GTot int = 7

(* Reified, because a [PLAIN] computation cannot be composed with [ML].  What
   comes back is a value of the representation type, which is the [int]. *)
let plain_result : int = reify (use_plain ())

let main () : ML unit =
  FStar.IO.print_string (string_of_int plain_result);
  FStar.IO.print_string "\n"
