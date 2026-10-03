(* Phantom type parameters.

   Uniform compilation (section 5.0) leaves the [Poly] type parameters in
   place, and some of them describe nothing about the runtime representation.
   Every parameter named [ph] below is such a phantom.

   Custard used to eliminate them.  It does not any more: a type's layout is a
   function of the type and of what it depends on, and "no declaration in the
   program mentions this parameter" is a fact about the whole program, so two
   units would answer it differently (section 12.5).  A phantom parameter is
   free in OCaml, and monomorphization has removed it by the time either of the
   C backends sees anything, so carrying it costs nothing that was worth a
   whole-program decision.

   What this test now checks is that they survive *uniformly*: every
   declaration keeps both parameters, so no use site can disagree with a
   declaration about the arity. *)
module Phantom
open FStar.All
open FStar.IO

(* [ph] is a parameter of the type that no field mentions.  Two constructors,
   so the newtype collapse of section 5.2 leaves the declaration standing. *)
noeq type tagged (a:Type) (ph:Type) =
  | L : a -> tagged a ph
  | R : a -> tagged a ph

(* [ph] does occur in the body -- but only in a position of [tagged] that is
   itself about to be dropped, which is what makes the analysis a fixed point
   rather than a single pass. *)
type chain (a:Type) (ph:Type) = tagged a ph

(* A function's type parameters get the same treatment.  OCaml infers them, so
   this is only visible in the IR and to the C backend, which has to
   instantiate what it is given. *)
let get (#a:Type) (#ph:Type) (x: chain a ph) : a =
  match x with
  | L v -> v
  | R v -> v

(* A cycle: neither declaration can be settled without the other, so this is
   the case that makes the analysis iterate.  Establishing that [ph] is unused
   in [odd_t] needs [even_t] settled first, and vice versa. *)
noeq type even_t (a:Type0) (ph:Type0) =
  | Zero : even_t a ph
  | ESucc : odd_t a ph -> even_t a ph
and odd_t (a:Type0) (ph:Type0) =
  | OSucc : a -> even_t a ph -> odd_t a ph

let rec depth (#a:Type) (#ph:Type) (e: even_t a ph) : nat =
  match e with
  | Zero -> 0
  | ESucc o -> 1 + depth_odd o
and depth_odd (#a:Type) (#ph:Type) (o: odd_t a ph) : nat =
  match o with
  | OSucc _ e -> 1 + depth e

let main () : ML unit =
  let p : chain int bool = L 7 in
  let q : chain int string = R 8 in
  let e : even_t int bool = ESucc (OSucc 1 (ESucc (OSucc 2 Zero))) in
  print_string (string_of_int (get p + get q + depth e));
  print_string "\n"
