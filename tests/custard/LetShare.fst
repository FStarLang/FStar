module LetShare

(* Section 30.17.  A value that is small only because it shares subterms.

   [ext] takes its argument apart and puts each field back twice, so the
   normal form of [b n] is twice the size of the normal form of [b (n-1)]:
   linear as written, exponential once written out.  Specializing [use] on it
   means normalizing it, which is exactly the step that destroys the sharing.

   With the budget below, neither the full nor the weak reduction fits, and
   the argument is keyed and substituted as written -- which is what makes
   the extracted code linear in the chain, and what this test checks by
   running it: the answer must be the one the exponential form would give. *)

module U32 = FStar.UInt32

noeq
type bnd = {
  p : U32.t -> U32.t;
  q : U32.t -> U32.t;
  r : U32.t -> U32.t;
}

let ext (b: bnd) : bnd =
  let { p = p; q = q; r = r } = b in
  { p = (fun x -> U32.add_mod (p x) (q x));
    q = (fun x -> U32.add_mod (q x) (r x));
    r = (fun x -> U32.add_mod (r x) (p x)) }

let b0 : bnd = {
  p = (fun x -> x);
  q = (fun x -> U32.add_mod x 1ul);
  r = (fun x -> U32.add_mod x 2ul);
}

let b1  = ext b0
let b2  = ext b1
let b3  = ext b2
let b4  = ext b3
let b5  = ext b4
let b6  = ext b5
let b7  = ext b6
let b8  = ext b7
let b9  = ext b8
let b10 = ext b9
let b11 = ext b10
let b12 = ext b11

let use ([@@@FStar.Attributes.monomorphize] b: bnd) (x: U32.t) : U32.t =
  U32.add_mod (b.p x) (b.r x)

let main () : FStar.All.ML unit =
  FStar.IO.print_string (U32.to_string (use b12 7ul));
  FStar.IO.print_string "\n"
