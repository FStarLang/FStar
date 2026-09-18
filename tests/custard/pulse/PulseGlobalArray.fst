module PulseGlobalArray
#lang-pulse
open Pulse
module A  = Pulse.Lib.Array
module G  = Pulse.Lib.GlobalArray
module US = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32

(* Section 71.  A table baked into the program image.

   The three things being pinned:

   - [primes] becomes [static const uint8_t ...[7] = { 2U, ... }], an array
     object with a braced initializer, so there is no startup code for it and
     the linker may put it in .rodata.  In particular it is *not* in
     custard_init_globals, which is what a global Custard cannot initialize
     in place would get.

   - [sq] shows that the list need not be written out: it is a total function
     of a literal, and the norm budget reduces it before extraction, so what
     reaches the backend is the same literal spine.

   - [main] reads through [G.array_of_static_array], which is where the
     [const] is cast away, and returns 0 only if every element survived the
     round trip. *)

let primes : G.static_array U8.t =
  G.mk_static_array [2uy; 3uy; 5uy; 7uy; 11uy; 13uy; 17uy]

let rec squares (n : nat { n <= 100 }) : Tot (list U32.t) (decreases n) =
  if n = 0 then []
  else FStar.List.Tot.append (squares (n - 1))
                             [U32.uint_to_t ((n - 1) * (n - 1))]

let sq : G.static_array U32.t = G.mk_static_array (squares 5)

(* [squares] is a [let rec], so its length is not something the SMT solver
   knows; [assert_norm] computes it.  The lemma is erased, but its call site
   is what puts the fact in scope for the array bound below. *)
let sq_len () : Lemma (Seq.length (G.static_array_elems sq) == 5) =
  assert_norm (FStar.List.Tot.length (squares 5) == 5)

fn sum_primes ()
  returns r:U32.t
{
  let a = G.array_of_static_array primes;
  with p s. assert (A.pts_to a #p s);
  A.pts_to_len a;
  let x0 = A.op_Dot_Lparen_Rparen a 0sz;
  let x6 = A.op_Dot_Lparen_Rparen a 6sz;
  drop_ (A.pts_to a #p s);
  U32.((FStar.Int.Cast.uint8_to_uint32 x0) +^
       (FStar.Int.Cast.uint8_to_uint32 x6))
}

fn last_square ()
  returns r:U32.t
{
  let a = G.array_of_static_array sq;
  with p s. assert (A.pts_to a #p s);
  A.pts_to_len a;
  sq_len ();
  let x = A.op_Dot_Lparen_Rparen a 4sz;
  drop_ (A.pts_to a #p s);
  x
}

fn main ()
  returns r:US.t
{
  let a = sum_primes ();
  let b = last_square ();
  (* 2 + 17 = 19, and the fifth square is 16. *)
  if (U32.(a =^ 19ul) && U32.(b =^ 16ul)) { 0sz } else { 1sz }
}
