module Bug1592

open FStar.HyperStack
open FStar.HyperStack.ST
open LowStar.Buffer

open LowStar.Modifies.Linear

(*
 * A pathological example for modifies_trans
 * Thanks to Santiago for the example
 *)
assume val f: b:buffer UInt8.t -> Stack unit
  (requires fun h -> live h b)
  (ensures  fun h0 _ h1 -> modifies (loc_buffer b) h0 h1)

#reset-options "--max_fuel 0 --max_ifuel 0 --using_facts_from '* -LowStar.Monotonic.Buffer.modifies_trans'"

let test (a:buffer UInt8.t) (b:buffer UInt8.t) : Stack unit
  (requires fun h0 -> live h0 a /\ live h0 b /\ disjoint a b)
  (ensures  fun h0 _ h1 -> live h1 a /\ live h1 b /\ modifies (loc_union (loc_buffer a) (loc_buffer b)) h0 h1)
= push_frame();
  let c = alloca 0uy 1ul in
  let d = alloca 0uy 1ul in
  f a;
  f b;
  f c;
  f d;
  f a;
  f b;
  f c;
  f d;
  pop_frame()
