module MachineIntSize

(* The simplifier decides [FStar.UInt.size x n] and [FStar.Int.size x n] when
   [x] and [n] are integer constants, without unfolding [size] (which would
   need [zeta] for [pow2]) and without SMT. *)

open FStar.Tactics.V2

let decided () : Tac unit =
  norm [simplify; primops; delta_qualifier ["unfold"]];
  match term_as_formula (cur_goal ()) with
  | True_ -> exact (`())
  | _ -> fail "not decided by the simplifier"

let _ = assert (FStar.UInt.size 255 8 /\ FStar.UInt.size 0 8 /\ FStar.UInt.size 0 0) by (decided ())
let _ = assert (~(FStar.UInt.size 256 8) /\ ~(FStar.UInt.size (-1) 8) /\ ~(FStar.UInt.size 1 0)) by (decided ())
let _ = assert (FStar.Int.size 127 8 /\ FStar.Int.size (-128) 8 /\ FStar.Int.size (-1) 1) by (decided ())
let _ = assert (~(FStar.Int.size 128 8) /\ ~(FStar.Int.size (-129) 8) /\ ~(FStar.Int.size 1 1)) by (decided ())
let _ = assert (FStar.UInt.size 340282366920938463463374607431768211455 128) by (decided ())
let _ = assert (~(FStar.UInt.size 340282366920938463463374607431768211456 128)) by (decided ())

(* The width of a literal's type, here [FStar.UInt32.n], is an [unfold] constant *)
let _ = assert (FStar.UInt.size 4096 FStar.UInt32.n) by (decided ())

(* Not decided on a non-constant *)
[@@expect_failure]
let _ = assert (forall (x:nat). FStar.UInt.size (x % 256) 8) by (decided ())
