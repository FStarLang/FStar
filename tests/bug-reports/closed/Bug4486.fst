module Bug4486

(* Real literals used to be stored as strings, and compared by
lexicographically comparing the (unsigned) integer and fractional parts.
That is wrong for negative reals, which made the normalizer disagree with
the SMT solver, and hence False provable. *)

open FStar.Real
open FStar.Tactics.V2
module RD = FStar.Stubs.Reflection.V2.Data
module RB = FStar.Stubs.Reflection.V2.Builtins
module RL = FStar.RealLiteral

(* F*'s lexer has no negative real literals, so we build them via the
reflection API. *)
let mhalf : real = _ by (exact (RB.pack_ln (RD.Tv_Const (RD.C_Real (RL.mk (-5) (-1))))))
let n15   : real = _ by (exact (RB.pack_ln (RD.Tv_Const (RD.C_Real (RL.mk (-15) (-1))))))
let n12   : real = _ by (exact (RB.pack_ln (RD.Tv_Const (RD.C_Real (RL.mk (-12) (-1))))))

[@@expect_failure]
let bad () : Lemma False =
  assert_norm (mhalf >=. 0.5R);
  assert (mhalf <. 0.5R)

[@@expect_failure]
let bad2 () : Lemma False =
  assert_norm (n15 >. n12);
  assert (n15 <. n12)

(* The normalizer gets these right now. *)
let _ = assert_norm (mhalf <. 0.5R)
let _ = assert_norm (mhalf <. 0.0R)
let _ = assert_norm (n15 <. n12)
let _ = assert_norm (n12 >. n15)
let _ = assert_norm (~ (mhalf >=. 0.5R))

#push-options "--no_smt"
let _ = assert (1.5R >. 1.2R)
let _ = assert (1001.0R <. 1002.00R)
#pop-options

(* And so does the SMT encoding. *)
let _ = assert (mhalf <. 0.5R)
let _ = assert (n15 <. n12)
let _ = assert (mhalf +. 0.5R == 0.0R)
let _ = assert (n15 *. 2.0R == 0.0R -. 3.0R)
