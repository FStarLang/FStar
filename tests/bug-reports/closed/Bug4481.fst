module Bug4481

(* The payload of C_Real used to be an unvalidated string that the SMT
encoder printed verbatim into the query, allowing arbitrary SMT-LIB to be
injected. Real literals are now represented, both in terms and in term
views, by a parsed (and canonical) mantissa and exponent: see
FStar.RealLiteral. *)

open FStar.Tactics.V2
open FStar.Real
module RL = FStar.RealLiteral
module R = FStar.Stubs.Reflection.V2.Builtins
module D = FStar.Stubs.Reflection.V2.Data

(* There is no way to inject anything into a real constant anymore: the
payload is a pair of integers. *)
let payload =
  "1.0)) :pattern ((Bug4481.r @u0)) :qid inj_q)) :named inj_a)) (assert false) (assert (! (forall ((@u0 Dummy_sort)) (! (= (Bug4481.r @u0) (BoxReal 1.0"

[@@expect_failure]
let r : real = _ by (exact (R.pack_ln (D.Tv_Const (D.C_Real payload))))

(* Non-canonical literals are not even well-typed, so that inspecting a
packed constant gives back the very same view (see inspect_pack_inv). *)
[@@expect_failure]
let noncanon = D.C_Real ({ RL.mantissa = 10; RL.exponent = -1 })

(* Even a forged (ill-typed) non-canonical literal is rejected when reading
the view back, rather than being silently canonicalized: unembedding a real
literal is injective. *)
let forged : RL.real_literal =
  FStar.Pervasives.coerce_eq #RL.real_literal_repr #RL.real_literal (magic ())
    ({ RL.mantissa = 10; RL.exponent = -1 })

[@@expect_failure]
let rbad : real = _ by (exact (R.pack_ln (D.Tv_Const (D.C_Real forged))))

(* Well-formed literals work. *)
let r5 : real = _ by (exact (R.pack_ln (D.Tv_Const (D.C_Real (RL.mk 15 (-1))))))
let r6 : real = _ by (exact (R.pack_ln (D.Tv_Const (D.C_Real (RL.mk (-25) (-2))))))

let _ = assert (r5 == 1.5R)
let _ = assert (r6 *. 4.0R +. 1.0R == 0.0R)

(* And the view of a literal is canonical, e.g. 1.500R and 1.5R give the
very same view. *)
let _ = assert_norm (R.inspect_ln (`(1.500R)) == D.Tv_Const (D.C_Real (RL.mk 15 (-1))))
let _ = assert_norm (R.inspect_ln (`(01.0R)) == D.Tv_Const (D.C_Real (RL.of_int 1)))
let _ = assert_norm (RL.to_string (RL.mk 1500 (-3)) == "1.5")
