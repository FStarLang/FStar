(*--build-config
    options:--admit_fsi FStar.Set;
    other-files:constr.fst set.fsi heap.fst st.fst all.fst list.fst string.fst
  --*)
module Gcd
open FStar.List
open FStar.Constructive

assume val intuitionistic_of_smt : #a:Type -> u:unit{a} -> Tot a
assume val smt_of_intuitionistic : #a:Type -> a -> Lemma a

type divides (a:pos) (b:pos) = (cexists (fun (c:pos) -> (a*c) == b))

type is_gcd (a:pos) (b:pos) (gcd:pos) =
    ((forall (d:pos). ((divides d a) /\ (divides d b)) ==> (divides d gcd)) /\ (divides gcd a) /\ (divides gcd b))

val times_one : a:pos -> Lemma (a * 1 = a)
let times_one a = ()

val a_divides_a' : a:pos -> Tot (divides a a)
let a_divides_a' a = ExIntro 1 (intuitionistic_of_smt (times_one a))

val a_divides_a : a:pos -> Lemma (divides a a)
let a_divides_a a = smt_of_intuitionistic (a_divides_a' a) //don't see why it doesn't work to inline the definition of a_divides_a'

val gcd_triv : a:pos -> Lemma (is_gcd a a a)
let gcd_triv a = a_divides_a a
