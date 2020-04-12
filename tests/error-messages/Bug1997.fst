module Bug1997

(* The actual test is printing this module and comparing to
 * the expected output. *)

(* This one associates to the left, it's a custom op *)
let ( =^ ) a b = a+b
let test1 (a b c : int) = a =^ b =^ c
let test2 (a b c : int) = (a =^ b) =^ c
let test3 (a b c : int) = a =^ (b =^ c)

let _ = assert_norm (test1 == test2)
[@expect_failure] let _ = assert_norm (test1 == test3)

(* Implication associates to the right. It is not a custom op. *)
let imp_assoc_0 (p q r : prop) = p ==> q ==> r
let imp_assoc_1 (p q r : prop) = p ==> (q ==> r)
let imp_assoc_2 (p q r : prop) = (p ==> q) ==> r

let _ = assert_norm (imp_assoc_0 == imp_assoc_1)
[@expect_failure] let _ = assert_norm (imp_assoc_1 == imp_assoc_2)

(* Implication binds tighter than iff *)
let imp_iff_0 (p q r : prop) = p ==> q <==> r
let imp_iff_1 (p q r : prop) = (p ==> q) <==> r
let imp_iff_2 (p q r : prop) = p ==> (q <==> r)

let _ = assert_norm (imp_iff_0 == imp_iff_1)
[@expect_failure] let _ = assert_norm (imp_iff_1 == imp_iff_2)

(* Conjunction binds tighter than implication *)
let imp_conj_1 (p q r s : prop) = p ==> q /\ r ==> s
let imp_conj_2 (p q r s : prop) = (p ==> q) /\ (r ==> s)
let imp_conj_3 (p q r s : prop) = p ==> (q /\ (r ==> s))
let imp_conj_4 (p q r s : prop) = p ==> ((q /\ r) ==> s)

let _ = assert_norm (imp_conj_1 == imp_conj_4)
[@expect_failure] let _ = assert_norm (imp_conj_1 == imp_conj_3)
[@expect_failure] let _ = assert_norm (imp_conj_1 == imp_conj_2)
[@expect_failure] let _ = assert_norm (imp_conj_2 == imp_conj_3)
[@expect_failure] let _ = assert_norm (imp_conj_2 == imp_conj_4)
[@expect_failure] let _ = assert_norm (imp_conj_3 == imp_conj_4)

(* Sanity check for negation *)
let impneg1 (p q r : prop) = p ==> q /\ ~p ==> r
let impneg2 (p q r : prop) = (p ==> q) /\ (~p ==> r)
let impneg3 (p q r : prop) = p ==> (q /\ (~p ==> r))
let impneg4 (p q r : prop) = p ==> ((q /\ ~p) ==> r)

let _ = assert_norm (impneg1 == impneg4)
[@expect_failure] let _ = assert_norm (impneg1 == impneg3)
[@expect_failure] let _ = assert_norm (impneg1 == impneg2)
[@expect_failure] let _ = assert_norm (impneg2 == impneg3)
[@expect_failure] let _ = assert_norm (impneg2 == impneg4)
[@expect_failure] let _ = assert_norm (impneg3 == impneg4)

(* Conjunction binds tighter than disjunction *)
let cd1 (p q r : prop) = p /\ q \/ r
let cd2 (p q r : prop) = (p /\ q) \/ r
let cd3 (p q r : prop) = p /\ (q \/ r)

let _ = assert_norm (cd1 == cd2)
[@expect_failure] let _ = assert_norm (cd1 == cd3)
[@expect_failure] let _ = assert_norm (cd2 == cd3)

let m0 (p q r s : prop) = p /\ (q \/ r) /\ s
let m1 (p q r s : prop) = p /\ q \/ r /\ s
let m2 (p q r s : prop) = (p /\ q) \/ r /\ s
let m3 (p q r s : prop) = (p /\ q) \/ (r /\ s)
let m4 (p q r s : prop) = p /\ q \/ (r /\ s)

let _ = assert_norm (m1 == m2)
let _ = assert_norm (m1 == m3)
let _ = assert_norm (m1 == m4)
[@expect_failure] let _ = assert_norm (m0 == m1)
[@expect_failure] let _ = assert_norm (m0 == m2)
[@expect_failure] let _ = assert_norm (m0 == m3)
[@expect_failure] let _ = assert_norm (m0 == m4)

let n0 (p q r s : prop) = p \/ (q /\ r) \/ s
let n1 (p q r s : prop) = p \/ q /\ r \/ s
let n2 (p q r s : prop) = (p \/ q) /\ r \/ s
let n3 (p q r s : prop) = (p \/ q) /\ (r \/ s)
let n4 (p q r s : prop) = p \/ q /\ (r \/ s)

let _ = assert_norm (n0 == n1)
[@expect_failure] let _ = assert_norm (n1 == n2)
[@expect_failure] let _ = assert_norm (n1 == n3)
[@expect_failure] let _ = assert_norm (n1 == n4)
[@expect_failure] let _ = assert_norm (n2 == n3)
[@expect_failure] let _ = assert_norm (n2 == n4)
[@expect_failure] let _ = assert_norm (n3 == n4)
