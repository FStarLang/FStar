module UnifierArith
assume
val vec (n:int) : Type
assume
val n :int
assume
val m :int
assume
val nnn : squash (n <= m /\ n <> 0)
assume
val v:vec (m - n)

// A bug in the unifier which was treating (-) structurally rather
// than as an interpreted symbol would cause it to generate a VC to
// prove that `m - n == (m - 1) - (n - 1)` by equating `m = m - 1` and
// `n = n - 1`, which of course fails.
let v' : vec ((m - 1) - (n - 1)) = v
