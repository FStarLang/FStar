module ExtBoolShortCircuit

/// `&&`, `||` and `not`.
///
/// F* gives `&&` and `||` *short-circuit typing*: in `b && e`, `e` is checked
/// under the assumption `b`. So `d <> 0l && (x / d) = q` typechecks, and it is
/// only well-defined at runtime if the backend also short-circuits. A backend
/// that evaluates both operands eagerly divides by zero, which is a hard
/// crash (SIGFPE on x86 C, `Division_by_zero` in OCaml, a panic in Rust) --
/// severity 1. That makes this test a *crash* detector rather than a
/// performance detector, which is what we want: a "wrong performance" bug is
/// invisible to a test that only compares results.
///
/// The partially-applied case (where extraction must fall back on the plain
/// two-argument `Prims.op_Amp_Amp` and therefore loses the short circuit) lives
/// in ExtBoolHigherOrder, which needs closures and so cannot target C.

module I32 = FStar.Int32

let chk (n:I32.t) (b:bool{b}) : I32.t = if b then 0l else n
let ( &&& ) (a b : I32.t) : I32.t = if a = 0l then b else a

let zero : I32.t = 0l
let ten  : I32.t = 10l
let two  : I32.t = 2l
let tru  : bool = true
let fls  : bool = false

/// If `&&` is not short-circuiting, this divides by zero.
let and_guards_div () : bool =
  not (I32.eq zero 0l) && I32.eq (I32.div ten zero) 5l

/// Likewise for `||`: the right operand must not be evaluated when the left
/// one is already true.
let or_guards_div () : bool =
  I32.eq zero 0l || I32.eq (I32.div ten zero) 5l

/// Nested, so that the guard for the inner division comes from an enclosing
/// `&&` rather than the immediately preceding operand.
let nested_guard () : bool =
  not (I32.eq zero 0l) && (I32.eq (I32.div ten zero) 5l || I32.eq (I32.rem ten zero) 0l)

/// `&&` chained left-to-right: only the first false operand may be reached.
let chained () : bool =
  I32.eq ten 10l && not (I32.eq zero 0l) && I32.eq (I32.div ten zero) 1l

let short_circuit_tests () : I32.t =
     chk 1l (not (and_guards_div ()))
 &&& chk 2l (or_guards_div ())
 &&& chk 3l (not (nested_guard ()))
 &&& chk 4l (not (chained ()))

/// Plain truth tables, to catch a backend that swaps or drops an operator.
let truth_tables () : I32.t =
     chk 10l (tru && tru)
 &&& chk 11l (not (tru && fls))
 &&& chk 12l (not (fls && tru))
 &&& chk 13l (not (fls && fls))
 &&& chk 14l (tru || tru)
 &&& chk 15l (tru || fls)
 &&& chk 16l (fls || tru)
 &&& chk 17l (not (fls || fls))
 &&& chk 18l (not fls)
 &&& chk 19l (not (not tru))
 &&& chk 20l (not (tru <> tru))
 &&& chk 21l (tru <> fls)
 &&& chk 22l (tru = tru)
 &&& chk 23l (not (tru = fls))

/// `if/then/else` on a boolean must not evaluate the untaken branch either.
let if_lazy () : I32.t =
     chk 40l (I32.eq (if I32.eq zero 0l then two else I32.div ten zero) 2l)
 &&& chk 41l (I32.eq (if not (I32.eq zero 0l) then I32.div ten zero else two) 2l)

let main () : I32.t =
     short_circuit_tests ()
 &&& truth_tables ()
 &&& if_lazy ()
