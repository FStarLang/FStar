module ExtBoolHigherOrder

/// `&&` / `||` used as *values* rather than fully applied.
///
/// F* only gives `&&` its short-circuit typing at full application. Passed as
/// a function argument it becomes `Prims.op_AmpAmp`, an ordinary strict
/// two-argument function, so both operands are evaluated. That is not a bug,
/// but the resulting *value* must still be right, and the code must compile.
/// Because both operands really are evaluated here, we must not hide a
/// division by zero under them.
///
/// This needs closures, which the C backend rejects (`Warning 11: this
/// expression is not Low*`), hence NO_C in the Makefile.

module I32 = FStar.Int32

let chk (n:I32.t) (b:bool) : I32.t = if b then 0l else n
let ( &&& ) (a b : I32.t) : I32.t = if a = 0l then b else a

let tru : bool = true
let fls : bool = false

/// `&&` used as a value: extraction must fall back on `Prims.op_AmpAmp`.
/// Both operands are evaluated, so we must not put a division under it -- we
/// only check that the *value* is still right and that it compiles at all.
let ap (f : bool -> bool -> bool) (a b : bool) : bool = f a b

let main () : I32.t =
     chk 30l (ap (fun a b -> a && b) tru tru)
 &&& chk 31l (not (ap (fun a b -> a && b) tru fls))
 &&& chk 32l (ap (fun a b -> a || b) fls tru)
 &&& chk 33l (not (ap (fun a b -> a || b) fls fls))
