module ExtSmoke

/// Smoke test for the harness itself: checks that the pass/fail plumbing of
/// every backend works, i.e. that `main` really is called and that its result
/// really becomes the process exit status.
///
/// NOTE for test authors: top-level constants in this directory must be
/// *literals*. A top-level binding whose definition is a computation is not a
/// C constant, so Karamel emits a `krmlinit_globals` static initializer for it;
/// that works for C but is rejected outright by the Rust backend (warning 9).

module I32 = FStar.Int32

/// `chk` requires its argument to be *provably* true, so that a cell failing
/// at runtime always means F* and the backend disagree. `chk_raw` is the
/// unrefined version; this module is the one place it is legitimate, because
/// checking that a *failing* check reports its tag is the whole point here.
/// Real tests must use `chk`.
let chk_raw (n:I32.t) (b:bool) : I32.t = if b then 0l else n
let chk (n:I32.t) (b:bool{b}) : I32.t = if b then 0l else n
let ( &&& ) (a b : I32.t) : I32.t = if a = 0l then b else a

let one : I32.t = 1l
let one' : I32.t = 1l   (* a second copy: `one == one` is rejected by the C
                           compiler under -Wtautological-compare *)
let two : I32.t = 2l

let main () : I32.t =
     chk 1l (I32.eq one 1l)
 &&& chk 2l (not (I32.eq one two))
     (* a failing check must produce its own tag, not 0 *)
 &&& chk 3l (I32.eq (chk_raw 42l (I32.eq one 7l)) 42l)
     (* a passing check must produce 0 *)
 &&& chk 4l (I32.eq (chk_raw 9l (I32.eq one 1l)) 0l)
     (* &&& must return the *first* failure *)
 &&& chk 5l (I32.eq (chk_raw 6l false &&& chk_raw 7l false) 6l)
 &&& chk 8l (I32.eq (one `I32.add` one) two)
     (* the refinement on `chk` must not make the runtime test vacuous: the
        condition still has to be evaluated at runtime, so a backend that
        computes it wrongly still fails the cell. *)
 &&& chk 9l (I32.eq (chk_raw 11l (I32.eq one one')) 0l)
