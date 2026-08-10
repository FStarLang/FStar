module ExtProjectorOfCtor

/// A projector applied directly to a constructor application. **Known krml
/// crash, XFAIL_C.**
///
/// `Circle?.radius (Circle seven)` makes the C backend die with an uncaught
/// OCaml exception:
///
///     Fatal error: exception Failure("Expected a type annotation for:
///       (CStar.Struct (None, [((Some "tag"), ...); (None, (CStar.Struct
///       (None, [((Some "case_Circle"), ...)])))]))")
///
/// i.e. the anonymous struct literal for `Circle seven` reaches the C printer
/// with no type to give the compound literal. `let c = Circle seven in
/// Circle?.radius c` and `match Circle seven with | Circle r -> r | _ -> 0ul`
/// both work, so the workaround is to bind the constructor application first
/// -- which is why every other module in this directory does exactly that.
///
/// This is severity 4: krml aborts with an unhandled exception rather than a
/// diagnostic, so there is no usable output and the message says nothing
/// about the user's source. Note that krml still *exits 0*, so a build system
/// that only checks the exit status will happily carry on with no output
/// file.

module I32 = FStar.Int32
module U32 = FStar.UInt32

let chk (n:I32.t) (b:bool) : I32.t = if b then 0l else n
let ( &&& ) (a b : I32.t) : I32.t = if a = 0l then b else a

let one : U32.t = 1ul
let two : U32.t = 2ul
let seven : U32.t = 7ul

type shape =
  | Circle : radius:U32.t -> shape
  | Rect   : w:U32.t -> h:U32.t -> shape
  | Empty  : shape

let main () : I32.t =
     chk 1l (U32.eq (Circle?.radius (Circle seven)) 7ul)
 &&& chk 2l (U32.eq (Rect?.w (Rect one two)) 1ul)
 &&& chk 3l (U32.eq (Rect?.h (Rect one two)) 2ul)
