module ExtSpecBinderClosures

/// The binder a `requires` desugars into, at higher order.
///
/// An arrow with a precondition can be the type of an *argument*, of a
/// result, of a local `let`, or of a field. Each of those is a separate place
/// for the two sides to disagree about how many arguments the arrow takes,
/// and the one written as a type abbreviation is the shape that actually
/// broke in issue #4650.
///
/// This needs closures, which the C and Rust backends reject ("Warning 11:
/// this expression is not Low*"), hence the NO_ entries in the Makefile --
/// the same ones ExtBoolHigherOrder carries.
///
/// See ExtSpecBinderArity for the basic invariant.

module I32 = FStar.Int32

let chk (n:I32.t) (b:bool{b}) : I32.t = if b then 0l else n
let ( &&& ) (a b : I32.t) : I32.t = if a = 0l then b else a

(* Top-level names, so extraction cannot constant-fold the calls; see
   README.md. *)
let three  : I32.t = 3l
let three' : I32.t = 3l   (* a second copy: see ExtSpecBinderArity *)
let four   : I32.t = 4l
let seven  : I32.t = 7l

/// --- an arrow with a precondition, as the type of an argument ---

let apply (f : (x:I32.t -> Pure I32.t (requires I32.v x >= 0) (ensures fun r -> r == x)))
          (x:I32.t{I32.v x >= 0})
  : r:I32.t{r == x}
  = f x

/// The same arrow written as an abbreviation.
type pos_fn = x:I32.t -> Pure I32.t (requires I32.v x >= 0) (ensures fun r -> r == x)

let apply_abbrev (f:pos_fn) (x:I32.t{I32.v x >= 0}) : r:I32.t{r == x} = f x

let idp : pos_fn = fun x -> x

/// Defined by naming another function rather than by an abstraction.
/// Extraction handles that in a branch of its own, which has no abstraction
/// to read the binders off and has to take them from the type instead.
let alias : pos_fn = idp

/// An arrow with a precondition as a *result* type, returned by a closure
/// that captures `y`.
type const_fn (y:I32.t) =
  x:I32.t -> Pure I32.t (requires I32.v x >= 0) (ensures fun r -> r == y)

let constantly (y:I32.t) : const_fn y = fun _ -> y

/// --- a user-written `squash` binder in the same positions: kept ---

type kept_fn = #p:squash True -> x:I32.t -> r:I32.t{r == x}

let apply_kept (f:kept_fn) (x:I32.t) : r:I32.t{r == x} = f #() x

let idk : kept_fn = fun #_ x -> x

/// --- partial application ---

/// `adder`'s dropped binder trails both explicit ones, so applying it to one
/// argument has to stop in front of that binder rather than through it.
let adder (x:I32.t) (y:I32.t)
  : Pure I32.t (requires I32.v x >= 0 /\ I32.v x <= 10 /\ I32.v y >= 0 /\ I32.v y <= 10)
               (ensures fun r -> I32.v r == I32.v x + I32.v y)
  = I32.add x y

let add_three = adder three

/// --- local definitions ---

/// Local `let`s are extracted by a different path than top-level ones, and
/// have to drop and keep exactly the same binders.
let nested (x:I32.t{I32.v x >= 0 /\ I32.v x <= 10}) : r:I32.t{I32.v r == I32.v x} =
  let loc_pre (y:I32.t) : Pure I32.t (requires I32.v y >= 0) (ensures fun r -> r == y) = y in
  let loc_kept (#p : squash True) (y:I32.t) : r:I32.t{r == y} = y in
  let loc_fn : pos_fn = fun y -> y in
  I32.add (loc_pre x) (I32.sub (loc_kept #() (loc_fn x)) x)

/// --- carried inside data ---

noeq type box = | Box : pos_fn -> box
let unbox (b:box) (x:I32.t{I32.v x >= 0}) : r:I32.t{r == x} = let Box f = b in f x

noeq type ops = { op : pos_fn }
let use_ops (o:ops) (x:I32.t{I32.v x >= 0}) : r:I32.t{r == x} = o.op x

let main () : I32.t =
     chk 1l (I32.eq (apply idp three) three')
 &&& chk 2l (I32.eq (apply_abbrev idp three) three')
 &&& chk 3l (I32.eq (apply_abbrev alias three) three')
 &&& chk 4l (I32.eq (constantly four three) four)
 &&& chk 5l (I32.eq (apply_kept idk three) three')
 &&& chk 6l (I32.eq (add_three four) seven)
 &&& chk 7l (I32.eq (nested three) three')
 &&& chk 8l (I32.eq (unbox (Box idp) three) three')
 &&& chk 9l (I32.eq (use_ops ({ op = idp }) three) three')
