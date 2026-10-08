module ExtSpecBinderRec

/// Recursion and the binder a `requires` desugars into.
///
/// A recursive definition is extracted with its own name already in scope, so
/// whatever extraction decides about its binders has to hold at the recursive
/// call in its own body as well as at every call outside it. Mutual recursion
/// has to agree across the whole group.
///
/// See ExtSpecBinderArity for the basic invariant and issue #4650.

module I32 = FStar.Int32

let chk (n:I32.t) (b:bool{b}) : I32.t = if b then 0l else n
let ( &&& ) (a b : I32.t) : I32.t = if a = 0l then b else a

(* Top-level names, so extraction cannot constant-fold the calls; see
   README.md. *)
let five : I32.t = 5l
let six  : I32.t = 6l

/// A precondition on a recursive function: the binder is dropped at the
/// definition *and* at the recursive call in the body.
let rec countdown (x:I32.t)
  : Pure I32.t (requires I32.v x >= 0) (ensures fun r -> I32.v r == 0)
               (decreases (I32.v x))
  = if I32.eq x 0l then 0l else countdown (I32.sub x 1l)

/// Mutual recursion, with a precondition on each side.
let rec even_down (x:I32.t)
  : Pure I32.t (requires I32.v x >= 0) (ensures fun r -> I32.v r == 0)
               (decreases (I32.v x))
  = if I32.eq x 0l then 0l else odd_down (I32.sub x 1l)
and odd_down (x:I32.t)
  : Pure I32.t (requires I32.v x >= 0) (ensures fun r -> I32.v r == 0)
               (decreases (I32.v x))
  = if I32.eq x 0l then 0l else even_down (I32.sub x 1l)

/// A user-written `squash` binder on a recursive function survives, and so it
/// has to be passed again at the recursive call.
let rec kept_rec (#p : squash True) (x:I32.t)
  : Pure I32.t (requires I32.v x >= 0) (ensures fun r -> I32.v r == 0)
               (decreases (I32.v x))
  = if I32.eq x 0l then 0l else kept_rec #() (I32.sub x 1l)

/// One of each in the same group: `kept` keeps its binder and `dropped` loses
/// one, and they call each other.
let rec kept_mut (#p : squash True) (x:I32.t)
  : Pure I32.t (requires I32.v x >= 0) (ensures fun r -> I32.v r == 0)
               (decreases (I32.v x))
  = if I32.eq x 0l then 0l else dropped_mut (I32.sub x 1l)
and dropped_mut (x:I32.t)
  : Pure I32.t (requires I32.v x >= 0) (ensures fun r -> I32.v r == 0)
               (decreases (I32.v x))
  = if I32.eq x 0l then 0l else kept_mut #() (I32.sub x 1l)

let main () : I32.t =
     chk 1l (I32.eq (countdown five) 0l)
 &&& chk 2l (I32.eq (even_down five) 0l)
 &&& chk 3l (I32.eq (odd_down six) 0l)
 &&& chk 4l (I32.eq (kept_rec #() five) 0l)
 &&& chk 5l (I32.eq (kept_mut #() five) 0l)
 &&& chk 6l (I32.eq (dropped_mut six) 0l)
