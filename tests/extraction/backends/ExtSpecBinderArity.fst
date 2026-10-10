module ExtSpecBinderArity

/// A `requires` clause desugars into a trailing implicit `squash` binder.
/// Extraction drops *that* binder and keeps a `squash` binder the user wrote,
/// and the definition and every call site have to agree about which is which
/// -- otherwise an argument is silently lost.
///
/// Issue #4650: the test used to be the *syntax* of the binder's type, so the
/// same `squash` reached through a type abbreviation was classified one way
/// in a definition and the other way at its call site, and the generated code
/// did not even typecheck. The binder a `requires` produces now carries a
/// `Prims.spec_binder` attribute, and nothing else is dropped.
///
/// Everything here is first order and directly applied, so it runs on every
/// backend. Closures are in ExtSpecBinderClosures, recursion in
/// ExtSpecBinderRec, effects in ../SpecBinderEffects.fst.

module I32 = FStar.Int32

let chk (n:I32.t) (b:bool{b}) : I32.t = if b then 0l else n
let ( &&& ) (a b : I32.t) : I32.t = if a = 0l then b else a

(* Operands are top-level names so that extraction cannot constant-fold the
   calls below; see README.md. *)
let three  : I32.t = 3l
let three' : I32.t = 3l   (* a second copy: comparing a result against the very
                             constant it came from collapses, once the callee
                             is inlined, to a self-comparison, which the C
                             compiler rejects under -Wtautological-compare *)
let four   : I32.t = 4l
let seven  : I32.t = 7l

/// --- the binder a `requires` desugars into is dropped ---

let pre1 (x:I32.t) : Pure I32.t (requires I32.v x >= 0) (ensures fun r -> r == x) = x

let pre2 (x:I32.t) (y:I32.t)
  : Pure I32.t (requires I32.v x >= 0 /\ I32.v y >= 0 /\ I32.v x + I32.v y < 2147483648)
               (ensures fun r -> I32.v r == I32.v x + I32.v y)
  = I32.add x y

/// The precondition mentions an earlier binder, so the dropped binder's type
/// really does depend on the binders in front of it.
let pre_dep (x:I32.t) : Pure I32.t (requires I32.v x == 3) (ensures fun r -> I32.v r == 3) = x

/// Declared by a `val` and defined separately. Extraction then reads the
/// signature off the `val` and the definition off the `let`, which is a
/// different path through `extract_lb_sig` than a self-annotated definition.
val pre_val : x:I32.t -> Pure I32.t (requires I32.v x >= 0) (ensures fun r -> r == x)
let pre_val x = x

/// --- a `squash` binder the user wrote is an ordinary argument ---

let kept_imp (#p : squash True) (x:I32.t) : I32.t = x

/// The same binder behind a type abbreviation. This is the shape that used to
/// give the definition and the call site different answers.
type proof = squash True
let kept_abbrev (#p : proof) (x:I32.t) : I32.t = x

let kept_expl (p : squash True) (x:I32.t) : I32.t = x

/// Both at once: `p` survives and the binder behind `x` does not, so this is
/// a two-argument function.
let mixed (#p : proof) (x:I32.t)
  : Pure I32.t (requires I32.v x >= 0) (ensures fun r -> r == x) = x

let main () : I32.t =
     chk 1l (I32.eq (pre1 three) three')
 &&& chk 2l (I32.eq (pre2 three four) seven)
 &&& chk 3l (I32.eq (pre_dep three) three')
 &&& chk 4l (I32.eq (pre_val three) three')
 &&& chk 5l (I32.eq (kept_imp #() three) three')
 &&& chk 6l (I32.eq (kept_abbrev #() three) three')
 &&& chk 7l (I32.eq (kept_expl () three) three')
 &&& chk 8l (I32.eq (mixed #() three) three')
