module TestNd

(* Tests for the [Nd] (nondeterministic, but terminating) effect, which
   sits strictly between [Tot] and [Dv]. *)

assume val f : unit -> Nd int

(* Nd computations are nondeterministic: two calls need not agree. *)
[@@expect_failure [19]]
let nondet () : Nd unit =
  let x = f () in
  let y = f () in
  assert (x == y)

(* ... and nothing at all is known about the result. *)
[@@expect_failure [19]]
let nospec () : Nd unit =
  let x = f () in
  assert (x == 0)

(* Nd computations terminate, so recursion is subject to a termination
   check (unlike in Dv). *)
[@@expect_failure [19]]
let rec loop (x:int) : Nd int = loop x

let rec count (n:nat) : Nd int =
  if n = 0 then f () else count (n - 1)

(* Since Nd terminates, it may be used at the top level: no
   "top-level let-bindings must be total" warning (240/272 are errors in
   this directory) and no `nonempty` obligation. *)
let global : int = f ()

(* Even at a type that is not obviously inhabited. *)
assume val t : Type
assume val g : unit -> Nd t
let global2 : t = g ()

(* Tot ⊆ Nd *)
let pure_into_nd (x:int) : Nd int = x + 1

(* Nd ⊆ Dv *)
let nd_into_dv () : Dv int = f ()

(* Nd ⊆ Tac *)
#push-options "--warn_error -274" // 'Arith.fst' in this directory shadows FStar.Tactics.Arith
let nd_into_tac () : FStar.Tactics.Effect.Tac int = f ()
#pop-options

(* But Dv ⊄ Nd *)
assume val h : unit -> Dv int
[@@expect_failure]
let dv_into_nd () : Nd int = h ()

(* Nd is not erasable: GTot does not flow into it. *)
assume val gh : unit -> GTot int
[@@expect_failure]
let ghost_into_nd () : Nd int = gh ()

(* An arrow into Nd lives in the universe of its result (as for Tot, and
   unlike Dv, whose arrows are all in Type0 since they are
   proof-irrelevant). *)
let _ : Type u#1 = unit -> Nd (Type u#0)

(* A top-level Nd binding is masked: it denotes *some* value of its type, but
   not a function of its definition. Two identical definitions must therefore
   not be provably equal, or a nondeterministic allocator used to define two
   globals would identify them. See issue #4534. *)
let nd_global1 = f ()
let nd_global2 = f ()

[@@expect_failure [19]]
let _ = assert (nd_global1 == nd_global2)

(* ...but a global is equal to itself, and its type is still known. *)
let _ = assert (nd_global1 == nd_global1)
let _ : int = nd_global1

(* The definition is also not unfolded by the normalizer. *)
let _ = assert_norm (nd_global1 == nd_global1)
