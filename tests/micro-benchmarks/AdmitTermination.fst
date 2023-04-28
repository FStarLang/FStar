module AdmitTermination

// blah not used recursively, silence
#set-options "--warn_error -328"

[@@admit_termination]
let rec f1 (x:nat) : nat = f1 x

(* Even admitting termination, this is not type
correct. *)
[@@expect_failure [19]; admit_termination]
let rec f2 (x:nat) : nat = f2 x - 1

[@@admit_termination]
let rec blah () = ()
and f (x:int) : int = f x

[@@admit_termination]
let rec g (x:int) : int = g x

val h : int -> int
[@@admit_termination]
let rec h (x:int) : int = h x

[@@admit_termination]
val i : int -> int

let rec i (x:int) : int = i x

let top1 () =
  let rec blah () = ()
  [@@admit_termination]
  and f (x:int) : int = f x
  in ()

(* This admits the termination of blah, not of f! *)
[@@expect_failure [19]]
let top2 () =
  [@@admit_termination]
  let rec blah () = ()
  and f (x:int) : int = f x
  in ()

(* Note that the admit_termination attribute applies to
*calls* to the admitted binding, and not the definition
of the binding. The difference is significant in mutual
recursion, see ahead. *)

(* Works: the body of f respects the termination argument
for g. Since we admit the termination of f, the body of g
has no obligation, and verifies. *)
let top3 () =
  [@@admit_termination]
  let rec f (x:pos) : int = g (x-1)
  and g (x:nat) : int = f (x+1)
  in ()

(* Fails: the body of g does not respect the termination
argument for f, which is not admitted. *)
[@@expect_failure [19]]
let top4 () =
  let rec f (x:pos) : int = g (x-1)
  [@@admit_termination]
  and g (x:nat) : int = f (x+1)
  in ()
