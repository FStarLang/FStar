module PulseByExample

module PM = Pulse.Main
open Pulse.Lib.Core

(*   
  Let's address each component of this simple Pulse function. 

  - The 3 backtick notation specifies that the code inside is written in an 
    F* syntax extension called Pulse. 

  - A Pulse function takes an arbitrary number of arguments, greater than zero. 
    The unit type is useful for taking no arguments.

  - A Pulse function needs a precondition (requires ...) and a postcondition
    (ensures ...). Pulse attempts to prove the postcondition given the
    precondition and the body computation. If it fails to do so, we say "the
    Pulse checker failed".

  - If the function has a non-unit return, then the return type must be specified. 
    (line 22 is not necessary in the following example because we return unit)
*)

```pulse
fn do_nothing (_:unit)
  requires emp
  returns _:unit
  ensures  emp
{
  // emp is the empty assertion. It is vacuously true. 
  ()
}
```

open Pulse.Lib.Reference
module R = Pulse.Lib.Reference

(* 
to cover 

- primitives 

write a program that has
- heap reference (alloc, write, read, free)
- local reference (write, read)
- erased values, implicit values
- exists/forall in spec

- introduce exists
- with... assert...
- fold/unfold
- with... unfold... (?)
*)

```pulse
fn prims (_:unit)
  requires emp
  ensures emp
{
  let boolean = true;
  let integer = 0;
  // assert (exists_ (fun (n:int) -> pure (integer == n)));
  // assert (exists_ (fun (n:nat) -> pure (integer == n)));
  let unit = ();
  let pair = (boolean,integer);
  let string = "hello";
  ()
}
```

```pulse
fn mmut (_:unit)
  requires emp
  ensures emp
{
  let mut b = true;
  b := false;
}
```

open FStar.Ghost
open Steel.FractionalPermission

(*
Heap reference read/write
Implicit, erased values
*)
```pulse
fn inc (r:R.ref int) (#v:erased int)
  requires R.pts_to r full_perm v
  ensures R.pts_to r full_perm (v+1)
{
  let vr = !r;
  assert (pure(vr == v));
  r := vr + 1;
}
```

```pulse
fn swap (r:R.ref int) (#v:erased int)
  requires R.pts_to r full_perm v
  ensures R.pts_to r full_perm (v+1)
{
  let vr = !r;
  assert (pure(vr == v));
  r := vr + 1;
}
```

// ```pulse
// fn silly_example (r1 r2:R.ref nat) (#v1:erased nat)
//   requires (
//     R.pts_to r1 full_perm v1 **
//     exists v2. R.pts_to full_perm v2
//   )
//   returns n:nat
//   ensures (
//     R.pts_to r0 full_perm n **
//     exists r. R.pts_to r full_perm (v0+1)
//   )
// {
//   let n = get_nat 0;
//   let val_r1 = !r1;
//   let val_r2 = !r2;

//   if (val_r1 > n) {
//     r1 := n;
//   }
//   let val_r0 = !r0;
//   let n = 5;

//   r0 := n;

//   let mut new_local_ref = 0;
//   new_local_ref := val_r0;

//   let new_heap_ref = alloc 0;
//   new_heap_ref := val_r0 + 1;

//   n
// }
// ```

// ```pulse
// fn local_ref (_:unit)
//   requires emp
//   ensures emp
// {
//   let mut local_ref = 0;
//   local_ref := 1;
// }
// ```

// ```pulse
// fn heap_ref (_:unit)
//   requires emp
//   ensures emp
// {
//   let local_ref = alloc 0;
//   local_ref := 1;
//   free local_ref;
// }
// ```

open Pulse.Lib.Array.Core
module A = Pulse.Lib.Array.Core

// ```pulse
// fn read_array (#t:Type0) 
//   (a:A.array t) 
//   (#s:erased (Seq.seq t)) 
//   (#p:perm)
//   requires A.pts_to a p s ** pure(A.length a > 0)
//   ensures  A.pts_to a p s
// {
//   let v0 = a.(0sz);
//   ()
// }
// ```

// ```pulse
// fn read_array_refined (#t:Type0) 
//   (l:pos) 
//   (a:(a:A.array t{A.length a == l})) 
//   (#s:erased (Seq.seq t)) 
//   (#p:perm)
//   requires A.pts_to a p s
//   ensures  A.pts_to a p s
// {
//   let v0 = a.(0sz);
//   ()
// }
// ```

// ```pulse
// fn write_array (#t:Type0) 
//   (l:pos) 
//   (a:(a:A.array t{A.length a == l}))
//   (v:t)
//   (#s:erased (Seq.seq t))
//   (#p:perm)
//   requires A.pts_to a p s
//   ensures  exists s_. A.pts_to a p s_
// {
//   (a.(0sz) <- v);
//   ()
// }
// ```

(* 


- loop invariants (while), other control flow (if, match)
- then, a program that brings everything up to this point together
  - maybe fibo with primitive types then introduce bounded integers
  - forall

- arrays

- some more mature example (e.g. sorting alg)

- some simple record data structure along with a library of functions on this DS
  (e.g. library of functions on 2D points)

- build up to explaining the pulse implementation of lpht? -- emphasis on connecting
  pure implementation to imperative code
- pulse linked list? -- more traditional sep logic example 

- concurrency, e.g. par incr of a ctr


*)