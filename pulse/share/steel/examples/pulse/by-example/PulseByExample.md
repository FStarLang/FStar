# Pulse By Example

Pulse is a syntax extension and typechecker extension of F*. 
A pulse program is embedded in an F* program, delimited by the syntax extension notation ` ```pulse ... ``` `. 
The first code snippet demonstrates an embedded Pulse program `five`, which produces the integer 5. 
The rest of the file is a normal F* program, and it can even invoke an embedded Pulse program -- see line X. 

Pulse programs accept 1 or more arguments, where the `unit` type can be used to thunk a computation. 
A Pulse program has a precondition (`requires ...`), postcondition (`ensures ...`), and optional return type. 
Pulse is a separation logic, so its propositions are separation logic propositions. 
You can read about the capabilities and operations that a separation logic offers [here](TODO). 

Returning to our code snippet, the separation logic proposition `emp` means that the program does not own any resources or have any knowledge. 
The keywork `pure` allows us to write a pure F* proposition inside a Pulse proposition. 
So the Pulse program `five` begins with no resources/knowledge and returns with the knowledge that the return value is logically equal to 5. 

```ocaml
module PM = Pulse.Main
open Pulse.Lib.Core

let my_list : list int = [1;2;3]

```pulse
fn five (_:unit)
  requires emp
  returns n:int
  ensures  pure (n == 5)
{ 
  5
}
``
let my_int = five ()
```

Let's make things more interesting. 
The next code snippet swaps the values of two integer references. 
A `ref` is a heap reference to some data, in this case integers. 
The precondition is a separation logic conjunction of ownership of two references pointing to some values `'n1` and `'n2`. 
A tick at the beginning of a variable name means the variable is an implicitly inferred logical variable. 
A logical variable cannot be used in a Pulse program outside of the specification (such as pre/postconditions, invariants, and assertions). 
After declaring an implicit logical variable, like `'n1` on line X, it can be referenced in later parts of the specification, like in the postcondition on line X. 
The postcondition says that the values of the two references are swapped. 

The program body demonstrates Pulse syntax for 
- immutable local variables: `let v1 = ...`
- reference read: `!r1`
- reference write: `r1 := ...`

```ocaml
open Pulse.Lib.Reference
module R = Pulse.Lib.Reference

``pulse
fn ref_swap (r1 r2:ref int)
  requires R.pts_to r1 'n1 
        ** R.pts_to r2 'n2
  ensures  R.pts_to r1 'n2
        ** R.pts_to r2 'n1
{
  let v1 = !r1;
  let v2 = !r2;
  r1 := v2;
  r2 := v1
}
``
```

You've seen references; now we'll introduce arrays. 
But first, a note on integers. 
In the following code snippet, we use non-primitive integers for the first time: `FStar.SizeT` is a module of machine integers. 
The module `Pulse.Class.BoundedIntegers` offers arithmetic operations on various types of bounded integers, including `FStar.SizeT` and `FStar.U32`. 
The bounded integer class overloads arithmetic operators, like `<`, to allow, e.g., the comparison over `SizeT`s `i < n` on line X and comparison over `nat`s `k < v n` on line X (`v` elaborates to `SZ.v` and converts a machine integer to a nat). 

Let's get back to arrays. 
The Pulse program `arr_swap` swaps the values at indices `i` and `j` in an input array. 
Notice that the array `a` is type-polymetric by the type parameter `#t`. 
The `#` notation means a variable is implicit, so it does not need to be specified if Pulse can infer it. 
The precondition specifies logical requirements on the values of `i` and `j` relative to the length of the array `n`. 

The postcondition uses an F* quantifier, `exists`, to declare that upon function return, the input array `a` has a new underlying sequence `s` that satisfies a whole bunch of logical propositions which constrain that the new sequence `s` is the same as the original sequence `'s0` except that the values at positions `i` and `j` are swapped. 
Study the pure part of the postcondition to convince yourself that it faithfully constraints this property! 

The program body demonstrates Pulse syntax for 
- array read: `a.(i)`
- array write: `(a.(i) <- ...)`

```ocaml
open Pulse.Lib.Array
module A = Pulse.Lib.Array
module SZ = FStar.SizeT
open Pulse.Class.BoundedIntegers

``pulse
fn arr_swap (#t:Type0) (n i j:SZ.t) (a:larray t (v n))
  requires 
    A.pts_to a 's0 **
    pure (Seq.length 's0 == v n /\ i < n /\ j < n)
  ensures exists s. 
    A.pts_to a s **
    pure (Seq.length 's0 == v n /\ Seq.length s == v n /\ i < n /\ j < n
       /\ (forall (k:nat). k < v n /\ k <> v i /\ k <> v j ==> Seq.index 's0 k == Seq.index s k)
       /\ Seq.index 's0 (v i) == Seq.index s (v j)
       /\ Seq.index 's0 (v j) == Seq.index s (v i))
{
  let vi = a.(i);
  let vj = a.(j);
  (a.(i) <- vj);
  (a.(j) <- vi);
}
``
```

The last example in this tutorial introduces looping. 
The Pulse program `max` computes the maximum value in an array of `nat`s. 
The first thing to note is the implicit argument `#'p` to `A.pts_to`. 
The `pts_to` proposition in the array and reference libraries accepts an *optional* implicit argument of type `perm`. 
This argument specifies the permission that the reference has over the value, e.g. full or half permission. 
Refer back to the separation logic tutorial for explanation of permissions. 
In the `max` function, we do not mutate the array `a` so we do not need full permission on the array. 
Thus, we infer the permission using a backticked variable name `'p` instead of omitting the permission argument of `pts_to`, which would default to enforcing full permission. 

The rest signature of `max` says that the function returns a `nat` and the value of this nat is greater than or equal to every value in the array. 
Considering only the non-specification aspects of the body (lines X-X and X-X), it looks like a canonical `max` program that you might write in C. 
The body demonstrates local *mutable* variables in Pulse, which can be writetn to / read from just like non-local references. 
The interesting piece is the loop invariant in lines X-X. 
A loop invariant is true before entering the loop, after each loop iteration, and upon exiting the loop. 
In other words, it is an aptly-named *invariant* of the program. 
If the loop invariant is cleverly crafted, it should help prove the postcondition of the program. 

Let's examine the loop invariant in the `max` program. 
The syntax `invariant` sets up the loop invariant, and the variable `b` declares the name of the loop condition. 
Once `b` is false, we exit the loop. 
We specify the value of `b` on line X in the pure part of the invariant. 
Next, notice the existentially quantified variables `vi` and `vmax`. 
These are used in the ownership part of the loop invariant, which says that we own the array `a` which still points to `'s` and the references `i` and `max` which point to some values as well. 
Finally, the interesting part of the invariant is the pure part, where we specify how logical values relate back to the references in memory. 
Here, we specify that every value in the sequence up to the `vi`th value is less than or equal to `vmax`. 
Convince yourself that this is true upon entering the loop (look at the initial values of `i` and `max`) and after each loop iteration (examine the loop body). 
Finally, upon exiting the loop we know that the value of reference `i` equals `n` and line X in the loop invariant is true, which implies line X in the postcondition. 
We have convinced ourselves of these properties via the assertions on lines X-X. 
Hooray! 

```ocaml
``pulse
fn max (n:SZ.t) (a:larray nat (v n))
  requires A.pts_to a #'p 's ** pure (Seq.length 's == v n)
  returns r:nat
  ensures A.pts_to a #'p 's
       ** pure (Seq.length 's == v n
             /\ (forall (i:nat). i < v n ==> Seq.index 's i <= r))
{
  let mut i = 0sz;
  let mut max = 0;
  while (let vi = !i; (vi < n))
  invariant b. exists (vi:SZ.t) (vmax:nat).
    A.pts_to a #'p 's **
    R.pts_to i vi **
    R.pts_to max vmax **
    pure (vi <= n /\ Seq.length 's == v n
       /\ (forall (j:nat). j < v vi ==> Seq.index 's j <= vmax)
       /\ b == (vi < n))
  {
    let vi = !i;
    let vmax = !max;
    let v = a.(vi);
    i := vi + 1sz;
    if (v > vmax) {
      max := v;
    }
  };
  with vi. assert (R.pts_to i vi);
  assert (pure (vi == n));
  assert (pure (forall (j:nat). j < v n ==> Seq.index 's j <= vmax));
  vmax
}
``
```

In this tutorial, you have seen custom Pulse proof syntax, like
- `requires`, `ensures`
- `pure`
- `exists` and `forall` in specifications
- `invariant`
- `assert`
- `with ... assert ...`

and sequential Pulse syntax, like
- local mutable and immutable references
- while loop
- if statement
- read/write of references and arrays

There is much more to Pulse! 
Including 
- match statements
- parallel blocks
- `fold` and `unfold` proof syntax