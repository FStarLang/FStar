module Pulse.Lib.GhostWitness

open Pulse.Lib.Pervasives

let sqeq (p : Type) (_ : squash p) : erased p =
  FStar.IndefiniteDescription.elim_squash #p ()

let psquash (a:Type u#a) : prop = squash a

```pulse
ghost
fn __ghost_witness (a:Type u#0) (_:squash a)
requires emp
returns i:a
ensures emp
{
  let pf = elim_pure_explicit (psquash a);
  let pf : squash a = FStar.Squash.join_squash pf;
  let i = sqeq a pf;
  let i = reveal i;
  i
}
```
let ghost_witness = __ghost_witness

```pulse
ghost
fn __ghost_witness2 (a:Type u#2) (_:squash a)
requires emp
returns i:a
ensures emp
{
  let pf = elim_pure_explicit (psquash a);
  let pf : squash a = FStar.Squash.join_squash pf;
  let i = sqeq a pf;
  let i = reveal i;
  i
}
```
let ghost_witness2 = __ghost_witness2

```pulse
ghost
fn __ghost_witness_exists (a:Type u#0)
requires pure (exists (x:a). True)
returns i:a
ensures emp
{
  ghost_witness a ();
}
```
let ghost_witness_exists = __ghost_witness_exists

```pulse
ghost
fn __ghost_witness_exists2 (a:Type u#2)
requires pure (exists (x:a). True)
returns i:a
ensures emp
{
  ghost_witness2 a ();
}
```
let ghost_witness_exists2 = __ghost_witness_exists2


// fails
// ```pulse
// fn ghost_witness_exists_star (a:Type u#0)
// requires exists* (x:a). emp
// returns xx:int
// ensures emp
// {
//   with i. _;
// }
// ```
