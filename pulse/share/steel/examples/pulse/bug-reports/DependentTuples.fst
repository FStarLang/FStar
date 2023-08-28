module DependentTuples
open Pulse.Lib.Pervasives
open Pulse.Lib.Reference
open Pulse.Lib.SpinLock

let exists_n (r:ref nat) : vprop = exists_ (fun n -> pts_to r n)

type tup_t = r:ref nat & lock (exists_n r)
let mk_tup r lk : tup_t = (| r, lk |)

assume
val global_tup : tup_t

#set-options "--print_implicits"

[@@expect_failure]
```pulse
fn tuple (_:unit)
  requires emp
  ensures emp
{
  acquire global_tup._2;
  assert (exists_n global_tup._1);
  unfold exists_n global_tup._1;  // this unfold affects the type of the dependent 
                                  // tuple, so we lost syntactic equality and the 
                                  // following assertion fails
  assert (exists_ (fun n -> pts_to global_tup._1 n));
  admit()
}
```

// the same program with a record instead of a dependent tuple works

noeq
type rec_t = 
{ r:ref nat;
  lk:lock (exists_n r); }

assume
val global_rec : rec_t

```pulse
fn record (_:unit)
  requires emp
  ensures emp
{
  acquire global_rec.lk;
  assert (exists_n global_rec.r);
  unfold exists_n global_rec.r;
  assert (exists_ (fun n -> pts_to global_rec.r n));
  admit()
}
```