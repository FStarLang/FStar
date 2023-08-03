module Records
open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference
module U8 = FStar.UInt8

(* test record mutation and permissions for records of byte refs *)

noeq
type rec2 = {
  r1: R.ref U8.t;
  r2: R.ref U8.t;
}

type rec_repr = {
  v1: U8.t;
  v2: U8.t;
}

let rec_perm (r:rec2) (v:rec_repr)
  : vprop
  = R.pts_to r.r1 full_perm v.v1 **
    R.pts_to r.r2 full_perm v.v2

//Using record syntax directly in Pulse vprops
//leads to strange type inference errors
let mk_rec_repr (v1 v2:U8.t) = { v1=v1; v2=v2 }


// When defining a predicate like rec_perm relating 
// a record and a record_repr, it's convenient to define
// a ghost function to fold the predicate.
// Eventually, it would be nice to auto-generate this 
// ghost function from the predicate definition.
```pulse
ghost
fn fold_rec_perm (r:rec2) (#v1 #v2:erased U8.t)
  requires
    R.pts_to r.r1 full_perm v1 **
    R.pts_to r.r2 full_perm v2
  ensures
    rec_perm r (mk_rec_repr v1 v2)
{
  fold (rec_perm r (mk_rec_repr v1 v2))
}
```

// Then, mutating a single field of the record involves:
```pulse
fn mutate_r2 (r:rec2) (#v:Ghost.erased rec_repr)
  requires rec_perm r v
  ensures exists (v_:rec_repr) .
    rec_perm r v_ ** pure (v_.v2 == 0uy /\ v_.v1 == v.v1)
{
  unfold (rec_perm r v); //1. unfolding the predicate
  r.r2 := 0uy;           //2. working with the fields
  fold_rec_perm r;       //3. folding it back up
  ()
}
```

let mk_rec2 r1 r2 = { r1=r1; r2=r2 }

```pulse
fn alloc_rec (v1 v2:U8.t)
  requires emp
  returns r:rec2
  ensures rec_perm r (mk_rec_repr v1 v2)
{
  let r1 = alloc #U8.t v1;
  let r2 = alloc #U8.t v2; 
  let r = mk_rec2 r1 r2;
  (* Unfortunately, these two rewrites are still needed
     to "rename" r1 and r2 as r.r1 and r.r2 *)
  rewrite (R.pts_to r1 full_perm v1)
      as  (R.pts_to r.r1 full_perm v1);
  rewrite (R.pts_to r2 full_perm v2)
      as  (R.pts_to r.r2 full_perm v2);
  fold_rec_perm r;
  r
}
```

//Some alternate ways to do it, useful test cases

// helpers 

```pulse
fn get_witness (x:R.ref U8.t) (#y:Ghost.erased U8.t)
requires R.pts_to x full_perm y
returns z:Ghost.erased U8.t
ensures R.pts_to x full_perm y ** pure (y==z)
{   
    y
}
```

```pulse
fn unfold_and_fold_manually (r:rec2) (#v:Ghost.erased rec_repr)
  requires rec_perm r v
  ensures exists (v_:rec_repr) . rec_perm r v_
{
  rewrite (rec_perm r v)
    as (R.pts_to r.r1 full_perm v.v1 **
        R.pts_to r.r2 full_perm v.v2);

  rewrite (R.pts_to r.r1 full_perm v.v1 **
           R.pts_to r.r2 full_perm v.v2)
    as (rec_perm r v);
  
  ()
}
```

//Syntax for a field update on v1
let rec_repr_with_v2 (v:rec_repr) (v2:U8.t) = { v1=v.v1; v2=v2 }


```pulse
fn explicit_unfold_witness_taking_and_fold (r:rec2) (#v:Ghost.erased rec_repr)
  requires rec_perm r v
  ensures exists (v_:rec_repr) . rec_perm r v_
{
  rewrite (rec_perm r v)
    as (R.pts_to r.r1 full_perm v.v1 **
        R.pts_to r.r2 full_perm v.v2);

  r.r2 := 0uy;
  let v2_ = get_witness(r.r2);


  rewrite (R.pts_to r.r1 full_perm v.v1 **
           R.pts_to r.r2 full_perm v2_)
    as    (rec_perm r (rec_repr_with_v2 v v2_));
  ()
}
```

```pulse
fn explicit_unfold_slightly_better_witness_taking_and_fold (r:rec2) (#v:Ghost.erased rec_repr)
  requires rec_perm r v
  ensures exists (v_:rec_repr) . rec_perm r v_
{
  rewrite (rec_perm r v)
    as (R.pts_to r.r1 full_perm v.v1 **
        R.pts_to r.r2 full_perm v.v2);

  r.r2 := 0uy;
  with v2_. assert (R.pts_to r.r2 full_perm v2_);

  rewrite (R.pts_to r.r1 full_perm v.v1 **
           R.pts_to r.r2 full_perm v2_)
    as    (rec_perm r (rec_repr_with_v2 v v2_));

  ()
}
```
