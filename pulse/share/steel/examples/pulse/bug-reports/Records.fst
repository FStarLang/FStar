module Records
open Pulse.Steel.Wrapper
module R = Steel.ST.Reference
module A = Steel.ST.Array
open Steel.FractionalPermission
open FStar.Ghost
module U8 = FStar.UInt8
module US = FStar.SizeT
module PM = Pulse.Main
module T = FStar.Tactics
module PM = Pulse.Main
open Steel.ST.Util 
open Pulse.Steel.Wrapper


noeq
type rec2 = {
  r1: R.ref U8.t;
  r2: R.ref U8.t;
}

type rec2_repr = {
  v1: U8.t;
  v2: U8.t;
}

let rec2_perm (r:rec2) (v:rec2_repr)
  : vprop = 
  R.pts_to r.r1 full_perm v.v1 `star`
  R.pts_to r.r2 full_perm v.v2


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
fn mutate_ref (r:R.ref U8.t) (x:U8.t) (#v:Ghost.erased U8.t)
  requires R.pts_to r full_perm v
  ensures R.pts_to r full_perm x
{
  r := x;
  ()
}
```


// fails with no error reported, but purports that it succeeds
// when [@@expect_failure] is uncommented
// [@@expect_failure]
```pulse
fn mutate_rec2_get_witness (r:rec2) (#v:Ghost.erased rec2_repr)
  requires rec2_perm r v
  ensures exists (v_:rec2_repr) . rec2_perm r v_
{
  rewrite (rec2_perm r v)
    as (R.pts_to r.r1 full_perm v.v1 `star`
        R.pts_to r.r2 full_perm v.v2);

  mutate_ref r.r2 0uy;
  let v2_ = get_witness(r.r2);

  rewrite (R.pts_to r.r1 full_perm v.v1 `star`
           R.pts_to r.r2 full_perm v2_)
    as `@(rec2_perm r {v with v2=v2_});
  
  ()
}
```

// fails with no error reported, but purports that it succeeds
// when [@@expect_failure] is uncommented
// [@@expect_failure]
```pulse
fn mutate_rec2_get_witness (r:rec2) (#v:Ghost.erased rec2_repr)
  requires rec2_perm r v
  ensures exists (v_:rec2_repr) . rec2_perm r v_
{
  rewrite (rec2_perm r v)
    as (R.pts_to r.r1 full_perm v.v1 `star`
        R.pts_to r.r2 full_perm v.v2);

  mutate_ref r.r2 0uy;
  let v2_ = get_witness(r.r2);

  rewrite (R.pts_to r.r1 full_perm v.v1 `star`
           R.pts_to r.r2 full_perm v2_)
    as `@(rec2_perm r {v with v2=v2_});
  
  ()
}
```

(* 
Code below works!

```pulse
fn get_witness_array (x:A.array U8.t) (#y:Ghost.erased (Seq.seq U8.t))
requires A.pts_to x full_perm y
returns z:Ghost.erased (Seq.seq U8.t)
ensures A.pts_to x full_perm y ** pure (y==z)
{   
    y
}
```

noeq
type rec1_array = {
  r: A.array U8.t;
}

type rec1_array_repr = {
  v: Seq.seq U8.t;
}

```pulse
fn get_witness_rec_arrays (r:rec1_array) (#v:Ghost.erased rec1_array_repr)
  requires A.pts_to r.r full_perm v.v
  ensures exists (v_:Seq.seq U8.t) . A.pts_to r.r full_perm v_
{
  let y = get_witness_array(r.r);
  ()
}
```
*)