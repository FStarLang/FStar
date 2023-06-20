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

(* defining rec_perm directly cause Core to prove `v.v1 == u.v1` by proving `v == u` which is bad.
  This indirection prevents F* from unfolding it and that works around the problem.
  Should fix this in Core.
*)
assume
val rec_perm (r:rec2) (v:rec_repr)
  : vprop

assume
val rec_perm_definition (r:rec2) (v:rec_repr)
  : Lemma 
    (ensures rec_perm r v == 
      (R.pts_to r.r1 full_perm v.v1 `star`
       R.pts_to r.r2 full_perm v.v2))
    [SMTPat (rec_perm r v)]

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


// this works without the introduction, but pulse can't 
// infer the existential unless v is provided as a witness
// and fails with a mysterious error: "match_typ: t2 is a uvar"
[@@expect_failure]
```pulse
fn rec_get_witness (r:rec2) (#v:Ghost.erased rec_repr)
  requires rec_perm r v
  ensures exists (v_:rec_repr) . rec_perm r v_
{
  rewrite (rec_perm r v)
    as (R.pts_to r.r1 full_perm v.v1 `star`
        R.pts_to r.r2 full_perm v.v2);

  introduce exists (v_:Ghost.erased rec_repr). (
    pure (v == v_)
  ) with _;

  rewrite (R.pts_to r.r1 full_perm v.v1 `star`
           R.pts_to r.r2 full_perm v.v2)
    as (rec_perm r v);
  
  ()
}
```

let rec_repr_with_v2 (v:rec_repr) (v2:U8.t) = { v1=v.v1; v2=v2 }

// error says: could not infer implicit arguments in rec_perm on line 94,
// but this fcn has no implicit args. also, this fcn errors at a different
// line (88) when the remainder of this file is *not* commented out... strange
[@@expect_failure]
```pulse
fn mutate_rec_get_witness (r:rec2) (#v:Ghost.erased rec_repr)
  requires rec_perm r v
  ensures exists (v_:rec_repr) . rec_perm r v_
{
  rewrite (rec_perm r v)
    as (R.pts_to r.r1 full_perm v.v1 `star`
        R.pts_to r.r2 full_perm v.v2);

  mutate_ref r.r2 0uy;
  let v2_ = get_witness(r.r2);


  // assert_ (R.pts_to r.r1 full_perm v.v1 `star`
  //          R.pts_to r.r2 full_perm v2_);

  rewrite (R.pts_to r.r1 full_perm v.v1 `star`
           R.pts_to r.r2 full_perm v2_)
    as    (rec_perm r (rec_repr_with_v2 v v2_));
  ()
}
```


(* same experiments but with records of arrays instead of byte refs *)

noeq
type rec_array = {
  r1: A.array U8.t;
  r2: A.array U8.t;
}

type rec_array_repr = {
  v1: Seq.seq U8.t;
  v2: Seq.seq U8.t;
}

let rec_array_perm (r:rec_array) (v:rec_array_repr)
  : vprop = 
  A.pts_to r.r1 full_perm v.v1 `star`
  A.pts_to r.r2 full_perm v.v2

// helpers 

```pulse
fn get_witness_array (x:A.array U8.t) (#y:Ghost.erased (Seq.seq U8.t))
requires A.pts_to x full_perm y
returns z:Ghost.erased (Seq.seq U8.t)
ensures A.pts_to x full_perm y ** pure (y==z)
{   
    y
}
```

```pulse
fn mutate_array (l:US.t) (a:(a:A.array U8.t{ US.v l == A.length a }))
                (#s:(s:Ghost.erased (Seq.seq U8.t){ US.v l > 0 /\ US.v l == Seq.length s }))
   requires A.pts_to a full_perm s
   ensures A.pts_to a full_perm (Seq.upd s 0 0uy)
{
  (a.(0sz) <- 0uy)
}
```


// same failure as mutate_rec_get_witness. suprrising that getting
// an array witness works (line 168) because the same currently 
// fails in L0Core.fst:232 ...
[@@expect_failure]
```pulse
fn mutate_rec_get_witness (l:US.t) (r:rec_array) (#v:Ghost.erased rec_array_repr)
  requires (
    rec_array_perm r v `star`
    pure (US.v l > 0 /\ A.length r.r2 == (US.v l) /\ Seq.length v.v2 == (US.v l))
  )
  ensures (
    A.pts_to r.r1 full_perm v.v1 `star`
    exists (v_:Seq.seq U8.t) . A.pts_to r.r2 full_perm v_
  )
{
  rewrite (rec_array_perm r v)
    as (A.pts_to r.r1 full_perm v.v1 `star`
        A.pts_to r.r2 full_perm v.v2);
  
  mutate_array l r.r2;
  let y = get_witness_array (r.r2); (* this works! *)

  rewrite (A.pts_to r.r1 full_perm v.v1 `star`
           A.pts_to r.r2 full_perm y)
    as `@(rec_array_perm r {v with v2=y});
  ()
}
```
