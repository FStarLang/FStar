module RecordOfArrays
open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference
module A = Pulse.Lib.Array
module U8 = FStar.UInt8
module US = FStar.SizeT

// Similar to Records, but with arrays

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
  A.pts_to r.r1 full_perm v.v1 **
  A.pts_to r.r2 full_perm v.v2

//Using record syntax directly in Pulse vprops
//leads to strange type inference errors
let mk_rec_array_repr (v1 v2:Seq.seq U8.t) = { v1=v1; v2=v2 }

```pulse
ghost
fn fold_rec_array_perm (r:rec_array) (#v1 #v2:erased (Seq.seq U8.t))
  requires
    A.pts_to r.r1 full_perm v1 **
    A.pts_to r.r2 full_perm v2
  ensures
    rec_array_perm r (mk_rec_array_repr v1 v2)
{
  fold (rec_array_perm r (mk_rec_array_repr v1 v2))
}
```


// Then, mutating a one of the arrays of the record involves:
```pulse
fn mutate_r2 (r:rec_array) (#v:(v:Ghost.erased rec_array_repr { Seq.length v.v2 > 0 }))
  requires rec_array_perm r v
  ensures exists (v_:rec_array_repr) .
    rec_array_perm r v_ ** pure (v_.v2 `Seq.equal` Seq.upd v.v2 0 0uy /\ v_.v1 == v.v1)
{
  unfold (rec_array_perm r v); //1. unfolding the predicate
  ((r.r2).(0sz) <- 0uy);       //2. working with the fields
  fold_rec_array_perm r;       //3. folding it back up
  ()
}
```

// Some alternate more explicit ways

```pulse
fn get_witness_array (x:A.array U8.t) (#y:Ghost.erased (Seq.seq U8.t))
requires A.pts_to x full_perm y
returns z:Ghost.erased (Seq.seq U8.t)
ensures A.pts_to x full_perm y ** pure (y==z)
{   
    y
}
```

let rec_array_repr_with_v2 (r:rec_array_repr) v2 = {r with v2}

```pulse
fn mutate_rec_get_witness (l:US.t) (r:rec_array) (#v:Ghost.erased rec_array_repr)
  requires (
    rec_array_perm r v **
    pure (US.v l > 0 /\ A.length r.r2 == (US.v l) /\ Seq.length v.v2 == (US.v l))
  )
  ensures exists v_.
    rec_array_perm r v_ **
    pure (Seq.length v.v2 > 0 /\ v_.v2 `Seq.equal` Seq.upd v.v2 0 0uy /\ v_.v1 == v.v1)
{
  rewrite (rec_array_perm r v)
    as (A.pts_to r.r1 full_perm v.v1 **
        A.pts_to r.r2 full_perm v.v2);
  
  ((r.r2).(0sz) <- 0uy);

  let y = get_witness_array (r.r2);   

  rewrite (A.pts_to r.r1 full_perm v.v1 **
           A.pts_to r.r2 full_perm y)
    as    (rec_array_perm r (rec_array_repr_with_v2 v y));
    
  ()
}
```
