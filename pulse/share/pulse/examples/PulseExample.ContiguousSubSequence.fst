module PulseExample.ContiguousSubSequence
#lang-pulse
open Pulse.Lib.Pervasives
module A = Pulse.Lib.Array
module SZ = FStar.SizeT
open FStar.Seq
open Pulse.Lib.BoundedIntegers

let starts_with_at (#a:Type) (i:nat) (s0 s1:seq a) = 
  i + Seq.length s0 <= Seq.length s1 /\
  Seq.slice s1 i (i + Seq.length s0 <: nat) `Seq.equal` s0

let take (#a:Type) (s:seq a) (n:nat { n <= Seq.length s }) = Seq.slice s 0 n

fn check_starts_with_at
      (#t:eqtype)
      (a0 a1:A.array t)
      (len0 len1:SZ.t)
      (j:SZ.t { j < len1 })
      (#s0:erased (Seq.seq t) { Seq.length s0 == SZ.v len0})
      (#s1:erased (Seq.seq t) { Seq.length s1 == SZ.v len1})
      (#p:perm)
requires
  A.pts_to a0 #p s0 **
  A.pts_to a1 #p s1
returns b:bool
ensures
  A.pts_to a0 #p s0 **
  A.pts_to a1 #p s1 **
  pure (b <==> starts_with_at (SZ.v j) s0 s1)
{
  if (len1 - j < len0)
  {
    false
  }
  else
  {
    let mut i0 : SZ.t = 0sz;
    let mut i1 : SZ.t = j;
    let mut break : bool = false;
    while (
      let vb = !break;
      let v0 = !i0;
      let v1 = !i1;
      (not vb &&
       v0 <> len0 &&
       v1 <> len1)
    )
    invariant b . (
      exists* v0 v1 vb.
        pts_to i0 v0 **
        pts_to i1 v1 **
        pts_to break vb **
        A.pts_to a0 #p s0 **
        A.pts_to a1 #p s1 **
        pure (
          v0 <= len0 /\
          v1 <= len1 /\
          (v1 == j + v0) /\
          b == (not vb && v0 <> len0 && v1 <> len1) /\
          starts_with_at (SZ.v j) (take s0 (SZ.v v0)) s1 /\
          (vb ==> v1 <> len1 /\ v0 <> len0 /\ Seq.index s1 (SZ.v v1) =!= Seq.index s0 (SZ.v v0))
        )
    )
    {
      let v0 = !i0;
      let v1 = !i1;
      let t0 = a0.(v0);
      let t1 = a1.(v1);
      if (t0 = t1)
      {
        i0 := v0 + 1sz;
        i1 := v1 + 1sz;
        assert pure (
            take s0 (SZ.v v0 + 1 <: nat) `Seq.equal`
            Seq.snoc (take s0 (SZ.v v0)) t0 
        );
      }
      else
      {
        break := true;
      }
    };
    let v0 = !i0;
    (v0 = len0)
  }
}

fn contiguous_sub_sequence
      (#t:eqtype)
      (a0 a1:A.array t)
      (len0 len1:SZ.t)
      (#s0:erased (Seq.seq t) { Seq.length s0 == SZ.v len0})
      (#s1:erased (Seq.seq t) { Seq.length s1 == SZ.v len1})
      (#p:perm)
requires
  A.pts_to a0 #p s0 **
  A.pts_to a1 #p s1
returns b:bool
ensures
  A.pts_to a0 #p s0 **
  A.pts_to a1 #p s1 **
  pure (b <==> (exists (j:nat { j < SZ.v len1 }).  starts_with_at j s0 s1))
{ 
  let mut j : SZ.t = 0sz;
  let mut found : bool = false;
  while (
    let vb = !found;
    let vj = !j;
    (not vb &&
     vj <> len1)
  )
  invariant b . (
    exists* vj vb.
      pts_to j vj **
      pts_to found vb **
      A.pts_to a0 #p s0 **
      A.pts_to a1 #p s1 **
      pure (
        vj <= len1 /\
        b == (not vb && vj < len1) /\
        (vb ==> SZ.v vj < SZ.v len1 /\ starts_with_at (SZ.v vj) s0 s1) /\
        (~vb ==> forall (j:nat{ j < SZ.v vj }). ~(starts_with_at j s0 s1))
      )
  )
  {
    let vj = !j;
    let at_j = check_starts_with_at a0 a1 len0 len1 vj; 
    if (at_j)
    {
      found := true;
    }
    else
    {
      j := vj + 1sz;
    }
  };
  !found
}