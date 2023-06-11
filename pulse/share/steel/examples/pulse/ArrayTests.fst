module ArrayTests
module T = FStar.Tactics
module PM = Pulse.Main
open Steel.ST.Util 
open Steel.ST.Array
open Steel.FractionalPermission
open FStar.Ghost
module U32 = FStar.UInt32
open Pulse.Steel.Wrapper
module A = Steel.ST.Array
module US = FStar.SizeT


#push-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection -Steel.ST.Effect'"

```pulse
fn array_of_zeroes (n:US.t)
   requires emp
   returns a: array U32.t
   ensures (
    A.pts_to a full_perm (Seq.create (US.v n) 0ul) `star`
    pure (is_full_array a /\ A.length a == US.v n)
  )
{
   let a = new_array 0ul n;
   a
}
```

//this is not a recommended way to do this, since s is not erased, but it works
```pulse
fn read_at_offset_0 (#t:Type0) (a:array t) (i:US.t) (#p:perm) (#s:Seq.seq t)
   requires (A.pts_to a p s `star`
             pure (US.v i < A.length a \/ US.v i < Seq.length s))
   returns x:t
   ensures (
      A.pts_to a p s `star`
      pure (Seq.length s == A.length a /\
            US.v i < Seq.length s /\
            x == Seq.index s (US.v i))
   )
{
   let x = a.(i);
   x
} 
```

```pulse
fn read_at_offset_poly (#t:Type0) (a:array t) (i:US.t) (#p:perm) (#s:Ghost.erased (Seq.seq t))
   requires (A.pts_to a p s `star`
             pure (US.v i < A.length a \/ US.v i < Seq.length s))
   returns x:t
   ensures (
      A.pts_to a p s `star`
      pure (Seq.length s == A.length a /\
            US.v i < Seq.length s /\
            x == Seq.index s (US.v i))
   )
{
   let x = a.(i);
   x
} 
```

```pulse
fn read_at_offset (a:array U32.t) (i:US.t) (#p:perm) (#s:Ghost.erased (Seq.seq U32.t))
   requires (A.pts_to a p s `star`
             pure (US.v i < A.length a \/ US.v i < Seq.length s))
   returns x:U32.t
   ensures (
      A.pts_to a p s `star`
      pure (Seq.length s == A.length a /\
            US.v i < Seq.length s /\
            x == Seq.index s (US.v i))
   )
{
   let x = a.(i);
   x
} 
```

assume
val test_array_access
  (#t: Type)
  (a: A.array t)
  (i: US.t)
  (#s: Ghost.erased (Seq.seq t) {US.v i < A.length a \/ US.v i < Seq.length s})
  (#p: perm)
: stt t
    (requires
      A.pts_to a p s)
    (ensures fun res ->
      A.pts_to a p s `star`
      pure (Seq.length s == A.length a /\
            US.v i < Seq.length s /\
            res == Seq.index s (US.v i)))

```pulse
fn read_at_offset_refine (a:array U32.t) (i:US.t) (#p:perm) (#s:Ghost.erased (Seq.seq U32.t))
   requires (A.pts_to a p s `star`
             pure (US.v i < A.length a \/ US.v i < Seq.length s))
   returns x:U32.t
   ensures (
      A.pts_to a p s
     `star`
      pure (Seq.length s == A.length a /\
            US.v i < Seq.length s /\
            x == Seq.index s (US.v i))
   )
{ 
   let x = test_array_access a i;
   x
} 
```


```pulse
fn read_at_offset_refine_poly (#t:Type0) (a:array t) (i:US.t) (#p:perm) (#s:Ghost.erased (Seq.seq t))
   requires (A.pts_to a p s `star`
             pure (US.v i < A.length a \/ US.v i < Seq.length s))
   returns x:t
   ensures (
      A.pts_to a p s
     `star`
      pure (Seq.length s == A.length a /\
            US.v i < Seq.length s /\
            x == Seq.index s (US.v i))
   )
{ 
   let x = test_array_access a i;
   x
} 
```
//Error message is poor as usual
//But, this type is genuinely incorrect, since the return type does not assume
//the validity of the pure conjuncts in the requires
//so the sequence indexing there cannot be proven to be safe
//Maybe we should find a way to allow the pure conjuncts to be assumed in the returns
//Megan correctly remarks that this is unintuitive ... let's see if we can fix it
[@@expect_failure]
```pulse
fn read_at_offset_refine (a:array U32.t) (i:US.t) (#p:perm) (#s:Ghost.erased (Seq.seq U32.t))
   requires (A.pts_to a p s `star` pure (US.v i < A.length a))
   returns x: (x:U32.t { Seq.length s == A.length a /\
                         x == Seq.index s (US.v i)})
   ensures (
      A.pts_to a p s
   )
{ 
   let x = test_array_access a i;
   (x <: (x:U32.t { Seq.length s == A.length a /\
                    US.v i < A.length a /\
                    x == Seq.index s (US.v i)}))
} 
```

//But if we hoist the pure payload into a refinement, then it can be used for typing throughout the spec & body
```pulse
fn read_at_offset_refine_post (a:array U32.t) (i:(i:US.t { US.v i < A.length a})) (#p:perm) (#s:Ghost.erased (Seq.seq U32.t))
   requires (A.pts_to a p s)
   returns x: (x:U32.t { Seq.length s == A.length a /\
                         x == Seq.index s (US.v i)})
   ensures (
      A.pts_to a p s
   )
{ 
   let x = test_array_access a i;
   (x <: (x:U32.t { Seq.length s == A.length a /\
                         x == Seq.index s (US.v i)}))
} 
```

```pulse
fn read_at_offset_refine_post2 (a:array U32.t) (i:US.t) (#p:perm) (#s:Ghost.erased (Seq.seq U32.t))
   requires (A.pts_to a p s `star` pure (US.v i < A.length a))
   returns x: (x:U32.t { Seq.length s == A.length a /\
                         US.v i < A.length a /\
                         x == Seq.index s (US.v i)})
   ensures (
      A.pts_to a p s
   )
{ 
   let x = test_array_access a i;
   (x <: (x:U32.t { Seq.length s == A.length a /\
                    US.v i < A.length a /\
                    x == Seq.index s (US.v i)}))
} 
```

```pulse
fn write_at_offset (#t:Type0) (a:array t) (i:US.t) (v:t)
                   (#s:(s:Ghost.erased (Seq.seq t) {US.v i < Seq.length s}))
   requires (A.pts_to a full_perm s)
   ensures (
      A.pts_to a full_perm (Seq.upd s (US.v i) v)
   )
{
   (a.(i) <- v)
}
```

let sorted (s0 s:Seq.seq U32.t) =
   (forall (i:nat). i < Seq.length s - 1 ==> U32.v (Seq.index s i) <= U32.v (Seq.index s (i + 1))) /\
   (forall (i:nat). i < Seq.length s0 ==> (exists (j:nat). j < Seq.length s /\ U32.v (Seq.index s0 i) == U32.v (Seq.index s j)))


open FStar.UInt32
#push-options "--query_stats"

```pulse
fn sort3 (a:array U32.t)
         (#s:(s:Ghost.erased (Seq.seq U32.t) {Seq.length s == 3}))
   requires (A.pts_to a full_perm s)
   ensures 
      exists (s':Seq.seq (U32.t)). (
         A.pts_to a full_perm s' `star`
         pure (sorted s s')
      )
{
   let x = a.(0sz);
   let y = a.(1sz);
   let z = a.(2sz);
   if (x >^ y) 
   {
      if (y >^ z)
      {
         (a.(0sz) <- z);
         (a.(1sz) <- y);
         (a.(2sz) <- x);
         ()
      }
      else {
         if (x >^ z)
         {
            (a.(0sz) <- y);
            (a.(1sz) <- z);
            (a.(2sz) <- x);
            ()
         }
         else
         {
            (a.(0sz) <- y);
            (a.(1sz) <- x);
            (a.(2sz) <- z);
            ()  
         }     
      }
   }
   else {
      if (y >^ z) {
         if (x >^ z) {
            (a.(0sz) <- z);
            (a.(1sz) <- x);
            (a.(2sz) <- y);
            ()
         }
         else {
            (a.(0sz) <- x);
            (a.(1sz) <- z);
            (a.(2sz) <- y);
            ()
         }
      }
      else {
         (a.(0sz) <- x);
         (a.(1sz) <- y);
         (a.(2sz) <- z);
         ()
      }
   }
}
```