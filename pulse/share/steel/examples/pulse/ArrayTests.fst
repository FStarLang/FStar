module ArrayTests
open Pulse.Lib.Pervasives
module U32 = FStar.UInt32
module A = Pulse.Lib.Array
module US = FStar.SizeT
module R = Pulse.Lib.Reference

#push-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection'"

let elseq (a:Type) (l:nat) = s:Ghost.erased (Seq.seq a) { Seq.length s == l }

```pulse
fn compare (#t:eqtype) (l:US.t) (a1 a2:A.larray t (US.v l))
           (#p1 #p2:perm) (#s1 #s2:elseq t (US.v l))
  requires (
    A.pts_to a1 p1 s1 **
    A.pts_to a2 p2 s2
  )
  returns res:bool
  ensures (
    A.pts_to a1 p1 s1 **
    A.pts_to a2 p2 s2 **
    (pure (res <==> Seq.equal s1 s2))
  )
{
  let mut i = 0sz;
  while (let vi = !i; if US.(vi <^ l) { let v1 = a1.(vi); let v2 = a2.(vi); (v1 = v2) } else { false } )
  invariant b. exists (vi:US.t). ( 
    R.pts_to i full_perm vi **
    A.pts_to a1 p1 s1 **
    A.pts_to a2 p2 s2 **
    pure (
      US.v vi <= US.v l /\
      (b == (US.(vi <^ l) && Seq.index s1 (US.v vi) = Seq.index s2 (US.v vi))) /\
      (forall (i:nat). i < US.v vi ==> Seq.index s1 i == Seq.index s2 i)
    )
  )
  {
    let vi = !i; 
    i := US.(vi +^ 1sz);
    ()
  };
  let vi = !i;
  let res = vi = l;
  res
}
```

```pulse
fn fill_array (#t:Type0) (l:US.t) (a:(a:A.array t{ US.v l == A.length a })) (v:t)
              (#s:(s:Ghost.erased (Seq.seq t) { Seq.length s == US.v l }))
   requires (A.pts_to a full_perm s)
   ensures 
      exists (s:Seq.seq t). (
         A.pts_to a full_perm s **
         pure (s `Seq.equal` Seq.create (US.v l) v)
      )
{
   let mut i = 0sz;
   while (let vi = !i; US.(vi <^ l))
   invariant b. exists (s:Seq.seq t) (vi:US.t). ( 
      A.pts_to a full_perm s **
      R.pts_to i full_perm vi **
      pure ((b == US.(vi <^ l)) /\
            US.v vi <= US.v l /\
            Seq.length s == A.length a /\
            (forall (i:nat). i < US.v vi ==> Seq.index s i == v))
   )
   {
      let vi = !i; 
      a.(vi) <- v;
      i := US.(vi +^ 1sz);
      ()
   };
   ()
}
```

```pulse
fn array_of_zeroes (n:US.t)
   requires emp
   returns a: array U32.t
   ensures (
    A.pts_to a full_perm (Seq.create (US.v n) 0ul) **
    pure (is_full_array a /\ A.length a == US.v n)
  )
{
   let a = A.alloc 0ul n;
   a
}
```

//this is not a recommended way to do this, since s is not erased, but it works
```pulse
fn read_at_offset_0 (#t:Type0) (a:array t) (i:US.t) (#p:perm) (#s:Seq.seq t)
   requires (A.pts_to a p s **
             pure (US.v i < Seq.length s))
   returns x:t
   ensures (
      A.pts_to a p s **
      pure (//Seq.length s == A.length a /\
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
   requires (A.pts_to a p s **
             pure (US.v i < Seq.length s))
   returns x:t
   ensures (
      A.pts_to a p s **
      pure (US.v i < Seq.length s /\
            x == Seq.index s (US.v i))
   )
{
   let x = a.(i);
   x
} 
```

```pulse
fn read_at_offset (a:array U32.t) (i:US.t) (#p:perm) (#s:Ghost.erased (Seq.seq U32.t))
   requires (A.pts_to a p s **
             pure (US.v i < Seq.length s))
   returns x:U32.t
   ensures (
      A.pts_to a p s **
      pure (US.v i < Seq.length s /\
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
      A.pts_to a p s **
      pure (Seq.length s == A.length a /\
            US.v i < Seq.length s /\
            res == Seq.index s (US.v i)))

```pulse
fn read_at_offset_refine (a:array U32.t) (i:US.t) (#p:perm) (#s:Ghost.erased (Seq.seq U32.t))
   requires (A.pts_to a p s **
             pure (US.v i < A.length a \/ US.v i < Seq.length s))
   returns x:U32.t
   ensures (
      A.pts_to a p s
     **
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
   requires (A.pts_to a p s **
             pure (US.v i < A.length a \/ US.v i < Seq.length s))
   returns x:t
   ensures (
      A.pts_to a p s
     **
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
   requires (A.pts_to a p s ** pure (US.v i < A.length a))
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
   x
}
```

```pulse
fn read_at_offset_refine_post2 (a:array U32.t) (i:US.t) (#p:perm) (#s:Ghost.erased (Seq.seq U32.t))
   requires (A.pts_to a p s ** pure (US.v i < A.length a))
   returns x: (x:U32.t { Seq.length s == A.length a /\
                         US.v i < A.length a /\
                         x == Seq.index s (US.v i)})
   ensures (
      A.pts_to a p s
   )
{ 
   let x = test_array_access a i;
   x
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
   a.(i) <- v
}
```

let sorted (s0 s:Seq.seq U32.t) =
   (forall (i:nat). i < Seq.length s - 1 ==> U32.v (Seq.index s i) <= U32.v (Seq.index s (i + 1))) /\
   (forall (i:nat). i < Seq.length s0 ==> (exists (j:nat). j < Seq.length s /\ U32.v (Seq.index s0 i) == U32.v (Seq.index s j)))


open FStar.UInt32
// #push-options "--query_stats"

```pulse
fn sort3 (a:array U32.t)
         (#s:(s:Ghost.erased (Seq.seq U32.t) {Seq.length s == 3}))
   requires (A.pts_to a full_perm s)
   ensures 
      exists s'. (
         A.pts_to a full_perm s' **
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
         a.(0sz) <- z;
         a.(1sz) <- y;
         a.(2sz) <- x;
      }
      else {
         if (x >^ z)
         {
            a.(0sz) <- y;
            a.(1sz) <- z;
            a.(2sz) <- x;
         }
         else
         {
            a.(0sz) <- y;
            a.(1sz) <- x;
            a.(2sz) <- z;
         }     
      }
   }
   else {
      if (y >^ z) {
         if (x >^ z) {
            a.(0sz) <- z;
            a.(1sz) <- x;
            a.(2sz) <- y;
         }
         else {
            a.(0sz) <- x;
            a.(1sz) <- z;
            a.(2sz) <- y;
         }
      }
      else {
         a.(0sz) <- x;
         a.(1sz) <- y;
         a.(2sz) <- z;
      }
   }
}
```

//Pulse does not yet implement join point inference
[@@expect_failure [228]]
```pulse
fn sort3_alt (a:array U32.t)
             (#s:(s:Ghost.erased (Seq.seq U32.t) {Seq.length s == 3}))
   requires (A.pts_to a full_perm s)
   ensures 
      exists s'. (
         A.pts_to a full_perm s' **
         pure (sorted s s')
      )
{
   let mut x = a.(0sz);
   let mut y = a.(1sz);
   let mut z = a.(2sz);
   let vx = !x;
   let vy = !y;
   if (vy <^ vx) 
   {
      x := vy;
      y := vx;
   };
   let vx = !x;
   let vz = !z;
   if (vz <^ vx)
   {
      x := vz;
      z := vx;
   };
   let vy = !y;
   let vz = !z;
   if (vz <^ vy)
   {
      y := vz;
      z := vy;
   };
   a.(0sz) <- x;
   a.(1sz) <- y;
   a.(2sz) <- z;
   ()
}
```
