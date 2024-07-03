module Pulse.Lib.Slice

module AP = Pulse.Lib.ArrayPtr

noeq
type slice t = {
    elt: AP.ptr t;
    len: SZ.t;
    fp: AP.footprint;
}

let len s = s.len

let pts_to #t s #p v =
    AP.pts_to s.elt #p s.fp v **
    pure (Seq.length v == SZ.v s.len)

let pts_to_is_small x p v = ()

```pulse
ghost
fn pts_to_len (#t: Type) (s: slice t) (#p: perm) (#v: Seq.seq t)
requires    (pts_to s #p v)
ensures    (pts_to s #p v ** pure (Seq.length v == SZ.v (len s)))

{
    unfold (pts_to s #p v);
    fold (pts_to s #p v)
}
```

let is_from_array #t a p s =
    AP.is_from_array p s.fp a **
    pure (SZ.v s.len == A.length a)

```pulse
fn from_array (#t: Type) (mutb: bool) (a: array t) (#p: perm) (#v: Ghost.erased (Seq.seq t)) (alen: SZ.t {
    SZ.v alen == A.length a /\
    (mutb == true ==> p == 1.0R)
})
requires    (A.pts_to a #p v)
returns s: (slice t)
ensures    (
        pts_to s #p v **
        is_from_array a p s
    )
{
    A.pts_to_len a;
    let ptr = AP.from_array a;
    with fp . assert (AP.pts_to ptr #p fp v ** AP.is_from_array p fp a);
    let res : slice t = {
        elt = ptr;
        len = alen;
        fp = fp;
    };
    rewrite (AP.pts_to ptr #p fp v) as (AP.pts_to res.elt #p res.fp v);
    fold (pts_to res #p v);
    rewrite (AP.is_from_array p fp a) as (AP.is_from_array p res.fp a);
    fold (is_from_array a p res);
    res
}
```

```pulse
ghost
fn to_array
    (#t: Type) (s: slice t) (#p: perm) (#v: Seq.seq t) (#a: array t)
requires    (pts_to s #p v ** is_from_array a p s)
ensures    (A.pts_to a #p v)
{
    unfold (pts_to s #p v);
    unfold (is_from_array a p s);
    AP.to_array s.elt a
}
```

```pulse
fn op_Array_Access
        (#t: Type)
        (a: slice t)
        (i: SZ.t)
        (#p: perm)
        (#s: Ghost.erased (Seq.seq t){SZ.v i < Seq.length s})
        requires
            pts_to a #p s
returns res : t
ensures
            pts_to a #p s **
            pure (res == Seq.index s (SZ.v i))
{
    unfold (pts_to a #p s);
    let res = AP.op_Array_Access a.elt i;
    fold (pts_to a #p s);
    res
}
```

```pulse
fn op_Array_Assignment
        (#t: Type)
        (a: slice t)
        (i: SZ.t)
        (v: t)
        (#s: Ghost.erased (Seq.seq t) {SZ.v i < Seq.length s})
        requires
            pts_to a s
        ensures
            pts_to a (Seq.upd s (SZ.v i) v)
{
    unfold (pts_to a s);
    AP.op_Array_Assignment a.elt i v;
    fold (pts_to a (Seq.upd s (SZ.v i) v))
}
```

```pulse
ghost
fn share
  (#a:Type)
  (arr:slice a)
  (#s:Ghost.erased (Seq.seq a))
  (#p:perm)
requires
    pts_to arr #p s
ensures pts_to arr #(p /. 2.0R) s ** pts_to arr #(p /. 2.0R) s
{
    unfold (pts_to arr #p s);
    AP.share arr.elt;
    fold (pts_to arr #(p /. 2.0R) s);
    fold (pts_to arr #(p /. 2.0R) s)
}
```

```pulse
ghost
fn gather
  (#a:Type)
  (arr:slice a)
  (#s0 #s1:Ghost.erased (Seq.seq a))
  (#p0 #p1:perm)
requires pts_to arr #p0 s0 ** pts_to arr #p1 s1
ensures pts_to arr #(p0 +. p1) s0 ** pure (s0 == s1)
{
    unfold (pts_to arr #p0 s0);
    unfold (pts_to arr #p1 s1);
    AP.gather arr.elt;
    fold (pts_to arr #(p0 +. p1) s0)
}
```

let is_split #t s p i s1 s2 =
    pure (
        s1.elt == s.elt /\
        AP.adjacent s1.fp s2.fp /\
        AP.merge s1.fp s2.fp == s.fp
    )

val split0 (#t: Type) (s: slice t) (#p: perm) (#v: Ghost.erased (Seq.seq t)) (i: SZ.t) : stt (slice t & slice t)
    (requires pts_to s #p v ** pure (SZ.v i <= Seq.length v))
    (ensures fun res -> let (s1, s2) = res in
        exists* v1 v2 .
            pts_to s1 #p v1 **
            pts_to s2 #p v2 **
            is_split s p i s1 s2 **
            pure (
                SZ.v i <= Seq.length v /\
                (v1, v2) == Seq.split v (SZ.v i)
            )
    )


```pulse
ghost
fn split0 (#t: Type) (s: slice t) (#p: perm) (#v: Ghost.erased (Seq.seq t)) (i: SZ.t)
    requires pts_to s #p v ** pure (SZ.v i <= Seq.length v)
    returns res : (slice t & slice t)
    ensures (let (s1, s2) = res in
        exists* v1 v2 .
            pts_to s1 #p v1 **
            pts_to s2 #p v2 **
            is_split s p i s1 s2 **
            pure (
                SZ.v i <= Seq.length v /\
                (v1, v2) == Seq.split v (SZ.v i)
            )
    )
{
    admit ()
}
```

let split s #p #v i = split0 s #p #v i
