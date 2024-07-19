module Pulse.Lib.ArrayPtr

noeq
type ptr t = {
    base: A.array t;
    offset: (offset: SZ.t { SZ.v offset <= A.length base})
}

[@@erasable]
noeq
type footprint (t: Type0) = {
    elt: ptr t;
    len: (len: SZ.t { SZ.v elt.offset + SZ.v len <= A.length elt.base});
}

let pts_to s #p fp v =
    A.pts_to_range s.base (SZ.v s.offset) (SZ.v s.offset + SZ.v fp.len) #p v **
    pure (fp.elt == s)

let pts_to_is_slprop2 x p fp s = ()

let is_from_array p fp a =
    pure (fp.elt.base == a /\ SZ.v fp.len == A.length a)

```pulse
fn from_array (#t: Type) (a: A.array t) (#p: perm) (#v: Ghost.erased (Seq.seq t))
    requires A.pts_to a #p v
    returns s: ptr t
    ensures exists* fp . pts_to s #p fp v ** is_from_array p fp a
{
    A.pts_to_len a;
    let res = {
        base = a;
        offset = 0sz;
    };
    let fp = {
        elt = res;
        len = SZ.uint_to_t (A.length a);
    };
    fold (is_from_array p fp a);
    A.pts_to_range_intro a p v;
    rewrite (A.pts_to_range a 0 (A.length a) #p v)
        as (A.pts_to_range res.base (SZ.v res.offset) (SZ.v res.offset + SZ.v fp.len) #p v);
    fold (pts_to res #p fp v);
    res
}
```

```pulse 
ghost
fn to_array (#t: Type) (s: ptr t) (a: array t) (#p: perm) (#fp: footprint t) (#v: Seq.seq t)
    requires pts_to s #p fp v ** is_from_array p fp a ** pure (
        Seq.length v == A.length a
    )
    ensures A.pts_to a #p v
{
    unfold (is_from_array p fp a);
    unfold (pts_to s #p fp v);
    rewrite (A.pts_to_range s.base (SZ.v s.offset) (SZ.v s.offset + SZ.v fp.len) #p v)
        as (A.pts_to_range a 0 (A.length a) #p v);
    A.pts_to_range_elim a _ _;
}
```

```pulse
fn op_Array_Access
        (#t: Type)
        (a: ptr t)
        (i: SZ.t)
        (#p: perm)
        (#fp: footprint t)
        (#s: Ghost.erased (Seq.seq t){SZ.v i < Seq.length s})
        requires
            pts_to a #p fp s
        returns res: t
        ensures
            pts_to a #p fp s **
            pure (res == Seq.index s (SZ.v i))
{
    unfold (pts_to a #p fp s);
    A.pts_to_range_prop a.base;
    let res = A.pts_to_range_index a.base (SZ.add a.offset i);
    fold (pts_to a #p fp s);
    res
}
```

```pulse
fn op_Array_Assignment
        (#t: Type)
        (a: ptr t)
        (i: SZ.t)
        (v: t)
        (#fp: footprint t)
        (#s: Ghost.erased (Seq.seq t) {SZ.v i < Seq.length s})
        requires
            pts_to a fp s
        ensures
            pts_to a fp (Seq.upd s (SZ.v i) v)
{
    unfold (pts_to a fp s);
    A.pts_to_range_prop a.base;
    let res = A.pts_to_range_upd a.base (SZ.add a.offset i) v;
    fold (pts_to a fp (Seq.upd s (SZ.v i) v));
}
```

```pulse
ghost
fn share
  (#a:Type)
  (arr:ptr a)
  (#s:Ghost.erased (Seq.seq a))
  (#fp: footprint a)
  (#p:perm)
    requires pts_to arr #p fp s
    ensures pts_to arr #(p /. 2.0R) fp s ** pts_to arr #(p /. 2.0R) fp s
{
    unfold (pts_to arr #p fp s);
    A.pts_to_range_share arr.base;
    fold (pts_to arr #(p /. 2.0R) fp s);
    fold (pts_to arr #(p /. 2.0R) fp s);    
}
```

```pulse
ghost
fn gather
  (#a:Type)
  (arr:ptr a)
  (#s0 #s1:Ghost.erased (Seq.seq a))
  (#p0 #p1:perm)
  (#fp: footprint a)
      requires pts_to arr #p0 fp s0 ** pts_to arr #p1 fp s1
      ensures pts_to arr #(p0 +. p1) fp s0 ** pure (s0 == s1)
{
    unfold (pts_to arr #p0 fp s0);
    unfold (pts_to arr #p1 fp s1);
    A.pts_to_range_gather arr.base;
    fold (pts_to arr #(p0 +. p1) fp s0)
}
```

let adjacent fp1 fp2 =
    fp1.elt.base == fp2.elt.base /\
    SZ.v fp1.elt.offset + SZ.v fp1.len == SZ.v fp2.elt.offset

let merge fp1 fp2 = {
    elt = fp1.elt;
    len = SZ.add fp1.len fp2.len;
}

let merge_assoc fp1 fp2 fp3 = ()

```pulse
fn split (#t: Type) (s: ptr t) (#p: perm) (#fp: footprint t) (#v: Ghost.erased (Seq.seq t)) (i: SZ.t)
    requires pts_to s #p fp v ** pure (SZ.v i <= Seq.length v)
    returns s' : ptr t
    ensures
        exists* v1 v2 fp1 fp2 .
            pts_to s #p fp1 v1 **
            pts_to s' #p fp2 v2 **
            pure (split_postcond fp v i v1 v2 fp1 fp2)
{
    unfold (pts_to s #p fp v);
    A.pts_to_range_prop s.base;
    let s' = {
        base = s.base;
        offset = SZ.add s.offset i;
    };
    let fp1 = {
        elt = fp.elt;
        len = i;
    };
    let fp2 = {
        elt = s';
        len = SZ.sub fp.len i;
    };
    A.pts_to_range_split s.base _ (SZ.v s'.offset) _;
    with s1 . assert (A.pts_to_range s.base (SZ.v s.offset) (SZ.v s'.offset) #p s1);
    rewrite
        (A.pts_to_range s.base (SZ.v s.offset) (SZ.v s'.offset) #p s1)
        as (A.pts_to_range s.base (SZ.v s.offset) (SZ.v s.offset + SZ.v fp1.len) #p s1);
    fold (pts_to s #p fp1 s1);
    with s2 . assert (A.pts_to_range s.base (SZ.v s'.offset) (SZ.v s.offset + SZ.v fp.len) #p s2);
    rewrite
        (A.pts_to_range s.base (SZ.v s'.offset) (SZ.v s.offset + SZ.v fp.len) #p s2)
        as (A.pts_to_range s'.base (SZ.v s'.offset) (SZ.v s'.offset + SZ.v fp2.len) #p s2);
    fold (pts_to s' #p fp2 s2);
    s'
}
```

```pulse
ghost
fn join (#t: Type) (s1: ptr t) (#p: perm) (#fp1: footprint t) (#v1: Seq.seq t) (s2: ptr t) (#fp2: footprint t {adjacent fp1 fp2}) (#v2: Seq.seq t)
    requires pts_to s1 #p fp1 v1 ** pts_to s2 #p fp2 v2
    ensures pts_to s1 #p (merge fp1 fp2) (Seq.append v1 v2)
{
    unfold (pts_to s1 #p fp1 v1);
    unfold (pts_to s2 #p fp2 v2);
    rewrite (A.pts_to_range s2.base (SZ.v s2.offset) (SZ.v s2.offset + SZ.v fp2.len) #p v2)
        as (A.pts_to_range s1.base (SZ.v s1.offset + SZ.v fp1.len) (SZ.v s1.offset + SZ.v (merge fp1 fp2).len) #p v2);
    A.pts_to_range_join s1.base (SZ.v s1.offset) (SZ.v s1.offset + SZ.v fp1.len) (SZ.v s1.offset + SZ.v (merge fp1 fp2).len);
    fold (pts_to s1 #p (merge fp1 fp2) (Seq.append v1 v2))
}
```
