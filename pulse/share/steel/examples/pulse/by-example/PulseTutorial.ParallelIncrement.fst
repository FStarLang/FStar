module PulseTutorial.ParallelIncrement
open Pulse.Lib.Pervasives
module U32 = FStar.UInt32
module L = Pulse.Lib.SpinLock
module GR = Pulse.Lib.GhostReference
module R = Pulse.Lib.Reference

```pulse //par$
fn par (#pf #pg #qf #qg:_)
       (f: unit -> stt unit pf (fun _ -> qf))
       (g: unit -> stt unit pg (fun _ -> qg))
requires pf ** pg
ensures qf ** qg
{
  parallel 
  requires pf and pg
  ensures qf and qg
  { f () }
  { g () };
  ()
}
```

```pulse
fn incr2 (x y:ref int)
requires pts_to x 'i ** pts_to y 'j
ensures pts_to x ('i + 1) ** pts_to y ('j + 1)
{
  fn incr (x:ref int) (#i:erased int)
  requires pts_to x i
  ensures pts_to x (i + 1)
  {
    let v = !x;
    x := v + 1;
  };
  par (fun _ -> incr x) (fun _ -> incr y);
}
```


[@@expect_failure]
```pulse
fn attempt0 (x:ref int)
requires pts_to x 'i
ensures pts_to x ('i + 2)
{
  fn incr (#i:erased int)
  requires pts_to x i
  ensures pts_to x (i + 1)
  {
    let v = !x;
    x := v + 1;
  };
  par (fun _ -> incr) (fun _ -> incr);
}
```

```pulse //attempt$
fn attempt (x:ref int)
requires pts_to x 'i
ensures emp
{
  let l = L.new_lock (exists* v. pts_to x v);
  fn incr ()
  requires emp
  ensures emp
  {
    L.acquire l;
    let v = !x;
    x := v + 1;
    L.release l
  };
  par incr incr
}
```

//lock_inv$
let contributions (left right: GR.ref int) (i v:int)=
  exists* (vl vr:int).
    GR.pts_to left #one_half vl **
    GR.pts_to right #one_half vr **
    pure (v == i + vl + vr)

let lock_inv (x:ref int) (init:int) (left right:GR.ref int) =
  exists* v. 
    pts_to x v **
    contributions left right init v
//lock_inv$

```pulse //incr_left$
fn incr_left (x:ref int)
             (#left:GR.ref int)
             (#right:GR.ref int)
             (#i:erased int)
             (lock:L.lock (lock_inv x i left right))
requires GR.pts_to left #one_half 'vl
ensures  GR.pts_to left #one_half ('vl + 1)
{
  L.acquire lock;
  unfold lock_inv;
  unfold contributions;
  let v = !x;
  x := v + 1;
  GR.gather left;
  GR.write left ('vl + 1);
  GR.share left;
  fold (contributions left right i (v + 1));
  fold lock_inv;
  L.release lock
}
```

```pulse //incr_right$
fn incr_right (x:ref int)
              (#left:GR.ref int)
              (#right:GR.ref int)
              (#i:erased int)
              (lock:L.lock (lock_inv x i left right))
requires GR.pts_to right #one_half 'vl
ensures  GR.pts_to right #one_half ('vl + 1)
{
  L.acquire lock;
  unfold lock_inv;
  unfold contributions;
  let v = !x;
  x := v + 1;
  GR.gather right;
  GR.write right ('vl + 1);
  GR.share right;
  fold (contributions left right i (v + 1));
  fold (lock_inv x i left right);
  L.release lock
}
```

```pulse //add2$
fn add2 (x:ref int)
requires pts_to x 'i
ensures  pts_to x ('i + 2)
{
  let left = GR.alloc 0;
  let right = GR.alloc 0;
  GR.share left;
  GR.share right;
  fold (contributions left right 'i 'i);
  fold (lock_inv x 'i left right);
  let lock = L.new_lock (lock_inv x 'i left right);
  par (fun _ -> incr_left x lock)
      (fun _ -> incr_right x lock);
  L.acquire lock;
  unfold lock_inv;
  unfold contributions;
  GR.gather left;
  GR.gather right;
  GR.free left;
  GR.free right;
}
```

/////////////////////////////////////////////////////////////////////////
// A bit more generic, with ghost functions
// A similar style to Bart Jacobs & Frank Piessens POPL '11
/////////////////////////////////////////////////////////////////////////

//Parameterize incr by the ghost steps it needs to take
//give it an abstract spec in terms of some call-provided aspec
```pulse //incr$
fn incr (x: ref int)
        (#refine #aspec: int -> vprop)
        (l:L.lock (exists* v. pts_to x v ** refine v))
        (ghost_steps: 
          (v:int -> vq:int -> stt_ghost unit emp_inames 
               (refine v ** aspec vq ** pts_to x (v + 1))
               (fun _ -> refine (v + 1) ** aspec (vq + 1) ** pts_to x (v + 1))))
requires aspec 'i
ensures aspec ('i + 1)
 {
    L.acquire l;
    with _v. _;
    let vx = !x;
    rewrite each _v as vx;
    x := vx + 1;
    ghost_steps vx 'i;
    L.release l;
}
```

//At the call-site, we instantiate incr twice, with different
//ghost steps
```pulse //add2_v2$
fn add2_v2 (x: ref int)
requires pts_to x 'i
ensures pts_to x ('i + 2)
{
    let left = GR.alloc 0;
    let right = GR.alloc 0;
    GR.share left;
    GR.share right;
    fold (contributions left right 'i 'i);
    let lock = L.new_lock (
      exists* (v:int).
        pts_to x v ** contributions left right 'i v
    );
    ghost
    fn step
        (lr:GR.ref int)
        (b:bool { if b then lr == left else lr == right })
        (v vq:int)
      requires 
        contributions left right 'i v **
        GR.pts_to lr #one_half vq **
        pts_to x (v + 1)
      ensures
        contributions left right 'i (v + 1) **
        GR.pts_to lr #one_half (vq + 1) **
        pts_to x (v + 1)
    { 
      unfold contributions;
      if b
      {
        with _p _v. rewrite (GR.pts_to lr #_p _v) as (GR.pts_to left #_p _v);
        GR.gather left;
        GR.write left (vq + 1);
        GR.share left;      
        with _p _v. rewrite (GR.pts_to left #_p _v) as (GR.pts_to lr #_p _v);
        fold (contributions left right 'i (v + 1));
      }
      else
      {
        with _p _v. rewrite (GR.pts_to lr #_p _v) as (GR.pts_to right #_p _v);
        GR.gather right;
        GR.write right (vq + 1);
        GR.share right;      
        with _p _v. rewrite (GR.pts_to right #_p _v) as (GR.pts_to lr #_p _v);
        fold (contributions left right 'i (v + 1));
      }
    };

    par (fun _ -> incr x lock (step left true))
        (fun _ -> incr x lock (step right false));

    L.acquire lock; //we leak the lock here, but we can do better, below
    unfold contributions;
    GR.gather left;
    GR.gather right;
    GR.free left;
    GR.free right;
}
```

//Note, rather than using two ghost references and duplicating code
//monoids and use just a single piece of ghost state. But, that's for another
//chapter

/////////////////////////////////////////////////////////////////////////
// Using invariants instead of locks
/////////////////////////////////////////////////////////////////////////

// Doing this with int instead of U32, just to keep it a bit simpler
// assuming atomic_read and cas on int
//atomic_primitives$
assume
val atomic_read (r:ref int) (#p:_) (#i:erased int)
  : stt_atomic int emp_inames 
    (pts_to r #p i)
    (fun v -> pts_to r #p i ** pure (reveal i == v))

assume
val cas (r:ref int) (u v:int) (#i:erased int)
  : stt_atomic bool emp_inames 
    (pts_to r i)
    (fun b ->
      cond b (pts_to r v ** pure (reveal i == u)) 
             (pts_to r i))
//atomic_primitives$

//This provides a way to allocate an invariant
//and then discard it
module C = Pulse.Lib.CancellableInvariant

```pulse //incr_atomic_spec$
fn incr_atomic
        (x: ref int)
        (#p:perm)
        (#t:erased C.token)
        (#refine #aspec: int -> vprop)
        (l:inv (C.cancellable t (exists* v. pts_to x v ** refine v)))
        (f: (v:int -> vq:int -> stt_ghost unit emp_inames 
                  (refine v ** aspec vq ** pts_to x (v + 1))
                  (fun _ -> refine (v + 1) ** aspec (vq + 1) ** pts_to x (v + 1))))
requires aspec 'i ** C.active p t
ensures aspec ('i + 1) ** C.active p t
//incr_atomic_body$
{
  //incr_atomic_body_read$
  atomic
  fn read ()
  requires C.active p t
  returns v:int
  ensures C.active p t
  opens (add_inv emp_inames l)
  {
    with_invariants l
    {
        C.take _;
        let v = atomic_read x;
        C.restore (exists* v. pts_to x v ** refine v);
        v
    }
  };
  //incr_atomic_body_read$
  //incr_atomic_body_loop$
  let mut continue = true;
  fold (cond true (aspec 'i) (aspec ('i + 1)));
  while (
    with _b. _;
    let b = !continue;
    rewrite each _b as b;
    b
  )
  invariant b.
    pts_to continue b **
    C.active p t **
    cond b (aspec 'i) (aspec ('i + 1))
  {
    let v = read ();
    let next = 
      with_invariants l
      returns b1:bool
      ensures cond b1 (aspec 'i) (aspec ('i + 1))
          ** pts_to continue true
          ** C.active p t
      {
        C.take _;
        let b = cas x v (v + 1);
        if b
        { 
          elim_cond_true b _ _;
          elim_cond_true true _ _;
          f _ _;
          intro_cond_false (aspec 'i) (aspec ('i + 1));
          C.restore (exists* v. pts_to x v ** refine v);
          false
        }
        else
        {
          with p q. rewrite (cond b p q) as q;
          C.restore (exists* v. pts_to x v ** refine v);
          true
        }
      };
    continue := next
  };
  //incr_atomic_body_loop$
  unfold cond;
}
```


```pulse //add2_v3$
fn add2_v3 (x: ref int)
requires pts_to x 'i
ensures pts_to x ('i + 2)
{
    let left = GR.alloc 0;
    let right = GR.alloc 0;
    GR.share left;
    GR.share right;
    fold (contributions left right 'i 'i);
    let tok = C.create2 (
      exists* (v:int).
          pts_to x v **
          contributions left right 'i v
    );
    C.share tok; 
    let inv = new_invariant (C.cancellable tok _);
    ghost
    fn step
        (lr:GR.ref int)
        (b:bool { if b then lr == left else lr == right })
        (v vq:int)
      requires 
        contributions left right 'i v **
        GR.pts_to lr #one_half vq **
        pts_to x (v + 1)
      ensures
        contributions left right 'i (v + 1) **
        GR.pts_to lr #one_half (vq + 1) **
        pts_to x (v + 1)
    { 
      unfold contributions;
      if b
      {
        with _p _v. rewrite (GR.pts_to lr #_p _v) as (GR.pts_to left #_p _v);
        GR.gather left;
        GR.write left (vq + 1);
        GR.share left;      
        with _p _v. rewrite (GR.pts_to left #_p _v) as (GR.pts_to lr #_p _v);
        fold (contributions left right 'i (v + 1));
      }
      else
      {
        with _p _v. rewrite (GR.pts_to lr #_p _v) as (GR.pts_to right #_p _v);
        GR.gather right;
        GR.write right (vq + 1);
        GR.share right;      
        with _p _v. rewrite (GR.pts_to right #_p _v) as (GR.pts_to lr #_p _v);
        fold (contributions left right 'i (v + 1));
      }
    };

    par (fun _ -> incr_atomic x inv (step left true))
        (fun _ -> incr_atomic x inv (step right false));

    C.gather tok;
    C.cancel_inv inv;
    unfold contributions;
    GR.gather left;
    GR.gather right;
    GR.free left;
    GR.free right;

}
```
