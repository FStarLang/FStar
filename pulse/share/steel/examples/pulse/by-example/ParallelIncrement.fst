module ParallelIncrement
open Pulse.Lib.Pervasives
module U32 = FStar.UInt32
module L = Pulse.Lib.SpinLock
module GR = Pulse.Lib.GhostReference
```pulse
fn increment (x: ref nat)
             (l:L.lock (exists* v. pts_to x #one_half v))
requires pts_to x #one_half 'i
ensures pts_to x #one_half ('i + 1)
 {
    let v = !x;
    L.acquire l;
    gather x;
    with p _v. rewrite (pts_to x #p _v) as (pts_to x _v);
    x := (v + 1);
    share x;
    with p _v. rewrite (pts_to x #p _v) as (pts_to x #one_half _v);
    L.release l;
    with p _v. rewrite (pts_to x #p _v) as (pts_to x #one_half _v);
}
```

#push-options "--print_implicits --ext 'pulse:env_on_err' --print_full_names"
```pulse
fn increment_f (x: ref nat)
               (#pred #qpred: nat -> vprop)
               (l:L.lock (exists* v. pts_to x #one_half v ** pred v))
               (f: (v:nat -> stt_ghost unit emp_inames 
                        (pred v ** qpred v ** pts_to x #one_half (v + 1))
                        (fun _ -> pred (v + 1) ** qpred (v + 1) ** pts_to x #one_half (v + 1))))
requires pts_to x #one_half 'i ** qpred 'i
ensures pts_to x #one_half ('i + 1) ** qpred ('i + 1)
 {
    let vx = !x;
    rewrite (qpred 'i) as (qpred vx);
    L.acquire l;
    gather x;
    with p v. rewrite (pts_to x #p v) as (pts_to x v);
    x := (vx + 1);
    share x;
    with p _v. rewrite (pts_to x #p _v) as (pts_to x #one_half _v);
    with _v. rewrite (pred _v) as (pred vx);
    f vx;
    L.release l;
    with p _v. rewrite (pts_to x #p _v) as (pts_to x #one_half _v);
    rewrite (qpred (vx + 1)) as (qpred ('i + 1));
}
```

```pulse
fn increment_f2 (x: ref int)
                (#pred #qpred: int -> vprop)
                (l:L.lock (exists* v. pts_to x v ** pred v))
                (f: (v:int -> vq:int -> stt_ghost unit emp_inames 
                        (pred v ** qpred vq ** pts_to x (v + 1))
                        (fun _ -> pred (v + 1) ** qpred (vq + 1) ** pts_to x (v + 1))))
requires qpred 'i
ensures qpred ('i + 1)
 {
    L.acquire l;
    let vx = !x;
    with _v. rewrite (pred _v) as (pred vx);
    x := vx + 1;
    f vx 'i;
    L.release l;
}
```

#push-options "--warn_error -249"
```pulse
fn parallel_increment
        (x: ref int)
requires pts_to x 'i
ensures pts_to x ('i + 2)
{
    let left = GR.alloc #int 0;
    let right = GR.alloc #int 0;
    GR.share left;
    GR.share right;
    let lock = L.new_lock (
      exists* (v:int).
        pts_to x v **
        (exists* (vl vr:int).
          GR.pts_to left #(half_perm full_perm) vl **
          GR.pts_to right #(half_perm full_perm) vr **
          pure (v == 'i + vl + vr))
    );
    ghost
    fn step
        (lr:GR.ref int)
        (b:bool { if b then lr == left else lr == right })
        (v vq:int)
      requires 
        (exists* (vl vr:int).
            GR.pts_to left #(half_perm full_perm) vl **
            GR.pts_to right #(half_perm full_perm) vr **
            pure (v == 'i + vl + vr)) **
        GR.pts_to lr #(half_perm full_perm) vq **
        pts_to x (v + 1)
      ensures
        (exists* (vl vr:int).
            GR.pts_to left #(half_perm full_perm) vl **
            GR.pts_to right #(half_perm full_perm) vr **
            pure (v + 1 == 'i + vl + vr)) **
        GR.pts_to lr #(half_perm full_perm) (vq + 1) **
        pts_to x (v + 1)
    { 
      if b
      {
        with _p _v. rewrite (GR.pts_to lr #_p _v) as (GR.pts_to left #_p _v);
        GR.gather left;
        with _p _v. rewrite (GR.pts_to left #_p _v) as (GR.pts_to left _v);
        GR.( left := vq + 1 );
        GR.share left;      
        with _p _v. rewrite (GR.pts_to left #_p _v) as (GR.pts_to lr #_p _v);
      }
      else
      {
        with _p _v. rewrite (GR.pts_to lr #_p _v) as (GR.pts_to right #_p _v);
        GR.gather right;
        with _p _v. rewrite (GR.pts_to right #_p _v) as (GR.pts_to right _v);
        GR.( right := vq + 1 );
        GR.share right;      
        with _p _v. rewrite (GR.pts_to right #_p _v) as (GR.pts_to lr #_p _v);
      }
    };

    parallel
    requires GR.pts_to left #(half_perm full_perm) 0
         and GR.pts_to right #(half_perm full_perm) 0
    ensures  GR.pts_to left #(half_perm full_perm) 1
         and GR.pts_to right #(half_perm full_perm) 1
    { increment_f2 x lock (step left true) }
    { increment_f2 x lock (step right false) };

    L.acquire lock;
    GR.gather left;
    GR.gather right;
    with _p _v. rewrite (GR.pts_to left #_p _v) as (GR.pts_to left _v);
    with _p _v. rewrite (GR.pts_to right #_p _v) as (GR.pts_to right _v);
    GR.free left;
    GR.free right;
}
```