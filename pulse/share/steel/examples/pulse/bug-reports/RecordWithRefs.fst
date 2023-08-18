module RecordWithRefs
open Pulse.Lib.Pervasives
module U8 = FStar.UInt8
module R = Pulse.Lib.Reference

noeq
type u8_pair = {
    a: ref U8.t;
    b: ref U8.t
}

let u8_pair_repr = (U8.t & U8.t)

let fst (p:u8_pair_repr) : U8.t =
  let (x, _) = p in x
let snd (p:u8_pair_repr) : U8.t =
  let (_, x) = p in x
  
let u8_pair_pred (p:u8_pair) (v:u8_pair_repr) : vprop = 
    R.pts_to p.a (fst v) **
    R.pts_to p.b (snd v)


```pulse
ghost
fn fold_u8_pair_pred (x:u8_pair) (#u #v:erased U8.t)
  requires
    R.pts_to x.a u **
    R.pts_to x.b v
  ensures
    u8_pair_pred x (reveal u, reveal v)
{
   fold (u8_pair_pred x (reveal u, reveal v))
}
```

```pulse
fn swap_pair (p: u8_pair) (#v: erased u8_pair_repr)
  requires 
    u8_pair_pred p v
  ensures
    u8_pair_pred p (snd v, fst v)
{
    rewrite (u8_pair_pred p v)
    as      (R.pts_to p.a (fst v) **
             R.pts_to p.b (snd v));
    let x = !p.a;
    let y = !p.b;
    p.a := y;
    p.b := x; 
    rewrite (R.pts_to p.a y **
             R.pts_to p.b x)
        as (u8_pair_pred p (snd v, fst v));
    ()
}
```


```pulse
fn swap_pair_alt (p: u8_pair) (#v: erased u8_pair_repr)
  requires 
    u8_pair_pred p v
  ensures
    u8_pair_pred p (snd v, fst v)
{
    unfold (u8_pair_pred p v);
    
    let x = !p.a;
    let y = !p.b;
    p.a := y;
    p.b := x;
    
    fold (u8_pair_pred p (snd v, fst v));

    ()
}
```

```pulse
fn swap_pair_alt2 (p: u8_pair) (#v: erased u8_pair_repr)
  requires 
    u8_pair_pred p v
  ensures
    u8_pair_pred p (snd v, fst v)
{
    with _p _v.
    unfold (u8_pair_pred _p _v);
    
    let x = !p.a;
    let y = !p.b;
    p.a := y;
    p.b := x;
    
    with _v1 _v2.
    fold [fst; snd] u8_pair_pred p (_v1, _v2);
    ()
}
```



```pulse
fn swap_pair_alt3 (p: u8_pair) (#v: erased u8_pair_repr)
  requires 
    u8_pair_pred p v
  ensures
    u8_pair_pred p (snd v, fst v)
{
    with _p _v.
    unfold (u8_pair_pred _p _v);
    
    let x = !p.a;
    let y = !p.b;
    p.a := y;
    p.b := x;
    
    fold_u8_pair_pred p
}
```
