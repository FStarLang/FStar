module BugHigherOrderApplication
open Pulse.Lib.Pervasives

```pulse
fn apply (#a #b:Type0) (f: (x:a -> stt b emp (fun _ -> emp))) (x:a)
    requires emp
    returns y:b
    ensures emp
{
    f x
}
```

```pulse
fn apply2 (#a #b:Type0) (f: (x:a -> stt b emp (fun _ -> emp))) (x:a)
    requires emp
    returns y:(b & b)
    ensures emp
{
    let fst = f x;
    let snd = f x;
    (fst, snd)
}
```

```pulse
fn apply_with_imps (#a #b:Type0) (#p:(a -> vprop)) (#q:(a -> b -> vprop))
                  (f: (x:a -> stt b (p x) (fun y -> q x y)))
                  (x:a)
    requires p x
    returns y:b
    ensures q x y
{
    f x;
}
```

```pulse
fn apply_with_imps_inst
    (#a #b:Type0) (#p:(a -> nat -> vprop)) (#q:(a -> nat -> b -> vprop))
    (f: (x:a -> #index:nat -> stt b (p x index) (fun y -> q x index y)))
    (x:a)
  requires p x 0
  returns y:b
  ensures q x 0 y
{
    f x;
}
```



```pulse
fn apply_with_imps_explicit 
    (#a #b:Type0) (#p:(a -> nat -> vprop)) (#q:(a -> nat -> b -> vprop))
    (f: (x:a -> #index:erased nat -> stt b (p x index) (fun y -> q x index y)))
    (x:a) (#i:erased nat)
  requires p x i
  returns y:b
  ensures q x i y
{
    f x #i;
}
```

```pulse
fn rec loop (x:int)
    requires emp
    returns y:int
    ensures emp
{
    let res = loop x;
    (res + 1)
}
```

```pulse
fn curry_stt
    (#a #b #c:Type0)
    (f: (a -> stt (b -> (stt c emp (fun _ -> emp))) emp (fun _ -> emp)))
    (x:a) (y:b)
  requires emp
  returns _:c
  ensures emp
{
    let g = f x;
    g y
}
```

let id_t (a:Type) = a -> stt a emp (fun _ -> emp)

// Abbreviations don't work yet
[@@expect_failure]
```pulse
fn apply_id_t (f:id_t bool) (x:bool)
  requires emp
  returns _:bool
  ensures emp
{
   let res = f x;
   res
}
```
