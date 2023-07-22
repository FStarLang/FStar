module MatchBasic

module T = FStar.Tactics
module PM = Pulse.Main
open Steel.ST.Util
open Steel.ST.Reference
open Steel.FractionalPermission
open FStar.Ghost
open Pulse.Steel.Wrapper

```pulse
fn test1 (n:nat)
  requires emp
  returns r:int
  ensures emp
{
  (* let v = n; *)
  match n {
    0 -> { 1 }
    _ -> { 0 }
  }
}
```

```pulse
fn test2 (n:nat)
  requires emp
  returns r:int
  ensures emp
{
  let v = n;
  match n {
    0 -> { 1 }
    x -> { x }
  }
}
```

```pulse
fn test3 (n:nat)
  requires emp
  returns r:int
  ensures emp
{
  match n {
    0 -> { 1 }
    x -> { let y = x+1; y }
  }
}

```

// FIXME: Need to qualifiy the constructors or otherwise they desugar to
// the (not yet in scope) type below. Only in batch mode apparently.
```pulse
fn test3_5 (n:option int) (z:bool)
  requires emp
  returns r:int
  ensures emp
{
  match n {
    Pervasives.None -> { (-1) }
    Pervasives.Some x -> { x }
  }
}
```

noeq
type optionint =
  | None
  | Some of int

```pulse
fn test4 (n:optionint) (z:bool)
  requires emp
  returns r:int
  ensures emp
{
  match n {
    None -> { 0 }
    Some x -> { x }
  }
}
```

```pulse
fn test5 (n:option int) (z:bool)
  requires emp
  returns r:int
  ensures emp
{
  match n {
    Pervasives.None -> { (-1) }
    Pervasives.Some x -> { x }
  }
}
```

```pulse
fn listid (xs : list int)
  requires emp
  returns r:(list int)
  ensures emp
{
  match xs {
    Nil -> { Nil #int }
    Cons hd tl -> { Cons #int hd tl }
  }
}
```

```pulse
fn hd (xs : list int)
  requires emp
  returns r:(int)
  ensures emp
{
  match xs {
    Nil -> { 0 }
    Cons hd tl -> { let t = tl; hd }
  }
}
```

```pulse
fn tl (xs : list int)
  requires emp
  returns r:(list u#0 int)
  ensures emp
{
  match xs {
    Nil -> { Nil #int }
    Cons hd tl -> { tl }
  }
}
```

[@@expect_failure [228]]
```pulse
fn incomplete (xs : list int)
  requires emp
  returns r:int
  ensures emp
{
  match xs {
    Nil -> { 1 }
  }
}
```

```pulse
fn partial_complete (xs : (xs:list int{List.length xs == 0}))
  requires emp
  returns r:int
  ensures emp
{
  match xs {
    Nil -> { 1 }
  }
}
```

```pulse
fn breq_1 (xs : list int)
  requires emp
  returns r:int
  ensures emp
{
  match xs {
    Nil -> { assert (pure (List.Tot.length xs == 0)); 0 } // works because of branch eq
    Cons _ _ -> { 1 } // assert (pure (isCons xs)); cons_hd xs }
  }
}
```

```pulse
fn breq_2 (xs : list int)
  requires emp
  returns r:int
  ensures emp
{
  match xs {
    Nil -> { assert (pure (List.Tot.length xs == 0)); 0 }
    Cons _ _ -> { Cons?.hd xs }
  }
}
```
