module Bug107

open Pulse.Lib.Pervasives

val foo : int -> int -> vprop
let foo x y = emp

```pulse
fn test0 ()
  requires foo 1 2
  ensures emp
{
  unfold foo 1 2;
  ()
}
```

```pulse
fn test1 ()
  requires foo 1 2
  ensures emp
{
  unfold foo;
  ()
}
```

```pulse
fn test2 ()
  requires foo 1 2
  ensures emp
{
  unfold foo 1;
  ()
}
```

[@@expect_failure] // should work
```pulse
fn test3 ()
  requires foo 1 2
  ensures emp
{
  unfold foo 1 _;
  ()
}
```

[@@expect_failure] // should work
```pulse
fn test4 ()
  requires foo 1 2
  ensures emp
{
  unfold foo _ 2;
  ()
}
```
