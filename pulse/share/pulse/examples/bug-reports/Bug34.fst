module Bug34

open Pulse.Lib.Pervasives

class eq (a:Type) = {
  (=?) : a -> a -> bool
}

instance eq_int : eq int = {
  (=?) = (=);
}

```pulse
fn test (#a:Type0) {| eq a |} (x:a)
  requires emp
  returns _:bool
  ensures emp
{
  (x =? x)
}
```

```pulse
fn call ()
  requires emp
  ensures  emp
{
  let x : bool = test 123;
  ()
}
```
