module Example.Ghost
open Pulse.Lib.Pervasives

//calling a function declared in F* as ghost fails
[@@expect_failure]
```pulse
ghost
fn test_elim_false (a:Type0) (p:(a -> vprop))
    requires pure False
    returns x:a
    ensures p x
{
    elim_false a p;
}
```

// You can return anything in Ghost, it doesn't have to be non-informative
```pulse
ghost
fn ret (#a:Type0) (x:a)
    requires emp
    returns y:a
    ensures emp
{
    x
}
```


//You can also return it as erased, though you don't have to
```pulse
ghost
fn ret2 (#a:Type0) (x:a)
    requires emp
    returns y:erased a
    ensures emp
{
    hide x
}
```

//Admit is overloaded to work in all the effects, include ghost
```pulse
ghost
fn use_admit (t:Type0) (p:vprop)
    requires emp
    returns x:t
    ensures p
{
    admit()
}
```
