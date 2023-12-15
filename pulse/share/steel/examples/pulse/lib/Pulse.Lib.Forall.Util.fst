module Pulse.Lib.Forall.Util
open Pulse.Lib.Pervasives
open Pulse.Lib.Stick.Util
module I = Pulse.Lib.Stick

```pulse
ghost
fn trans_compose (#a #b #c:Type0) (p:(a -> vprop)) (q:(b -> vprop)) (r:(c -> vprop))
                 (f: (a -> GTot b)) (g: (b -> GTot c))
    requires (forall* x. p x @==> q (f x)) ** (forall* x. q x @==> r (g x))
    ensures forall* x. p x @==> r (g (f x))
{
    ghost fn aux (x:a)
        requires ((forall* x. p x @==> q (f x)) ** (forall* x. q x @==> r (g x)))
        ensures p x @==> r (g (f x))
    {
        ghost fn aux (_:unit) 
        requires ((forall* x. p x @==> q (f x)) ** (forall* x. q x @==> r (g x))) ** p x
        ensures r (g (f x))
        {
            elim_forall #_ #(fun x -> p x @==> q (f x)) x;
            unfold (p x @==> q (f x));
            elim_stick _ _;
            elim_forall #_ #(fun x -> q x @==> r (g x)) (f x);
            unfold (q (f x) @==> r (g (f x)));
            elim_stick _ _;
        };
        intro_stick _ _ _ aux;
        fold (p x @==> r (g (f x)));
    };
    intro_forall _ aux
}
```

```pulse
ghost
fn trans (#a:Type0) (p q r: (a -> vprop))
    requires (forall* x. p x @==> q x) ** (forall* x. q x @==> r x)
    ensures forall* x. p x @==> r x
{
    trans_compose p q r id id
}
```

```pulse
ghost fn elim_forall_imp (#a:Type0) (p q: (a -> vprop)) (x:a)
    requires (forall* x. p x @==> q x) ** p x
    ensures q x
{
    elim_forall #_ #(fun x -> p x @==> q x) x;
    unfold (p x @==> q x);
    elim_stick _ _;
}
```
