module Pulse.Lib.Stick.Util
open Pulse.Lib.Pervasives
include Pulse.Lib.Stick

```pulse
ghost
fn refl (p:vprop)
   requires emp
   ensures p @==> p
{
    ghost fn intro_stick_aux (u:unit)
    requires emp ** p
    ensures p
    { () };
    Pulse.Lib.Stick.intro_stick _ _ _ intro_stick_aux;
    fold (p @==> p);
}
```

```pulse
ghost
fn curry (p q r:vprop)
   requires (p ** q) @==> r
   ensures p @==> (q @==> r)
{
    ghost fn aux (_:unit)
    requires ((p ** q) @==> r) ** p
    ensures q @==> r
    { 
        ghost fn aux (_:unit)
        requires (((p ** q) @==> r) ** p) ** q
        ensures r
        { 
            unfold ((p ** q) @==> r);
            elim_stick (p ** q) _;
        };
        intro_stick _ _ _ aux; 
        fold (q @==> r);
    };
    intro_stick _ _ _ aux;
    fold (p @==> (q @==> r));
}
```


```pulse
ghost
fn trans (p q r:vprop)
    requires (p @==> q) ** (q @==> r)
    ensures p @==> r
{
   ghost fn aux (_:unit)
   requires ((p @==> q) ** (q @==> r)) ** p
   ensures r
   { 
      unfold (p @==> q);
      elim_stick _ _;
      
      unfold (q @==> r);
      elim_stick _ _;
   };
   intro_stick _ _ _ aux;
   fold (p @==> r);
}
```

```pulse
ghost
fn comm_l (p q r:vprop)
   requires (p ** q) @==> r
   ensures (q ** p) @==> r
{
    ghost fn aux (_:unit)
    requires ((p ** q) @==> r) ** (q ** p)
    ensures r
    { 
        unfold (p ** q) @==> r;
        elim_stick (p ** q) _;
    };
    intro_stick _ _ _ aux; 
    fold ((q ** p) @==> r);
}
```

```pulse
ghost
fn comm_r (p q r:vprop)
   requires p @==> (q ** r)
   ensures p @==> (r ** q)
{
    ghost fn aux (_:unit)
    requires (p @==> (q ** r)) ** p
    ensures r ** q
    { 
        unfold (p @==> (q ** r));
        elim_stick p (q ** r);
    };
    intro_stick _ _ _ aux; 
    fold (p @==> (r ** q));
}
```

```pulse
ghost
fn assoc_l (p q r s:vprop)
   requires (p ** (q ** r)) @==> s
   ensures ((p ** q) ** r) @==> s
{
    ghost fn aux (_:unit)
    requires ((p ** (q ** r)) @==> s) ** ((p ** q) ** r)
    ensures s
    { 
        unfold (p ** (q ** r)) @==> s;
        elim_stick (p ** (q ** r)) _;
    };
    intro_stick _ _ _ aux;
    fold (((p ** q) ** r) @==> s);
}
```

```pulse
ghost
fn assoc_r (p q r s:vprop)
   requires p @==> ((q ** r) ** s)
   ensures p @==> (q ** (r ** s))
{
    ghost fn aux (_:unit)
    requires (p @==> ((q ** r) ** s)) ** p
    ensures q ** (r ** s)
    { 
        unfold (p @==> ((q ** r) ** s));
        elim_stick p ((q ** r) ** s);
    };
    intro_stick _ _ _ aux;
    fold (p @==> (q ** (r ** s)));
}
```


```pulse
ghost
fn elim (p q:vprop)
   requires (p @==> q) ** p
   ensures q
{
  unfold (p @==> q);
  elim_stick #emp_inames p q;
}
```


```pulse
ghost
fn elim_hyp_l (p q r:vprop)
    requires ((p ** q) @==> r) ** p
    ensures (q @==> r)
{
    curry p q r;
    elim _ _;
}
```

```pulse
ghost
fn elim_hyp_r (p q r:vprop)
    requires ((p ** q) @==> r) ** q
    ensures (p @==> r)
{
    comm_l p q r;
    curry q p r;
    elim _ _;
}
```
