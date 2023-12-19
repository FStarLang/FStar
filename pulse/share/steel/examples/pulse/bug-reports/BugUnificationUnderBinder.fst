module BugUnificationUnderBinder
open Pulse.Lib.Pervasives

assume
val p (x:int) (y:int) : vprop

```pulse
fn test (_:unit)
requires exists* x. p x 5
ensures emp
{
    with zz. assert (exists* x. p x zz);
    drop_ _;
}
```

```pulse
fn test_fa (_:unit)
requires forall* x. p x 5
ensures emp
{
    with zz. assert (forall* x. p x zz);
    drop_ _;
} 
```

assume
val is_list (l:list int) : vprop
open FStar.List.Tot

let aux (l1 l2:list 'a) (x:'a) 
: Lemma 
    (ensures l1@(x::l2) == (l1 @ [x])@l2)
    [SMTPat (l1@(x::l2))]
= List.Tot.Properties.append_assoc l1 [x] l2

```pulse
fn test1 (pfx:list int) (hd:int)
requires forall* tl. is_list (pfx @ (hd::tl))
ensures emp
{
    rewrite (forall* tl. is_list (pfx @ (hd::tl)))
          as (forall* tl. is_list ((pfx @ [hd])@tl));
    admit()
}
```