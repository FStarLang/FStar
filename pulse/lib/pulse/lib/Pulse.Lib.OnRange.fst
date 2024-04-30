module Pulse.Lib.OnRange

open Pulse.Lib.Pervasives
open Pulse.Lib.Stick

let rec on_range
  (p: (nat -> vprop))
  (i j: nat)
: Tot vprop
  (decreases (if j <= i then 0 else j - i))
= if j < i
  then pure False
  else if j = i
  then emp
  else p i ** on_range p (i + 1) j

let on_range_eq_false (p:nat -> vprop) (i j:nat)
: Lemma 
  (requires i > j)
  (ensures on_range p i j == pure False)
= ()

let on_range_eq_emp (p:nat -> vprop) (i j:nat)
: Lemma 
  (requires i == j)
  (ensures on_range p i j == emp)
= ()

let on_range_eq_cons (p:nat -> vprop) (i j:nat)
: Lemma 
  (requires i < j)
  (ensures on_range p i j == (p i ** on_range p (i + 1) j))
= ()

let rec on_range_is_small (p:nat -> vprop) (i:nat) (j:nat)
: Lemma (requires forall k. (i <= k /\ k < j) ==> is_small (p k))
        (ensures is_small (on_range p i j))
        (decreases (if j <= i then 0 else j - i))
= if j < i
  then ()
  else if j = i
  then ()
  else on_range_is_small p (i + 1) j

let rec on_range_is_big (p:nat -> vprop) (i:nat) (j:nat)
: Lemma (requires forall k. (i <= k /\ k < j) ==> is_big (p k))
        (ensures is_big (on_range p i j))
        (decreases (if j <= i then 0 else j - i))
= if j < i
  then ()
  else if j = i
  then ()
  else on_range_is_big p (i + 1) j

```pulse
ghost
fn on_range_le
    (p: (nat -> vprop))
    (#i:nat)
    (#j:nat)
requires on_range p i j
ensures on_range p i j ** pure (i <= j)
{
  if (j < i)
  {
    rewrite (on_range p i j) as pure False;
    unreachable ()
  }
  else {
    ()
  }
}
```

```pulse
ghost
fn on_range_empty
  (p: (nat -> vprop))
  (i: nat)
requires emp
ensures on_range p i i
{
  rewrite emp as on_range p i i;
}
```

```pulse
ghost
fn on_range_singleton_intro
  (p: (nat -> vprop))
  (i: nat)
requires p i
ensures on_range p i (i + 1)
{
  on_range_empty p (i + 1);
  rewrite (p i ** on_range p (i + 1) (i + 1))
      as  (on_range p i (i + 1))
}
```

```pulse
ghost
fn on_range_singleton_elim
  ()
  (#p: (nat -> vprop))
  (#i:nat)
  (#j:nat { j == i + 1 })
requires on_range p i j
ensures p i
{
  rewrite (on_range p i j) as (p i ** on_range p (i + 1) j);
  rewrite (on_range p (i + 1) j) as emp;
}
```

```pulse
ghost
fn rec on_range_split
  (j:nat)
  (#p: (nat -> vprop))
  (#i:nat{ i <= j })
  (#k:nat{ j <= k })
requires on_range p i k
ensures on_range p i j ** on_range p j k
decreases (j - i)
{
  if (i = j)
  {
    rewrite emp as on_range p i j;
  }
  else
  {
    rewrite (on_range p i k) as (p i ** on_range p (i + 1) k);
    on_range_split j;
    rewrite (p i ** on_range p (i + 1) j) as (on_range p i j);
  }
}
```

```pulse
ghost
fn rec on_range_join
  (i j k: nat)
  (#p: (nat -> vprop))
requires on_range p i j ** on_range p j k
ensures on_range p i k
decreases (j - i)
{
  on_range_le p #i #j;
  if (i = j)
  {
    rewrite (on_range p i j) as emp;
  }
  else
  {
    rewrite (on_range p i j) as (p i ** on_range p (i + 1) j);
    on_range_join (i + 1) j k;
    on_range_le p #(i + 1) #k;
    rewrite (p i ** on_range p (i + 1) k) as (on_range p i k);
  }
}
```

```pulse
ghost
fn on_range_cons
  (i:nat)
  (#p: (nat -> vprop))
  (#j:nat{j == i + 1})
  (#k: nat)
requires p i ** on_range p j k
ensures on_range p i k
{
  on_range_le p #j #k;
  rewrite (p i ** on_range p j k) as (on_range p i k);
}
```

```pulse
ghost
fn on_range_uncons
  ()
  (#p: (nat -> vprop))
  (#i:nat)
  (#k:nat { i < k })
requires on_range p i k
ensures p i ** on_range p (i + 1) k
{
  rewrite (on_range p i k) as (p i ** on_range p (i + 1) k);
}
```

```pulse
ghost
fn on_range_cons_with_implies
  (i:nat)
  (#p: (nat -> vprop))
  (#k: nat)
requires p i ** on_range p (i + 1) k
ensures on_range p i k ** (on_range p i k @==> (p i ** on_range p (i + 1) k))
{
  on_range_le p #(i + 1) #k;
  ghost
  fn aux ()
  requires emp ** on_range p i k
  ensures p i ** on_range p (i + 1) k
  {
    rewrite (on_range p i k) as (p i ** on_range p (i + 1) k);
  };
  Pulse.Lib.Stick.intro_stick _ _ _ aux;
  with a b. rewrite (stick a b) as (a @==> b);
  rewrite (p i ** on_range p (i + 1) k) as (on_range p i k);
}
```


```pulse
ghost
fn rec on_range_snoc
  ()
  (#p: (nat -> vprop))
  (#i #j:nat)
requires on_range p i j ** p j
ensures on_range p i (j + 1)
decreases (if j <= i then 0 else j - i)
{
  on_range_le p #i #j;
  if (i = j) 
  {
    rewrite (on_range p i j) as emp;
    rewrite (p j ** emp) as (on_range p i (j + 1))
  }
  else
  {
    rewrite (on_range p i j) as (p i ** on_range p (i + 1) j);
    on_range_snoc () #p #(i + 1) #j;
    on_range_le p;
    rewrite (p i ** on_range p (i + 1) (j + 1)) as (on_range p i (j + 1));
  }
}
```

```pulse
ghost
fn rec on_range_unsnoc
  ()
  (#p: (nat -> vprop))
  (#i:nat)
  (#k:nat{ i < k })
requires on_range p i k
ensures on_range p i (k - 1) ** p (k - 1)
decreases (k - i)
{
  if (i = k - 1)
  {
    rewrite on_range p i k as (p (k - 1) ** on_range p i (k - 1));
  }
  else
  {
    rewrite on_range p i k as (p i ** on_range p (i + 1) k);
    on_range_unsnoc ();
    rewrite (p i ** on_range p (i + 1) (k - 1)) as (on_range p i (k - 1));
  }
}
```

```pulse
ghost
fn on_range_snoc_with_implies
  ()
  (#p: (nat -> vprop))
  (#i:nat)
  (#j:nat)
requires on_range p i j ** p j
ensures on_range p i (j + 1) **  (on_range p i (j + 1) @==> (on_range p i j ** p j))
{
  on_range_le p #i #j;
  ghost
  fn aux ()
  requires emp ** on_range p i (j + 1)
  ensures on_range p i j ** p j
  {
    on_range_unsnoc ();
    rewrite (p (j + 1 - 1)) as (p j)
  };
  Pulse.Lib.Stick.intro_stick _ _ _ aux;
  with a b. rewrite (stick a b) as (a @==> b);
  on_range_snoc()
}
```

```pulse
ghost
fn rec on_range_get
  (j:nat)
  (#p: (nat -> vprop))
  (#i:nat{i <= j})
  (#k:nat{j < k})
requires on_range p i k
ensures on_range p i j ** p j ** on_range p (j + 1) k
decreases (j - i)
{
  if (j = i)
  {
    rewrite (on_range p i k) as (p j ** on_range p (i + 1) k);
    rewrite emp as on_range p i j;
  }
  else
  {
    rewrite (on_range p i k) as (p i ** on_range p (i + 1) k);
    on_range_get j;
    rewrite (p i ** on_range p (i + 1) j) as (on_range p i j);
  }
}
```

```pulse
ghost
fn rec on_range_put
  (i:nat)
  (j:nat{ i <= j })
  (k:nat{ j < k })
  (#p: (nat -> vprop))
requires on_range p i j ** p j ** on_range p (j + 1) k
ensures on_range p i k
decreases (j - i)
{
  if (j = i)
  {
    rewrite (p j ** on_range p (j + 1) k) as (on_range p i k);
    rewrite on_range p i j as emp;
  }
  else
  {
    rewrite (on_range p i j) as (p i ** on_range p (i + 1) j);
    on_range_put (i + 1) j k;
    on_range_le p;
    rewrite (p i ** on_range p (i + 1) k) as (on_range p i k);
  }
}
```


```pulse
ghost
fn on_range_focus
  (j:nat)
  (#p: (nat -> vprop))
  (#i:nat{ i <= j })
  (#k:nat{ j < k })
requires on_range p i k
ensures p j ** (p j @==> on_range p i k)
{
  on_range_get j;
  ghost
  fn aux ()
  requires (on_range p i j ** on_range p (j + 1) k) ** p j
  ensures on_range p i k
  {
    on_range_put i j k;
  };
  Pulse.Lib.Stick.intro_stick _ _ _ aux;
  with a b. rewrite (stick a b) as (a @==> b);
}
```


```pulse
ghost
fn rec on_range_weaken_and_shift
  (p p': (nat -> vprop))
  (delta: int)
  (i: nat { i + delta >= 0 })
  (j: nat { j + delta >= 0 })
  (phi: (k: nat { i <= k /\ k < j }) -> stt_ghost unit emp_inames(p k) (fun _ -> p' (k + delta)))
requires on_range p i j
ensures on_range p' (i + delta) (j + delta)
decreases (if j <= i then 0 else j - i)
{
  on_range_le p;
  if (i = j)
  {
    rewrite (on_range p i j) as emp;
    rewrite emp as on_range p' (i + delta) (j + delta);
  }
  else
  {
    rewrite (on_range p i j) as (p i ** on_range p (i + 1) j);
    ghost
    fn phi_aux (k:nat { i + 1 <= k /\ k < j })
    requires p k
    ensures p' (k + delta)
    {
      phi k
    };
    on_range_weaken_and_shift p p' delta (i + 1) j phi_aux;
    phi i;
    on_range_cons (i + delta) #p' #_ #_;
  }
}
```

let on_range_weaken
  (p p': (nat -> vprop))
  (i: nat)
  (j: nat)
  (phi: (k: nat { i <= k /\ k < j }) -> stt_ghost unit emp_inames (p k) (fun _ -> p' k))
: stt_ghost unit emp_inames
    (on_range p i j)
    (fun _ -> on_range p' i j)
= on_range_weaken_and_shift p p' 0 i j phi
