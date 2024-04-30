(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Pulse.Lib.OnRange

open Pulse.Lib.Pervasives
open Pulse.Lib.Stick

let rec on_range p i j : Tot vprop (decreases j - i) =
  if i < j
  then p i ** on_range p (i + 1) j
  else if i = j
  then emp
  else pure False

let on_range_elim_lt (p:nat -> vprop) (i j:nat)
  : Lemma (requires i < j)
          (ensures on_range p i j == p i ** on_range p (i + 1) j) = ()

let on_range_elim_eq (p:nat -> vprop) (i j:nat)
  : Lemma (requires i == j)
          (ensures on_range p i j == emp) = ()

let on_range_elim_gt (p:nat -> vprop) (i j:nat)
  : Lemma (requires j < i)
          (ensures on_range p i j == pure False) = ()

let rec on_range_is_small p i j
  : Lemma (requires forall k. (i <= k /\ k < j) ==> is_small (p k))
          (ensures is_small (on_range p i j))
          (decreases j - i) =
  if i < j
  then on_range_is_small p (i + 1) j
  else ()

```pulse
ghost
fn on_range_le (p:nat -> vprop) (#i #j:nat)
  requires on_range p i j
  ensures on_range p i j ** pure (i <= j)
{
  if (j < i) {
    rewrite (on_range p i j) as
            (pure False);
    unreachable ()
  } else { () }
}
```

```pulse
ghost
fn on_range_empty (p:nat -> vprop) (i:nat)
  requires emp
  ensures on_range p i i
{
  rewrite emp as (on_range p i i)
} 
```

```pulse
ghost
fn on_range_singleton_intro (p:nat -> vprop) (i:nat)
  requires p i
  ensures on_range p i (i + 1)
{
  rewrite (p i ** emp) as (on_range p i (i + 1))
}
```

```pulse
ghost
fn on_range_singleton_elim () (#p:nat -> vprop) (#i:nat) (#j:nat { j == i + 1 })
  requires on_range p i j
  ensures p i
{
  rewrite (on_range p i j) as (p i ** emp)
}
```

```pulse
ghost
fn rec on_range_split (j:nat) (#p:nat -> vprop) (#i:nat { i <= j }) (#k:nat { j <= k })
  requires on_range p i k
  ensures on_range p i j ** on_range p j k
  decreases (j - i)
{
  if (j = i) {
    rewrite (emp ** on_range p i k) as (on_range p i j ** on_range p j k)
  } else {
    rewrite (on_range p i k) as (p i ** on_range p (i + 1) k);
    on_range_split j #p #(i + 1) #k;
    rewrite (p i ** on_range p (i + 1) j) as (on_range p i j)
  }
}
```

```pulse
ghost
fn rec on_range_join (i j k:nat) (#p:nat -> vprop)
  requires on_range p i j ** on_range p j k
  ensures on_range p i k
  decreases (j - i)
{
  on_range_le p #i #j;
  on_range_le p #j #k;
  if (i < j) {
    rewrite (on_range p i j) as (p i ** on_range p (i + 1) j);
    on_range_join (i + 1) j k;
    rewrite (p i ** on_range p (i + 1) k) as (on_range p i k)
  } else if (j = i) {
    rewrite (on_range p i j ** on_range p j k) as (emp ** on_range p i k)
  } else {
    unreachable ()
  }
}
```

```pulse
ghost
fn on_range_cons (i:nat) (#p:nat -> vprop) (#j:nat { j == i + 1 }) (#k:nat)
  requires p i ** on_range p j k
  ensures on_range p i k
{
  on_range_le p;
  rewrite (p i ** on_range p j k) as (on_range p i k)
}
```

```pulse
ghost
fn on_range_uncons () (#p:nat -> vprop) (#i:nat) (#k:nat { i < k })
  requires on_range p i k
  ensures p i ** on_range p (i + 1) k
{
  rewrite (on_range p i k) as (p i ** on_range p (i + 1) k)
}
```

```pulse
ghost
fn on_range_cons_with_implies (i:nat) (#p:nat -> vprop) (#k:nat)
  requires p i ** on_range p (i + 1) k
  ensures on_range p i k **
          (on_range p i k @==> (p i ** on_range p (i + 1) k))
{
  on_range_le p;
  rewrite (p i ** on_range p (i + 1) k) as (on_range p i k);

  ghost
  fn aux ()
    requires emp ** on_range p i k
    ensures p i ** on_range p (i + 1) k
  {
    on_range_uncons ()
  };

  intro_stick _ _ _ aux
}
```

```pulse
ghost
fn rec on_range_snoc () (#p:nat -> vprop) (#i #j:nat)
  requires on_range p i j ** p j
  ensures on_range p i (j + 1)
  decreases (j - i)
{
  on_range_le p;
  if (i < j) {
    rewrite (on_range p i j) as (p i ** on_range p (i + 1) j);
    on_range_snoc ();
    rewrite (p i ** on_range p (i + 1) (j + 1)) as (on_range p i (j + 1))
  } else if (i = j) {
    rewrite (on_range p i j ** (p j ** emp)) as (emp ** on_range p i (j + 1))
  } else {
    unreachable ()
  }
}
```

```pulse
ghost
fn rec on_range_unsnoc () (#p:nat -> vprop) (#i:nat) (#k:nat { i < k })
  requires on_range p i k
  ensures on_range p i (k - 1) ** p (k - 1)
  decreases (k - i)
{
  rewrite (on_range p i k) as (p i ** on_range p (i + 1) k);
  if (i < k - 1) {
    on_range_unsnoc ();
    rewrite (p i ** on_range p (i + 1) (k - 1)) as (on_range p i (k - 1))
  } else if (i = k - 1) {
    rewrite (p i ** on_range p (i + 1) k) as (p (k - 1) ** on_range p i (k - 1))
  } else {
    unreachable ()
  }
}
```

```pulse
ghost
fn on_range_snoc_with_implies () (#p:nat -> vprop) (#i #j:nat)
  requires on_range p i j ** p j
  ensures on_range p i (j + 1) **
          (on_range p i (j + 1) @==> (on_range p i j ** p j))
{
  on_range_le p;
  on_range_snoc ();
  ghost
  fn aux ()
    requires emp ** on_range p i (j + 1)
    ensures on_range p i j ** p j
  {
    on_range_unsnoc () #p #i #(j + 1);
    rewrite (p ((j + 1) - 1)) as p j
  };
  intro_stick _ _ _ aux;
}
```

```pulse
ghost
fn on_range_get (j:nat) (#p:nat -> vprop) (#i:nat { i <= j }) (#k:nat { j < k })
  requires on_range p i k
  ensures on_range p i j ** p j ** on_range p (j + 1) k
  decreases (j - i)
{
  on_range_split j;
  on_range_uncons () #p #j #k
}
```

```pulse
ghost
fn on_range_put (i:nat) (j:nat { i <= j }) (k:nat { j < k }) (#p:nat -> vprop)
  requires on_range p i j ** p j ** on_range p (j + 1) k
  ensures on_range p i k
{
  on_range_cons j #p #(j + 1) #k;
  on_range_join i j k
}
```

```pulse
ghost
fn on_range_focus (j:nat) (#p:nat -> vprop) (#i:nat { i <= j }) (#k:nat { j < k })
  requires on_range p i k
  ensures p j ** (p j @==> on_range p i k)
{
  on_range_get j #p #i #k;
  ghost
  fn aux ()
    requires (on_range p i j ** on_range p (j + 1) k) ** p j
    ensures on_range p i k
  {
    on_range_put i j k
  };

  intro_stick _ _ _ aux
}
```

```pulse
ghost
fn rec on_range_weaken_and_shift (p p':nat -> vprop) (delta:int)
  (i j:(k:nat { 0 <= k + delta }))
  (phi:(k:nat { i <= k /\ k < j }) -> stt_ghost unit emp_inames (p k) (fun _ -> p' (k + delta)))
  requires on_range p i j
  ensures on_range p' (i + delta) (j + delta)
  decreases (j - i)
{
  on_range_le p;
  if (i < j) {
    on_range_uncons ();
    on_range_weaken_and_shift p p' delta (i + 1) j (fun k -> phi k);
    phi i;
    on_range_cons (i + delta)
  } else if (i = j) {
    rewrite (on_range p i j) as (on_range p' (i + delta) (j + delta))
  } else {
    unreachable ()
  }
}
```

```pulse
ghost
fn on_range_weaken
  (p p':nat -> vprop)
  (i:nat)
  (j:nat)
  (phi:(k: nat { i <= k /\ k < j }) -> stt_ghost unit emp_inames (p k) (fun _ -> p' k))
    requires on_range p i j
    ensures on_range p' i j
{
  on_range_weaken_and_shift p p' 0 i j phi
}
```
