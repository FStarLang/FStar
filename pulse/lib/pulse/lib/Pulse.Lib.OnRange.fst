module Pulse.Lib.OnRange
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Stick

let rec on_range
  ([@@@mkey]p: (nat -> slprop))
  ([@@@mkey]i j: nat)
: Tot slprop
  (decreases (if j <= i then 0 else j - i))
= if j < i
  then pure False
  else if j = i
  then emp
  else p i ** on_range p (i + 1) j

let on_range_eq_false (p:nat -> slprop) (i j:nat)
: Lemma 
  (requires i > j)
  (ensures on_range p i j == pure False)
= ()

let on_range_eq_emp (p:nat -> slprop) (i j:nat)
: Lemma 
  (requires i == j)
  (ensures on_range p i j == emp)
= ()

let on_range_eq_cons (p:nat -> slprop) (i j:nat)
: Lemma 
  (requires i < j)
  (ensures on_range p i j == (p i ** on_range p (i + 1) j))
= ()

let rec on_range_eq_get (p:nat -> slprop) (i j k:nat)
: Lemma 
  (requires i <= j /\ j < k)
  (ensures on_range p i k == (on_range p i j ** p j ** on_range p (j + 1) k))
  (decreases j - i)
= if i = j
  then ( slprop_equivs () )
  else (
    on_range_eq_get p (i + 1) j k;
    slprop_equivs()
  )

let rec on_range_eq_snoc (p:nat -> slprop) (i j:nat)
: Lemma 
  (requires i <= j)
  (ensures on_range p i (j + 1) == on_range p i j ** p j)
  (decreases j - i)
= if j = i
  then slprop_equivs ()
  else (
    on_range_eq_snoc p (i + 1) j;
    slprop_equivs()
  )

let rec on_range_frame (p q:nat -> slprop) (i j:nat)
: Lemma 
  (requires forall k. i <= k /\ k < j ==> p k == q k)
  (ensures on_range p i j == on_range q i j)
  (decreases (if (j <= i) then 0 else j - i))
= if j <= i
  then ()
  else (
    on_range_frame p q (i + 1) j
  )

let rec on_range_timeless (p:nat -> slprop) (i:nat) (j:nat)
: Lemma (requires forall k. (i <= k /\ k < j) ==> timeless (p k))
        (ensures timeless (on_range p i j))
        (decreases (if j <= i then 0 else j - i))
= if j < i
  then ()
  else if j = i
  then ()
  else on_range_timeless p (i + 1) j

let rec on_range_join_eq
  (i j k: nat)
  (p: (nat -> slprop))
: Lemma 
  (requires i <= j /\ j <= k)
  (ensures ((on_range p i j ** on_range p j k) == on_range p i k))
  (decreases (j - i))
= if i = j 
  then slprop_equivs ()
  else ( 
    calc (==) {
      on_range p i j ** on_range p j k;
    (==) {}
      (p i ** on_range p (i + 1) j) ** on_range p j k;
    (==) {slprop_equivs()}
      p i ** (on_range p (i + 1) j ** on_range p j k);
    (==) { on_range_join_eq (i + 1) j k p }
      p i ** (on_range p (i + 1) k);
    (==) { on_range_eq_cons p i k }
      on_range p i k;
    }
  )

ghost
fn on_range_le
    (p: (nat -> slprop))
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

ghost
fn on_range_empty
  (p: (nat -> slprop))
  (i: nat)
requires emp
ensures on_range p i i
{
  rewrite emp as on_range p i i;
}



ghost
fn on_range_empty_elim
  (p: (nat -> slprop))
  (i: nat)
requires on_range p i i
ensures emp
{
  rewrite (on_range p i i) as emp;
}



ghost
fn on_range_singleton_intro
  (p: (nat -> slprop))
  (i: nat)
requires p i
ensures on_range p i (i + 1)
{
  on_range_empty p (i + 1);
  rewrite (p i ** on_range p (i + 1) (i + 1))
      as  (on_range p i (i + 1))
}



ghost
fn on_range_singleton_elim
  ()
  (#p: (nat -> slprop))
  (#i:nat)
  (#j:nat { j == i + 1 })
requires on_range p i j
ensures p i
{
  rewrite (on_range p i j) as (p i ** on_range p (i + 1) j);
  rewrite (on_range p (i + 1) j) as emp;
}



ghost
fn rec on_range_split
  (j:nat)
  (#p: (nat -> slprop))
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



ghost
fn on_range_join
  (i j k: nat)
  (#p: (nat -> slprop))
requires on_range p i j ** on_range p j k
ensures on_range p i k
decreases (j - i)
{
  on_range_le p #i #j;
  on_range_le p #j #k;
  on_range_join_eq i j k p;
  rewrite (on_range p i j ** on_range p j k) as (on_range p i k);
}



ghost
fn on_range_cons
  (i:nat)
  (#p: (nat -> slprop))
  (#j:nat{j == i + 1})
  (#k: nat)
requires p i ** on_range p j k
ensures on_range p i k
{
  on_range_le p #j #k;
  rewrite (p i ** on_range p j k) as (on_range p i k);
}



ghost
fn on_range_uncons
  ()
  (#p: (nat -> slprop))
  (#i:nat)
  (#k:nat { i < k })
requires on_range p i k
ensures p i ** on_range p (i + 1) k
{
  rewrite (on_range p i k) as (p i ** on_range p (i + 1) k);
}



ghost
fn on_range_cons_with_implies
  (i:nat)
  (#p: (nat -> slprop))
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
  rewrite (p i ** on_range p (i + 1) k) as (on_range p i k);
}




ghost
fn rec on_range_snoc
  ()
  (#p: (nat -> slprop))
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



ghost
fn rec on_range_unsnoc
  ()
  (#p: (nat -> slprop))
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



ghost
fn on_range_snoc_with_implies
  ()
  (#p: (nat -> slprop))
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
  on_range_snoc()
}



ghost
fn rec on_range_get
  (j:nat)
  (#p: (nat -> slprop))
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



ghost
fn rec on_range_put
  (i:nat)
  (j:nat{ i <= j })
  (k:nat{ j < k })
  (#p: (nat -> slprop))
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




ghost
fn on_range_focus
  (j:nat)
  (#p: (nat -> slprop))
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
}




ghost
fn rec on_range_weaken_and_shift
  (p p': (nat -> slprop))
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


let on_range_weaken
  (p p': (nat -> slprop))
  (i: nat)
  (j: nat)
  (phi: (k: nat { i <= k /\ k < j }) -> stt_ghost unit emp_inames (p k) (fun _ -> p' k))
: stt_ghost unit emp_inames
    (on_range p i j)
    (fun _ -> on_range p' i j)
= on_range_weaken_and_shift p p' 0 i j phi


ghost
fn rec on_range_zip (p q:nat -> slprop) (i j:nat)
  requires on_range p i j ** on_range q i j
  ensures on_range (fun k -> p k ** q k) i j
  decreases (j-i)
{
  if (j < i) {
    on_range_eq_false p i j;
    rewrite (on_range p i j) as pure False;
    unreachable ();
  } else if (j = i) {
    rewrite each j as i;
    on_range_empty_elim p i;
    on_range_empty_elim q i;
    on_range_empty (fun k -> p k ** q k) i;
  } else {
    on_range_uncons () #p;
    on_range_uncons () #q;
    on_range_zip p q (i + 1) j;
    on_range_cons i #(fun k -> p k ** q k);
  }
}



ghost
fn rec on_range_unzip (p q:nat -> slprop) (i j:nat)
  requires on_range (fun k -> p k ** q k) i j
  ensures  on_range p i j ** on_range q i j
  decreases (j-i)
{
  if (j < i) {
    on_range_eq_false (fun k -> p k ** q k) i j;
    rewrite (on_range (fun k -> p k ** q k) i j) as pure False;
    unreachable ();
  } else if (j = i) {
    on_range_empty_elim (fun k -> p k ** q k) i;
    on_range_empty p i;
    on_range_empty q i;
    ();
  } else {
    on_range_uncons () #(fun k -> p k ** q k);
    on_range_unzip p q (i + 1) j;
    on_range_cons i #p;
    on_range_cons i #q;
  }
}

