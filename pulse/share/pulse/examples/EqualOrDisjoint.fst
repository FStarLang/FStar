module EqualOrDisjoint
#lang-pulse
open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference
module TR = Pulse.Lib.Trade
open Pulse.Lib.Trade
open Pulse.Lib.Forall.Util

fn compare_pointers u#a (#a:Type u#a) (x y:ref a)
returns b:bool
ensures pure (b <==> (x==y))
{ admit() }

ghost
fn disjoint_neq u#a (#a:Type u#a) (x y:ref a) (#v1 #v2:a)
preserves x |-> v1 ** y |-> v2
ensures pure (x =!= y)
{
  let b:bool = FStar.StrongExcludedMiddle.strong_excluded_middle (x == y);
  if (b)
  { 
    rewrite each y as x;
    gather x;
    pts_to_perm_bound x;
    unreachable ()
  }
} 

let ite (p:prop) (x y:prop) = (p ==> x) /\ (~p ==> y)

let refs_eq_or_disjoint (#a:Type u#a) ([@@@mkey]x1:ref a) ([@@@mkey]x2:ref a) (v1 v2:a) =
  x1 |-> Frac 0.5R v1 **
  x2 |-> Frac 0.5R v2 **
  (exists* (eq:bool).
    cond eq 
        (pure (x1 == x2))
        (x1 |-> Frac 0.5R v1 ** x2 |-> Frac 0.5R v2))

ghost
fn flip_refs_eq_or_disjoint u#a (#a:Type u#a) ([@@@mkey]x1:ref a) ([@@@mkey]x2:ref a) (v1 v2:a)
requires refs_eq_or_disjoint x1 x2 v1 v2
ensures refs_eq_or_disjoint x2 x1 v2 v1
{
  unfold refs_eq_or_disjoint;
  with (eq:bool). assert cond eq _ _;

  let b:bool = reveal eq;
  if (b)
  {
    elim_cond_true _ _ _;
    intro_cond_true (pure (x2 == x1)) (x2 |-> Frac 0.5R v2 ** x1 |-> Frac 0.5R v1);
    fold refs_eq_or_disjoint x2 x1 v2 v1;
  }
  else
  {
    elim_cond_false _ _ _;
    intro_cond_false (pure (x2 == x1)) (x2 |-> Frac 0.5R v2 ** x1 |-> Frac 0.5R v1);
    fold refs_eq_or_disjoint x2 x1 v2 v1;
  }
}

ghost
fn intro_refs_eq u#a (#a:Type u#a) (x:ref a) (#v:erased a)
requires x |-> v
ensures refs_eq_or_disjoint x x v v
{
  share x;
  intro_cond_true (pure (x == x)) (x |-> Frac 0.5R v ** x |-> Frac 0.5R v);
  fold refs_eq_or_disjoint x x v v;
}

ghost
fn intro_refs_disjoint u#a (#a:Type u#a) (x1 x2:ref a) (#v1 #v2:erased a)
requires x1 |-> v1 ** x2 |-> v2
ensures refs_eq_or_disjoint x1 x2 v1 v2
{
  share x1; share x2;
  intro_cond_false (pure (x1 == x2)) (x1 |-> Frac 0.5R v1 ** x2 |-> Frac 0.5R v2);
  fold refs_eq_or_disjoint x1 x2 v1 v2;
}

ghost
fn elim_is_eq u#a (#a:Type u#a) (x1 x2:ref a) (#v1 #v2:a)
preserves refs_eq_or_disjoint x1 x2 v1 v2
requires pure (x1 == x2)
ensures pure (v1 == v2)
{
  unfold refs_eq_or_disjoint;
  with (eq:bool). assert cond eq _ _;
  let v : bool = reveal eq;
  if (v) 
  {
    rewrite (x2 |-> Frac 0.5R v2) as (x1 |-> Frac 0.5R v2);
    pts_to_injective_eq x1;
    rewrite (x1 |-> Frac 0.5R v2) as (x2 |-> Frac 0.5R v2);
    fold (refs_eq_or_disjoint x1 x2 v1 v2);
  }
  else
  {
    elim_cond_false _ _ _;
    gather x1;
    gather x2;
    disjoint_neq x1 x2;
    unreachable()
  }
}

ghost
fn get_full_x1 (#a:Type u#0) (x1 x2:ref a) (v1 v2:a)
requires refs_eq_or_disjoint x1 x2 v1 v2
ensures x1 |-> v1
ensures pure (x1==x2 ==> v1==v2)
ensures forall* v1'. 
  (x1 |-> v1') @==> 
  (exists* v2'. refs_eq_or_disjoint x1 x2 v1' v2' ** 
                pure (ite (x1==x2) (v2'==v1') (v2'==v2)))
{ 
  unfold refs_eq_or_disjoint;
  with (eq:bool). assert cond eq _ _;
  let v : bool = reveal eq;
  if (v) 
  {
    elim_cond_true _ _ _;
    rewrite each x2 as x1;
    gather x1;
    intro_forall_imp
      (fun v1' -> x1 |-> v1')
      (fun v1' ->
        exists* v2'. 
          refs_eq_or_disjoint x1 x2 v1' v2' **
          pure (ite (x1==x2) (v2'==v1') (v2'==v2)))
      emp
      fn v1' { 
        share x1;
        intro_cond_true
          (pure (x1 == x2))
          (x1 |-> Frac 0.5R v1' ** x2 |-> Frac 0.5R v1');
        rewrite (x1 |-> Frac 0.5R v1')
          as    (x2 |-> Frac 0.5R v1');
        fold (refs_eq_or_disjoint x1 x2 v1' v1');
      };
  }
  else
  {
    elim_cond_false _ _ _;
    gather x1;
    gather x2;
    disjoint_neq x1 x2;
    intro_forall_imp
      (fun v1' -> x1 |-> v1')
      (fun v1' ->
        exists* v2'.
          refs_eq_or_disjoint x1 x2 v1' v2' **
          pure (ite (x1==x2) (v2'==v1') (v2'==v2)))
      (x2 |-> v2)
      fn v1' { 
        share x1;
        share x2;
        intro_cond_false
          (pure (x1 == x2))
          (x1 |-> Frac 0.5R v1' ** x2 |-> Frac 0.5R v2);
        fold (refs_eq_or_disjoint x1 x2 v1' v2);
      };
  }
}

ghost
fn get_full_x2 (#a:Type u#0) (x1 x2:ref a) (v1 v2:a)
requires refs_eq_or_disjoint x1 x2 v1 v2
ensures x2 |-> v2
ensures pure (x1==x2 ==> v1==v2)
ensures forall* v2'. 
    (x2 |-> v2') @==> 
    (exists* v1'. refs_eq_or_disjoint x1 x2 v1' v2' ** 
        pure (ite (x1==x2) (v1'==v2') (v1'==v1)))
{
  flip_refs_eq_or_disjoint _ _ _ _;
  get_full_x1 _ _ _ _;
  intro_forall_imp #a
    (fun v2' -> x2 |-> v2')
    (fun v2' ->
      exists* v1'. 
        refs_eq_or_disjoint x1 x2 v1' v2' **
        pure (ite (x1==x2) (v1'==v2') (v1'==v1)))
    (forall* v2'. 
      (x2 |-> v2') @==> 
      (exists* v1'. refs_eq_or_disjoint x2 x1 v2' v1' ** 
          pure (ite (x2==x1) (v1'==v2') (v1'==v1))))
    fn v2' {
      elim_forall_imp _ _ v2';
      flip_refs_eq_or_disjoint x2 x1 _ _ ;
    };
}

ghost
fn elim_refs_eq u#a (#a:Type u#a) (x1 x2:ref a) (#v1 #v2:erased a)
requires refs_eq_or_disjoint x1 x2 v1 v2
requires pure (x1 == x2)
ensures x1 |-> v1
ensures pure (v1 == v2)
{
  elim_is_eq x1 x2;
  unfold refs_eq_or_disjoint;
  rewrite each x2 as x1;
  gather x1;
  drop_ (cond _ _ _);
}

ghost
fn intro_refs_disj u#a (#a:Type u#a) (x1 x2:ref a) (#v1 #v2:erased a)
requires x1 |-> v1 ** x2 |-> v2
ensures refs_eq_or_disjoint x1 x2 v1 v2
ensures pure (x1 =!= x2)
{
  disjoint_neq x1 x2;
  share x1;
  share x2;
  intro_cond_false
    (pure (x1 == x2))
    (x1 |-> Frac 0.5R v1 ** x2 |-> Frac 0.5R v2);
  fold refs_eq_or_disjoint;
}

ghost
fn elim_refs_disj  u#a (#a:Type u#a) (x1 x2:ref a) (#v1 #v2:erased a)
requires refs_eq_or_disjoint x1 x2 v1 v2
requires pure (x1 =!= x2)
ensures x1 |-> v1 ** x2 |-> v2
{
  unfold refs_eq_or_disjoint;
  with (eq:bool). assert (cond eq _ _);
  let v:bool = reveal eq;
  if (v)
  {
    elim_cond_true _ _ _;
    unreachable();
  }
  else
  { 
    elim_cond_false _ _ _;
    gather x1;
    gather x2;
  }
}


fn swap (#a:Type0) (x1 x2:ref a) (#v1 #v2:erased a)
requires refs_eq_or_disjoint x1 x2 v1 v2
ensures refs_eq_or_disjoint x1 x2 v2 v1
{
  if (compare_pointers x1 x2)
  {
    elim_is_eq x1 x2;
  }
  else
  {
    unfold refs_eq_or_disjoint;
    let u1 = !x1;
    let u2 = !x2;
    fold refs_eq_or_disjoint;
    get_full_x1 _ _ _ _;
    x1 := u2;
    elim_forall_imp _ _ _;
    get_full_x2 _ _ _ _;
    x2 := u1;
    elim_forall_imp _ _ _;
  }
}

fn swap_unopt (#a:Type0) (x1 x2:ref a) (#v1 #v2:erased a)
requires refs_eq_or_disjoint x1 x2 v1 v2
ensures refs_eq_or_disjoint x1 x2 v2 v1
{
  unfold refs_eq_or_disjoint;
  let u1 = !x1;
  let u2 = !x2;
  fold refs_eq_or_disjoint;
  get_full_x1 _ _ _ _;
  x1 := u2;
  elim_forall_imp _ _ _;
  get_full_x2 _ _ _ _;
  x2 := u1;
  elim_forall_imp _ _ _;
}

fn call_swap_eq (#a:Type0) (x:ref a) (#v:erased a)
requires x |-> v
ensures x |-> v
{
  intro_refs_eq x;
  swap x x;
  elim_refs_eq  _ _;
}

fn call_swap_disj (#a:Type0) (x1 x2:ref a) (#v1 #v2:erased a)
requires x1 |-> v1 ** x2 |-> v2
ensures x1 |-> v2 ** x2 |-> v1
{
  intro_refs_disj x1 x2;
  swap x1 x2;
  elim_refs_disj  _ _;
}