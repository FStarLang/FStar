(*
   Copyright 2025 Microsoft Research

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

module Pulse.Lib.Borrow
open Pulse.Lib.Pervasives
open Pulse.Lib.Shift
open Pulse.Lib.Trade
open Pulse.Lib.GhostReference
#lang-pulse

noeq type blockchain_node =
  | Split : blockchain_edge -> blockchain_edge -> blockchain_node
and blockchain_edge = {
  be_prop: slprop_ref;
  be_ref: ref blockchain_node;
}

let dummy_edge = { be_prop = null_slprop_ref; be_ref = null }
let dummy_node = Split dummy_edge dummy_edge

noeq type blockchain_root = {
  rt_tree: blockchain_edge;
  rt_returned: ref bool;
  rt_next: ref blockchain_root;
}

[@@erasable]
type lifetime : Type0 =
  ref blockchain_root

let fpts_to #t ([@@@mkey] r: ref t) (x: t) = exists* p. pts_to r #p x

ghost fn dup_fpts_to u#t (t: Type u#t) r x () : duplicable_f (fpts_to #t r x) = {
  unfold fpts_to r x;
  share r;
  fold fpts_to r x;
  fold fpts_to r x;
}
instance duplicable_fpts_to t r x : duplicable (fpts_to #t r x) = { dup_f = dup_fpts_to t r x }

type unat: Type0 =
  | Zero : unat
  | Succ : unat -> unat

let rec root_idx ([@@@mkey] x: ref blockchain_root) ([@@@mkey] i: unat) (y: ref blockchain_root) :
    Tot slprop (decreases i) =
  match i with
  | Zero -> pure (x == y)
  | Succ i -> exists* z. fpts_to x z ** root_idx z.rt_next i y

ghost fn rec dup_root_idx (x: ref blockchain_root) (i: unat) (y: ref blockchain_root) ()
  norewrite
  preserves root_idx x i y
  ensures root_idx x i y
  decreases i
{
  match i {
    Zero -> {
      assert rewrites_to i Zero;
      unfold root_idx x Zero y;
      fold root_idx x Zero y;
      fold root_idx x Zero y;
    }
    Succ j -> {
      assert rewrites_to i (Succ j);
      unfold root_idx x (Succ j) y; with z. _;
      dup (fpts_to x z) ();
      dup_root_idx z.rt_next j y ();
      fold root_idx x (Succ j) y;
      fold root_idx x (Succ j) y;
    }
  }
}
instance duplicable_root_idx x i y : duplicable (root_idx x i y) = { dup_f = dup_root_idx x i y }

let root_idx' ([@@@mkey] x: ref blockchain_root) ([@@@mkey] i: unat) (y: blockchain_root) =
  exists* z. root_idx x i z ** fpts_to z y

ghost fn elim_root_idx'_zero x y
  requires root_idx' x Zero y
  ensures fpts_to x y
{
  unfold root_idx' x Zero y;
  with z. assert root_idx x Zero z;
  unfold root_idx x Zero z;
  assert rewrites_to x z;
}

ghost fn elim_root_idx'_succ x (n: unat) y
  requires root_idx' x (Succ n) y
  ensures exists* z. fpts_to x z ** root_idx' z.rt_next n y
{
  unfold root_idx' x (Succ n) y;
  unfold root_idx x (Succ n); with z. _;
  fold root_idx' z.rt_next n y;
}

ghost fn dup_root_idx' x i y () : duplicable_f (root_idx' x i y) = {
  unfold root_idx' x i y; with z. _;
  dup (root_idx x i z) ();
  dup (fpts_to z y) ();
  fold root_idx' x i y;
  fold root_idx' x i y;
}
instance duplicable_root_idx' x i y : duplicable (root_idx' x i y) = { dup_f = dup_root_idx' x i y }

let valid_split (x a b: slprop_ref) =
  exists* px pa pb.
  slprop_ref_pts_to x px **
  slprop_ref_pts_to a pa **
  slprop_ref_pts_to b pb **
  shift (later px) (later pa ** later pb ** trade (later pa ** later pb) (later px))

ghost fn dup_valid_split x a b () : duplicable_f (valid_split x a b) = {
  unfold valid_split x a b; with px pa pb. _;
  dup (
    slprop_ref_pts_to x px **
    slprop_ref_pts_to a pa **
    slprop_ref_pts_to b pb **
    shift (later px) (later pa ** later pb ** trade (later pa ** later pb) (later px))
  ) ();
  fold valid_split x a b;
  fold valid_split x a b;
}
instance duplicable_valid_split x a b : duplicable (valid_split x a b) = { dup_f = dup_valid_split x a b }

let rec bc_idx ([@@@mkey] x: blockchain_edge) ([@@@mkey] is: list bool) (y: blockchain_edge) :
    Tot slprop (decreases is) =
  match is with
  | i::is ->
    exists* a b.
      valid_split x.be_prop a.be_prop b.be_prop **
      fpts_to x.be_ref (Split a b) **
      bc_idx (if i then b else a) is y
  | [] -> pure (x == y)

ghost fn rec dup_bc_idx x (is: list bool) y ()
  norewrite
  preserves bc_idx x is y
  ensures bc_idx x is y
  decreases is
{
  match is {
    [] -> {
      assert rewrites_to is [];
      unfold bc_idx x [] y;
      fold bc_idx x [] y;
      fold bc_idx x [] y;
    }
    i::is' -> {
      assert rewrites_to is (i::is');
      unfold bc_idx x (i::is') y; with a b. _;
      dup_bc_idx (if i then b else a) is' y ();
      dup (fpts_to x.be_ref (Split a b)) ();
      dup (valid_split x.be_prop a.be_prop b.be_prop) ();
      fold bc_idx x (i::is') y;
      fold bc_idx x (i::is') y;
    }
  }
}
instance duplicable_bc_idx x is y : duplicable (bc_idx x is y) = { dup_f = dup_bc_idx x is y }

let unless c p = if c then emp else p

let rec rt_borrowed ([@@@mkey] x: ref blockchain_root) ([@@@mkey] n: unat) (b: slprop) : Tot slprop (decreases n) =
  match n with
  | Zero -> emp
  | Succ n -> exists* r y c (b': slprop). fpts_to x r **
    slprop_ref_pts_to r.rt_tree.be_prop y **
    pts_to r.rt_returned #0.5R c **
    trade b (unless c (later y) ** b') **
    rt_borrowed r.rt_next n b'

type stored_shape =
  | StoredCheckedOut
  | Stored
  | StoredBoth : stored_shape -> stored_shape -> stored_shape

let rec bc_stored ([@@@mkey] x: blockchain_edge) (d: stored_shape) (y: slprop) : Tot slprop (decreases d) =
  match d with
  | Stored -> exists* z. slprop_ref_pts_to x.be_prop z ** later z ** trade (later z) y
  | StoredCheckedOut -> live x.be_ref ** y
  | StoredBoth da db -> exists* (ya yb: slprop) (a b: blockchain_edge).
    fpts_to x.be_ref (Split a b) **
    bc_stored a da ya **
    bc_stored b db yb **
    trade (ya ** yb) y

let rec rt_stored ([@@@mkey] x: ref blockchain_root) (n: unat) (b: slprop) : Tot slprop (decreases n) =
  match n with
  | Zero -> trade emp b
  | Succ n -> exists* r (b1 b2: slprop). fpts_to x r **
    (exists* d. bc_stored r.rt_tree d b1) **
    rt_stored r.rt_next n b2 **
    trade (b1 ** b2) b

let owns_end ([@@@mkey] x: ref blockchain_root) (n: unat) =
  exists* y. root_idx x n y ** live y

ghost fn elim_owns_end_zero x
  requires owns_end x Zero
  ensures live x
{
  unfold owns_end x Zero; with y. _;
  unfold root_idx x Zero y;
  rewrite each y as x;
}

let lifetime_alive a =
  exists* y n.
    rt_borrowed a n y **
    rt_stored a n y **
    owns_end a n
  
let rec star_later_slprops (ps: list slprop) : slprop =
  match ps with
  | [] -> emp
  | p::ps -> later p ** star_later_slprops ps

let lifetime_opened a ps =
  exists* y n.
    rt_borrowed a n y **
    rt_stored a n (trade (star_later_slprops ps) y) **
    owns_end a n

let lifetime_dead a =
  exists* y n. rt_borrowed a n y ** y ** owns_end a n

ghost fn alloc_dummy_root ()
  returns r: ref blockchain_root
  ensures exists* y. pts_to r y
{
  alloc { rt_tree = dummy_edge; rt_returned = null; rt_next = null }
}

ghost fn begin_lifetime ()
  returns a: lifetime
  ensures a
{
  let a = alloc_dummy_root ();
  fold rt_borrowed a Zero emp;
  intro (trade emp emp) fn _ {};
  fold rt_stored a Zero emp;
  fold root_idx a Zero a;
  fold owns_end a Zero;
  fold lifetime_alive a;
  a
}

ghost fn rec bc_stored_elim x (d: stored_shape) y
  requires bc_stored x d y
  ensures y
  decreases d
{
  match d {
    Stored -> {
      unfold bc_stored x Stored y; with z. _;
      drop_ (slprop_ref_pts_to x.be_prop z);
      elim_trade (later z) y;
    }
    StoredCheckedOut -> {
      unfold bc_stored x StoredCheckedOut y;
      drop_ (live x.be_ref);
    }
    StoredBoth da db -> {
      unfold bc_stored x (StoredBoth da db) y; with ya yb a b. _;
      bc_stored_elim a da ya;
      bc_stored_elim b db yb;
      drop_ (fpts_to x.be_ref (Split a b));
      elim_trade _ _;
    }
  }
}

ghost fn rec rt_stored_elim a (n: unat) y
  requires rt_stored a n y
  ensures y
  decreases n
{
  match n {
    Zero -> {
      unfold rt_stored a Zero y;
      elim_trade emp y;
    }
    Succ m -> {
      unfold rt_stored a (Succ m) y; with r b1 b2. _;
      rt_stored_elim r.rt_next m b2;
      bc_stored_elim r.rt_tree _ b1;
      drop_ (fpts_to a r);
      elim_trade _ _;
    }
  }
}

ghost fn end_lifetime (a: lifetime)
  requires a
  ensures lifetime_dead a
{
  unfold lifetime_alive a; with y n. _;
  rt_stored_elim a n y;
  fold lifetime_dead a;
}

let (>:>) a p =
  exists* n is r l.
    root_idx' a n r **
    bc_idx r.rt_tree is l **
    slprop_ref_pts_to l.be_prop p **
    live l.be_ref

let borrowed a p =
  exists* j r.
    root_idx' a j r **
    slprop_ref_pts_to r.rt_tree.be_prop p **
    pts_to r.rt_returned #0.5R false

ghost fn shift_root_idx a #b n y
  requires fpts_to a b
  requires root_idx b.rt_next n y
  ensures root_idx a (Succ n) y
{
  fold root_idx a (Succ n) y;
}

ghost fn shift_root_idx' a #b n y
  requires fpts_to a b
  requires root_idx' b.rt_next n y
  ensures root_idx' a (Succ n) y
{
  unfold root_idx' b.rt_next n y;
  shift_root_idx a n _;
  fold root_idx' a (Succ n) y;
}

ghost fn shift_owns_end a #b n
  requires fpts_to a b
  requires owns_end b.rt_next n
  ensures owns_end a (Succ n)
{
  unfold owns_end b.rt_next n;
  shift_root_idx a n _;
  fold owns_end a (Succ n);
}

ghost fn rec set_end (a: lifetime) (n: unat) (y: blockchain_root)
  requires owns_end a n
  requires live y.rt_next
  ensures root_idx' a n y
  ensures owns_end a (Succ n)
  decreases n
{
  match n {
    Zero -> {
      assert rewrites_to n Zero;
      unfold owns_end a Zero; with a'. _;
      unfold root_idx a Zero; rewrite each a' as a;
      a := y;
      fold fpts_to a y;
      dup (fpts_to a y) ();
      fold root_idx a Zero a;
      fold root_idx' a Zero y;
      fold root_idx y.rt_next Zero y.rt_next;
      fold root_idx a (Succ Zero) y.rt_next;
      fold owns_end a (Succ Zero);
    }
    Succ m -> {
      assert rewrites_to n (Succ m);
      unfold owns_end a (Succ m); with b. _;
      assert root_idx a (Succ m) b ** live b;
      unfold root_idx a (Succ m) b; with c. _;
      assert fpts_to a c ** root_idx c.rt_next m b;
      fold owns_end c.rt_next m;
      set_end c.rt_next m y;
      dup (fpts_to a c) ();
      shift_owns_end a (Succ m);
      shift_root_idx' a m _;
    }
  }
}

ghost fn fpts_to_gather u#t (#t: Type u#t) (x: ref t) y y'
  preserves fpts_to x y
  requires fpts_to x y'
  ensures pure (y == y')
{
  unfold fpts_to x y;
  unfold fpts_to x y';
  gather x #y #y';
  fold fpts_to x y;
}

ghost fn rec push_rt_borrowed x (n: unat) (b: slprop) r #c #w
  requires rt_borrowed x n b
  requires pts_to r.rt_returned #0.5R c
  requires slprop_ref_pts_to r.rt_tree.be_prop w
  requires root_idx' x n r
  ensures rt_borrowed x (Succ n) (unless c (later w) ** b)
  decreases n
{
  match n {
    Zero -> {
      assert rewrites_to n Zero;
      elim_root_idx'_zero x r;
      unfold rt_borrowed x Zero b;
      intro (trade (unless c (later w) ** b) (unless c (later w) ** b)) fn _ {};
      fold rt_borrowed r.rt_next Zero b;
      fold rt_borrowed x (Succ Zero) (unless c (later w) ** b);
    }
    Succ m -> {
      assert rewrites_to n (Succ m);
      unfold rt_borrowed x (Succ m) b; with z y c' b'. _;
      assert fpts_to x z ** trade b (unless c' (later y) ** b') ** rt_borrowed z.rt_next m b';
      elim_root_idx'_succ x m r; with z'. assert fpts_to x z ** fpts_to x z';
      fpts_to_gather x z z'; rewrite each z' as z;
      assert root_idx' z.rt_next m r;
      push_rt_borrowed z.rt_next m b' r;
      assert trade b (unless c' (later y) ** b');
      intro (trade (unless c (later w) ** b) (unless c' (later y) ** unless c (later w) ** b'))
          #(trade b (unless c' (later y) ** b')) fn _ { elim_trade _ _ };
      fold rt_borrowed x (Succ n) (unless c (later w) ** b);
    }
  }
}

ghost fn rec push_rt_stored x (n: unat) (b: slprop) r (#w: slprop)
  requires rt_stored x n b
  requires slprop_ref_pts_to r.rt_tree.be_prop w
  requires root_idx' x n r
  requires later w
  ensures rt_stored x (Succ n) (later w ** b)
  decreases n
{
  match n {
    Zero -> {
      assert rewrites_to n Zero;
      elim_root_idx'_zero x r;
      unfold rt_stored x Zero b;
      fold rt_stored r.rt_next Zero b;
      intro (trade (later w) (later w)) fn _ {};
      fold bc_stored r.rt_tree Stored (later w);
      intro (trade (later w**b) (later w**b)) fn _ {};
      fold rt_stored x (Succ Zero) (later w ** b);
    }
    Succ m -> {
      assert rewrites_to n (Succ m);
      elim_root_idx'_succ x m r; with z'. _;
      unfold rt_stored x (Succ m) b; with z b1 b2. _;
      fpts_to_gather x z z'; rewrite each z' as z;
      push_rt_stored z.rt_next m _ r;
      intro (trade (b1 ** later w ** b2) (later w ** b)) #(trade (b1 ** b2) b) fn _ { elim_trade _ _ };
      fold rt_stored x (Succ n) (later w ** b);
    }
  }
}

ghost fn push_new_root (a: lifetime) (q: slprop) (c: bool) (#n: unat) (#y #z: slprop)
  requires owns_end a n
  requires rt_borrowed a n y
  requires rt_stored a n z
  requires later q
  ensures a >:> q
  ensures rt_borrowed a (Succ n) (unless c (later q) ** y)
  ensures rt_stored a (Succ n) (later q ** z)
  ensures owns_end a (Succ n)
  ensures exists* e. root_idx' a n e **
    slprop_ref_pts_to e.rt_tree.be_prop q **
    pts_to e.rt_returned #0.5R c
{
  let be_prop = slprop_ref_alloc q;
  let rt_returned = alloc c;
  share rt_returned;
  let rt_next = alloc_dummy_root ();
  let be_ref = alloc dummy_node;
  let e = { rt_tree = { be_prop; be_ref }; rt_returned; rt_next };
  assert rewrites_to be_prop e.rt_tree.be_prop;
  assert rewrites_to be_ref e.rt_tree.be_ref;
  assert rewrites_to rt_returned e.rt_returned;
  assert rewrites_to rt_next e.rt_next;
  dup (slprop_ref_pts_to be_prop q) ();
  set_end a n e;
  dup (root_idx' a n e) ();
  dup (slprop_ref_pts_to be_prop q) ();
  push_rt_borrowed a n y e;
  dup (root_idx' a n e) ();
  dup (slprop_ref_pts_to be_prop q) ();
  push_rt_stored a n _ e;
  dup (root_idx' a n e) ();
  fold bc_idx e.rt_tree [] e.rt_tree;
  fold (a >:> q);
}

ghost fn borrow' (a: lifetime) (p: slprop)
  preserves a
  requires later p
  ensures a >:> p
  ensures borrowed a p
{
  unfold lifetime_alive a; with y n. _;
  push_new_root a p false;
  fold borrowed a p;
  fold lifetime_alive a;
}

ghost fn borrow (a: lifetime) (p: slprop)
  preserves a
  requires p
  ensures a >:> p
  ensures borrowed a p
{
  later_intro p;
  borrow' a p;
}

open FStar.List.Tot { (@) }

ghost fn rec push_bc_idx x (is: list bool) j y #z #w
  requires bc_idx x is y
  requires fpts_to y.be_ref (Split z w)
  requires valid_split y.be_prop z.be_prop w.be_prop
  ensures bc_idx x (is@[j]) (if j then w else z)
  decreases is
{
  match is {
    [] -> {
      unfold bc_idx x [] y; rewrite each y as x;
      fold bc_idx (if j then w else z) [] (if j then w else z);
      fold bc_idx x [j] (if j then w else z);
      rewrite each [j] as (is@[j]);
    }
    i::is' -> {
      assert rewrites_to is (i::is');
      unfold bc_idx x (i::is') y; with a b. _;
      push_bc_idx (if i then b else a) is' j y;
      fold bc_idx x (i::(is'@[j])) (if j then w else z);
      rewrite each (i::(is'@[j])) as (is@[j]);
    }
  }
}

ghost fn share_borrow' #a (p q1 q2: slprop)
  requires a >:> p
  requires shift (later p) (later q1 ** later q2 ** trade (later q1 ** later q2) (later p))
  ensures a >:> q1
  ensures a >:> q2
{
  unfold (a >:> p); with n is r l. _;
  let na = alloc dummy_node;
  let nb = alloc dummy_node;
  let ra = slprop_ref_alloc q1;
  let rb = slprop_ref_alloc q2;
  let ea = { be_prop = ra; be_ref = na };
  rewrite each na as ea.be_ref;
  rewrite each ra as ea.be_prop;
  let eb = { be_prop = rb; be_ref = nb };
  rewrite each nb as eb.be_ref;
  rewrite each rb as eb.be_prop;
  l.be_ref := Split ea eb;
  fold (fpts_to l.be_ref (Split ea eb));
  dup (fpts_to l.be_ref (Split ea eb)) ();
  dup (slprop_ref_pts_to ea.be_prop q1) ();
  dup (slprop_ref_pts_to eb.be_prop q2) ();
  fold valid_split l.be_prop ea.be_prop eb.be_prop;
  dup (bc_idx r.rt_tree is l) ();
  dup (valid_split l.be_prop ea.be_prop eb.be_prop) ();
  push_bc_idx r.rt_tree is false l; 
  push_bc_idx r.rt_tree is true l; 
  dup (root_idx' a n r) ();
  fold (a >:> q1);
  fold (a >:> q2);
}

ghost fn share_borrow #a (p q1 q2: timeless_slprop)
  requires a >:> p
  requires shift p (q1 ** q2 ** trade (q1 ** q2) p)
  ensures a >:> q1
  ensures a >:> q2
{
  intro (shift (later p) (later q1 ** later q2 ** trade (later q1 ** later q2) (later p)))
      #(shift p (q1 ** q2 ** trade (q1 ** q2) p)) fn _ {
    later_elim_timeless p;
    elim_shift _ _;
    later_intro q1;
    later_intro q2;
    intro (trade (later q1 ** later q2) (later p)) #(trade (q1 ** q2) p) fn _ {
      later_elim_timeless q1;
      later_elim_timeless q2;
      elim_trade _ _;
      later_intro p;
    }
  };
  share_borrow' p q1 q2
}

ghost fn rt_stored_mono a n y z
  requires rt_stored a n y
  requires trade y z
  ensures rt_stored a n z
{
  match n {
    Zero -> {
      assert rewrites_to n Zero;
      unfold rt_stored a Zero y;
      intro (trade emp z) #(trade y z ** trade emp y) fn _ { elim_trade emp y; elim_trade y z };
      fold rt_stored a Zero z;
    }
    Succ m -> {
      assert rewrites_to n (Succ m);
      unfold rt_stored a (Succ m) y; with r b1 b2. _;
      intro (trade (b1 ** b2) z) #(trade y z ** trade (b1 ** b2) y) fn _ {
        elim_trade (b1 ** b2) y;
        elim_trade y z;
      };
      fold rt_stored a (Succ m) z;
    }
  }
}

ghost fn weaken_opened' #a (p q: slprop) #qs
  requires lifetime_opened a (p::qs)
  requires trade (later q) (later p)
  ensures lifetime_opened a (q::qs)
{
  unfold lifetime_opened a (p::qs); with y n. _;
  intro (trade (trade (star_later_slprops (p :: qs)) y)
      (trade (star_later_slprops (q :: qs)) y)) #(trade (later q) (later p)) fn _ {
    unfold star_later_slprops (q :: qs);
    elim_trade (later q) (later p);
    fold star_later_slprops (p :: qs);
    elim_trade _ _;
  };
  rt_stored_mono a n (trade (star_later_slprops (p::qs)) y) (trade (star_later_slprops (q::qs)) y);
  fold lifetime_opened a (q::qs);
}

ghost fn weaken_opened #a (p q: timeless_slprop) #qs
  requires lifetime_opened a (Cons #slprop p qs)
  requires trade q p
  ensures lifetime_opened a (Cons #slprop q qs)
{
  intro (trade (later q) (later p)) #(trade q p) fn _ {
    later_elim_timeless q;
    elim_trade q p;
    later_intro p;
  };
  weaken_opened' p q;
}

ghost fn open_lifetime (a: lifetime)
  requires a
  ensures lifetime_opened a []
{
  unfold lifetime_alive a; with y n. _;
  intro (trade y (trade (star_later_slprops []) y)) fn _ { unfold star_later_slprops [] };
  rt_stored_mono a n y (trade (star_later_slprops []) y);
  fold lifetime_opened a [];
}

ghost fn close_lifetime (a: lifetime)
  requires lifetime_opened a []
  ensures a
{
  unfold lifetime_opened a []; with y n. _;
  intro (trade (trade (star_later_slprops []) y) y) fn _ {
    fold star_later_slprops [];
    elim_trade (star_later_slprops []) y
  };
  rt_stored_mono a n (trade (star_later_slprops []) y) y;
  fold lifetime_alive a;
}

ghost fn fpts_to_of_root_idx' x j r
  requires root_idx' x j r
  ensures exists* y. fpts_to x y
{
  match j {
    Zero -> {
      elim_root_idx'_zero x r;
    }
    Succ j -> {
      elim_root_idx'_succ x j r;
      drop_ (root_idx' _ _ r);
    }
  }
}

[@@allow_ambiguous]
ghost fn too_much_perm u#t (#t: Type u#t) (x: ref t) #y1 #y2 #p1 #p2
  requires pts_to x #p1 y1
  requires pts_to x #p2 y2
  requires pure (p1 +. p2 >. 1.0R)
  ensures pure False
{
  gather x;
  pts_to_perm_bound x;
  drop_ (pts_to x _)
}

ghost fn later_equiv_commute p q
  requires later (equiv p q)
  ensures equiv (later p) (later q)
{
  later_equiv p q;
  rewrite later (equiv p q) as equiv (later p) (later q)
}

ghost fn rec bc_stored_take x (d: stored_shape) y (is: list bool) p #l
  requires bc_stored x d y
  requires bc_idx x is l
  requires slprop_ref_pts_to l.be_prop p
  requires live l.be_ref
  ensures exists* d'. bc_stored x d' (trade (later p) y)
  ensures later p
  decreases is
{
  match d {
    Stored -> {
      unfold bc_stored x Stored y; with z. _;
      match is {
        [] -> {
          unfold bc_idx x [] l;
          rewrite each l as x;
          slprop_ref_gather x.be_prop #z #p;
          later_equiv_commute z p;
          equiv_dup (later z) (later p);
          equiv_elim (later z) (later p);
          intro (trade (later p) y) #(equiv (later z) (later p) ** trade (later z) y) fn _ {
            equiv_comm _ _;
            equiv_elim _ _;
            elim_trade _ _;
          };
          drop_ (slprop_ref_pts_to x.be_prop z);
          fold bc_stored x StoredCheckedOut (trade (later p) y);
        }
        i::is' -> {
          unfold bc_idx x (i::is') l; with a b. _;
          unfold valid_split; with px pa pb. _;
          slprop_ref_gather x.be_prop #z #px;
          drop_ (slprop_ref_pts_to x.be_prop z);
          later_equiv_commute z px;
          equiv_dup _ _;
          equiv_elim _ _;
          elim_shift _ _;
          intro (trade (later pa ** later pb) y) #(equiv (later z) (later px) **
              trade (later z) y ** trade (later pa ** later pb) (later px)) fn _ {
            elim_trade (later pa ** later pb) (later px);
            equiv_comm _ _; equiv_elim _ _;
            elim_trade (later z) y
          };
          intro (trade (later pa) (later pa)) fn _ {};
          fold bc_stored a Stored (later pa);
          intro (trade (later pb) (later pb)) fn _ {};
          fold bc_stored b Stored (later pb);
          match i {
            false -> {
              bc_stored_take a Stored (later pa) is' p; with da'. _;
              intro (trade (trade (later p) (later pa) ** later pb) (trade (later p) y))
                  #(trade (later pa ** later pb) y) fn _ {
                elim_trade (later p) (later pa);
                elim_trade _ _;
              };
              fold bc_stored x (StoredBoth da' Stored) (trade (later p) y);
            }
            true -> {
              bc_stored_take b Stored (later pb) is' p; with db'. _;
              intro (trade (later pa ** trade (later p) (later pb)) (trade (later p) y))
                  #(trade (later pa ** later pb) y) fn _ {
                elim_trade (later p) (later pb);
                elim_trade _ _;
              };
              fold bc_stored x (StoredBoth Stored db') (trade (later p) y);
            }
          }
        }
      }
    }
    StoredCheckedOut -> {
      unfold bc_stored x StoredCheckedOut y;
      match is {
        [] -> {
          unfold bc_idx x [] l;
          rewrite each l as x;
          too_much_perm x.be_ref;
          unreachable ();
        }
        i::is -> {
          unfold bc_idx x (i::is) l;
          unfold fpts_to x.be_ref;
          too_much_perm x.be_ref;
          unreachable ();
        }
      }
    }
    StoredBoth da db -> {
      assert rewrites_to d (StoredBoth da db);
      unfold bc_stored x (StoredBoth da db) y; with ya yb a b. _;
      match is {
        [] -> {
          unfold bc_idx x [] l;
          rewrite each l as x;
          unfold fpts_to x.be_ref;
          too_much_perm x.be_ref;
          unreachable ();
        }
        i::is' -> {
          unfold bc_idx x (i::is') l; with a' b'. _;
          drop_ (valid_split _ _ _);
          fpts_to_gather x.be_ref (Split a b) (Split a' b');
          rewrite each a' as a; rewrite each b' as b;
          match i {
            false -> {
              bc_stored_take a da ya is' p; with da'. _;
              intro (trade (trade (later p) ya ** yb) (trade (later p) y)) #(trade (ya ** yb) y) fn _ {
                elim_trade (later p) ya;
                elim_trade (ya ** yb) y;
              };
              fold bc_stored x (StoredBoth da' db) (trade (later p) y);
            }
            true -> {
              bc_stored_take b db yb is' p; with db'. _;
              intro (trade (ya ** trade (later p) yb) (trade (later p) y)) #(trade (ya ** yb) y) fn _ {
                elim_trade (later p) yb;
                elim_trade (ya ** yb) y;
              };
              fold bc_stored x (StoredBoth da db') (trade (later p) y);
            }
          }
        }
      }
    }
  }
}

ghost fn elim_owns_end_succ x #r m
  requires owns_end x (Succ m)
  preserves fpts_to x r
  ensures owns_end r.rt_next m
{
  unfold owns_end x (Succ m); with y. _;
  unfold root_idx x (Succ m) y; with r'. _;
  fpts_to_gather x r r'; rewrite each r' as r;
  fold owns_end r.rt_next m;
}

ghost fn intro_owns_end_succ x #r m
  requires owns_end r.rt_next m
  preserves fpts_to x r
  ensures owns_end x (Succ m)
{
  unfold owns_end r.rt_next m;
  dup (fpts_to x r) ();
  fold root_idx x (Succ m);
  fold owns_end x (Succ m);
}

ghost fn rec rt_stored_take x (n: unat) b j is #r p #l
  preserves owns_end x n
  requires rt_stored x n b
  requires root_idx' x j r
  requires bc_idx r.rt_tree is l
  requires slprop_ref_pts_to l.be_prop p
  requires live l.be_ref
  ensures rt_stored x n (trade (later p) b)
  ensures later p
  decreases n
{
  match n {
    Zero -> {
      elim_owns_end_zero x;
      fpts_to_of_root_idx' x j r;
      unfold fpts_to x;
      too_much_perm x;
      unreachable ()
    }
    Succ m -> {
      assert rewrites_to n (Succ m);
      unfold rt_stored x (Succ m) b; with y b1 b2. _;
      match j {
        Zero -> {
          elim_root_idx'_zero x r;
          fpts_to_gather x r y; rewrite each y as r;
          bc_stored_take r.rt_tree _ b1 is p;
          intro (trade (trade (later p) b1 ** b2) (trade (later p) b)) #(trade (b1 ** b2) b) fn _ {
            elim_trade (later p) b1;
            elim_trade (b1 ** b2) b;
          };
          fold rt_stored x (Succ m) (trade (later p) b);
        }
        Succ j -> {
          elim_root_idx'_succ x j r; with z. _;
          fpts_to_gather x y z; rewrite each z as y;
          dup (fpts_to x y) ();
          elim_owns_end_succ x m;
          rt_stored_take y.rt_next m b2 j is p;
          intro (trade (b1 ** trade (later p) b2) (trade (later p) b))
              #(trade (b1 ** b2) b) fn _ {
            elim_trade (later p) b2;
            elim_trade (b1 ** b2) b;
          };
          fold rt_stored x (Succ m) (trade (later p) b);
          intro_owns_end_succ x m;
          drop_ (fpts_to x y);
        }
      }
    }
  }
}

ghost fn push_new_root_internal (a: lifetime) (q: slprop) (#n: unat) (#y #z: slprop)
  requires owns_end a n
  requires rt_borrowed a n y
  requires rt_stored a n z
  requires later q
  ensures a >:> q
  ensures rt_borrowed a (Succ n) (emp ** y)
  ensures rt_stored a (Succ n) (later q ** z)
  ensures owns_end a (Succ n)
{
  push_new_root a q true; with e. _;
  drop_ (
    root_idx' a n e **
    slprop_ref_pts_to e.rt_tree.be_prop q **
    pts_to e.rt_returned #0.5R true
  )
}

ghost fn use_borrow' (a: lifetime) (p: slprop) (#qs: list slprop)
  requires lifetime_opened a qs
  requires a >:> p
  ensures lifetime_opened a (p::qs)
  ensures later p
{
  unfold lifetime_opened a qs; with y n. _;
  unfold (a >:> p); with j is r l. _;
  rt_stored_take a n _ j is p;
  intro (trade (trade (later p) (trade (star_later_slprops qs) y))
      (trade (star_later_slprops (p :: qs)) y)) fn _ {
    rewrite star_later_slprops (p :: qs) as later p ** star_later_slprops qs;
    elim_trade _ _;
    elim_trade _ _;
  };
  rt_stored_mono a n _ _;
  fold lifetime_opened a (p::qs)
}

ghost fn end_use_borrow' (a: lifetime) (p: slprop) (#qs: list slprop)
  requires lifetime_opened a (p::qs)
  requires later p
  ensures lifetime_opened a qs
  ensures a >:> p
{
  unfold lifetime_opened a (p::qs); with y n. _;
  push_new_root_internal a p;
  intro (trade (later p ** trade (star_later_slprops (p :: qs)) y) (trade (star_later_slprops qs) (emp ** y))) fn _ {
    rewrite later p ** star_later_slprops qs as star_later_slprops (p :: qs);
    elim_trade _ _;
  };
  rt_stored_mono a (Succ n) _ _;
  fold lifetime_opened a qs;
}

ghost fn sub_borrow' (#a: lifetime) (p q: slprop)
  requires trade (later p) (later q ** trade (later q) (later p))
  preserves a
  requires a >:> p
  ensures a >:> q
{
  open_lifetime a;
  use_borrow' a p;
  elim_trade (later p) (later q ** trade (later q) (later p));
  weaken_opened' p q;
  end_use_borrow' a q;
  close_lifetime a;
}

ghost fn sub_borrow (#a: lifetime) (p q: timeless_slprop)
  requires trade p (q ** trade q p)
  preserves a
  requires a >:> p
  ensures a >:> q
{
  intro (trade (later p) (later q ** trade (later q) (later p)))
      #(trade p (q ** trade q p)) fn _ {
    later_elim_timeless p;
    elim_trade p (q ** trade q p);
    later_intro q;
    intro (trade (later q) (later p)) #(trade q p) fn _ {
      later_elim_timeless q;
      elim_trade q p;
      later_intro p;
    };
  };
  sub_borrow' p q;
}

ghost fn use_borrow (a: lifetime) (p: timeless_slprop) (#q: list slprop)
  requires lifetime_opened a q
  requires a >:> p
  ensures lifetime_opened a (Cons #slprop p q)
  ensures p
{
  use_borrow' a p;
  later_elim_timeless p;
}

ghost fn end_use_borrow (a: lifetime) (p: slprop) (#qs: list slprop)
  requires lifetime_opened a (p::qs)
  requires p
  ensures lifetime_opened a qs
  ensures a >:> p
{
  later_intro p;
  end_use_borrow' a p;
}

ghost fn rec rt_borrowed_take x (n: unat) j #r #p
  preserves owns_end x n
  preserves exists* b. rt_borrowed x n b ** b

  requires root_idx' x j r
  requires slprop_ref_pts_to r.rt_tree.be_prop p
  requires pts_to r.rt_returned #0.5R false

  ensures later p

  decreases n
{
  with b. assert rt_borrowed x n b;
  match n {
    Zero -> {
      elim_owns_end_zero x;
      fpts_to_of_root_idx' x j r;
      unfold fpts_to x;
      too_much_perm x;
      unreachable ()
    }
    Succ m -> {
      assert rewrites_to n (Succ m);
      unfold rt_borrowed x (Succ m) b; with r' y c b'. _;
      elim_trade b _;
      match j {
        Zero -> {
          elim_root_idx'_zero x r;
          fpts_to_gather x r r'; rewrite each r' as r;
          gather r.rt_returned;
          r.rt_returned := true;
          share r.rt_returned; drop_ (pts_to r.rt_returned #0.5R true);
          rewrite unless c (later y) as later y;
          slprop_ref_gather r.rt_tree.be_prop #y #p;
          later_equiv_commute y p; equiv_elim (later y) (later p);
          intro (trade b' (unless true (later y) ** b')) fn _ { rewrite emp as unless true (later y) };
          fold rt_borrowed x n b';
        }
        Succ j -> {
          elim_root_idx'_succ x j r; with z. _;
          fpts_to_gather x r' z; rewrite each z as r';
          elim_owns_end_succ x m;
          rt_borrowed_take r'.rt_next m j; with b''. _;
          intro (trade (unless c (later y) ** b'') (unless c (later y) ** b'')) fn _ {};
          dup (fpts_to x r') ();
          fold rt_borrowed x n (unless c (later y) ** b'');
          shift_owns_end x m;
        }
      }
    }
  }
}

ghost fn end_borrow' (a: lifetime) p
  preserves lifetime_dead a
  requires borrowed a p
  ensures later p
{
  unfold lifetime_dead a; with y n. _;
  unfold borrowed a p; with j r. _;
  rt_borrowed_take a n j;
  fold lifetime_dead a;
}

ghost fn end_borrow (a: lifetime) (p: timeless_slprop)
  preserves lifetime_dead a
  requires borrowed a p
  ensures p
{
  end_borrow' a p;
  later_elim_timeless p;
}
