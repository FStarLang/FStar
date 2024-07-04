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

module ParallelFor

open Pulse.Lib.Pervasives
open Pulse.Lib.Fixpoints
open Pulse.Lib.Task
open FStar.Real
open Pulse.Lib.Pledge
open Pulse.Lib.InvList
open Pulse.Lib.OnRange

module P = Pulse.Lib.Pledge

```pulse
ghost
fn aux_squash_pledge (f v : slprop) (_:unit)
  requires f ** pledge emp_inames f (pledge emp_inames f v)
  ensures  f ** v
{
  P.squash_pledge emp_inames f v;
  P.redeem_pledge emp_inames f v
}
```

```pulse
ghost
fn squash_pledge (f v : slprop)
  requires pledge emp_inames f (pledge emp_inames f v)
  ensures pledge emp_inames f v
{
  Pulse.Lib.Pledge.squash_pledge emp_inames f v
}
```

let div_perm (p:perm) (n:pos) : perm =
  let open PulseCore.FractionalPermission in
  p /. (of_int n)

(* Basic sketch of a parallel for *)

(* First, a sequential one. *)

let rewrite_ = Pulse.Lib.Core.rewrite

// ```pulse
// ghost
// fn p_join (p : (nat->slprop)) (i j k : nat) (_ : squash (i <= j /\ j <= k))
//   requires on_range p i j ** on_range p j k
//   ensures  on_range p i k
// {
//   rewrite_ _ _ (p_join_equiv p i j k ())
// }
// ```

// ```pulse
// fn p_split (p : (nat->slprop)) (i j k : nat) (_ : squash (i <= j /\ j <= k))
//   requires on_range p i k
//   ensures on_range p i j ** on_range p j k
// {
//   rewrite_ _ _ (slprop_equiv_sym _ _ (p_join_equiv p i j k ()))
// }
// ```

// ```pulse
// ghost
// fn p_join_last (p : (nat->slprop)) (n : nat) (_ : squash (n > 0))
//   requires on_range p 0 (n-1) ** p (n-1)
//   ensures on_range p 0 n
// {
//   rewrite_ _ _ (slprop_equiv_sym _ _ (p_join_last_equiv p n))
// }
// ```

// ```pulse
// ghost
// fn p_split_last (p : (nat->slprop)) (n : nat) (_ : squash (n > 0))
//   requires on_range p 0 n
//   ensures on_range p 0 (n-1) ** p (n-1)
// {
//   rewrite_ _ _ (p_join_last_equiv p n)
// }
// ```

// ```pulse
// ghost
// fn p_combine (p1 p2 : (nat->slprop)) (i j : nat)
//   requires on_range p1 i j ** on_range p2 i j
//   ensures on_range (fun i -> p1 i ** p2 i) i j
// {
//   rewrite_ _ _ (p_combine_equiv p1 p2 i j)
// //   rewrite_ _ _ (slprop_equiv_sym _ _ (p_combine_equiv p1 p2 i j))
// }
// ```

// ```pulse
// ghost
// fn p_uncombine (p1 p2 : (nat->slprop)) (i j : nat)
//   requires on_range (fun i -> p1 i ** p2 i) i j
//   ensures on_range p1 i j ** on_range p2 i j
// {
// //   rewrite_ _ _ (p_combine_equiv p1 p2 i j)
//   rewrite_ _ _ (slprop_equiv_sym _ _ (p_combine_equiv p1 p2 i j))
// }
// ```

```pulse
fn rec simple_for
   (pre post : (nat -> slprop))
   (r : slprop) // This resource is passed around through iterations.
   (f : (i:nat -> stt unit (r ** pre i) (fun () -> (r ** post i))))
   (n : nat)
   requires r ** on_range pre 0 n
   ensures r ** on_range post 0 n
{
  (* Couldn't use a while loop here, weird errors, try again. *)
  if (n = 0) {
    on_range_empty_elim pre 0;
    on_range_empty post 0;
  } else {
    // rewrite (on_range pre 0 n) as (on_range pre (reveal (hide 0)) (reveal (hide n)));
    on_range_unsnoc ();
    f (n-1);
    simple_for pre post r f (n-1);
    on_range_snoc ();
    ()
  }
}
```

```pulse
fn for_loop
   (pre post : (nat -> slprop))
   (r : slprop) // This resource is passed around through iterations.
   (f : (i:nat -> stt unit (r ** pre i) (fun () -> (r ** post i))))
   (lo hi : nat)
   requires r ** on_range pre lo hi
   ensures r ** on_range post lo hi
{
  on_range_le pre;
  let pre'  : (nat -> slprop) = (fun (i:nat) -> pre  (i + lo));
  let post' : (nat -> slprop) = (fun (i:nat) -> post (i + lo));
  ghost
  fn shift_back (k : nat{lo <= k /\ k < hi})
    requires pre k
    ensures pre' (k + (-lo))
  {
    rewrite pre k as pre' (k + (-lo));
  };
  assert (on_range pre lo hi);
  on_range_weaken_and_shift
    pre pre'
    (-lo)
    lo hi
    shift_back;
  rewrite (on_range pre' (lo+(-lo)) (hi+(-lo))) as (on_range pre' 0 (hi-lo));
  assert (on_range pre' 0 (hi-lo));

  fn f' (i:nat)
    requires r ** pre' i
    ensures r ** post' i
  {
    rewrite pre' i as pre (i+lo);
    f (i+lo);
    rewrite post (i+lo) as post' i;
  };

  simple_for pre' post' r f' (hi-lo);

  assert (on_range post' 0 (hi-lo));

  ghost
  fn shift_forward (k : nat{k < hi-lo})
    requires post' k
    ensures post (k + lo)
  {
    rewrite post' k as post (k + lo);
  };
  on_range_weaken_and_shift
    post' post
    lo
    0 (hi-lo)
    shift_forward;
  rewrite
    on_range post (0+lo) ((hi-lo)+lo)
  as
    on_range post lo hi;
}
```

assume val frac_n (n:pos) (p:pool) (e:perm)
  : stt unit (pool_alive #e p)
             (fun () -> on_range (fun i -> pool_alive #(div_perm e n) p) 0 n)

assume val unfrac_n (n:pos) (p:pool) (e:perm)
  : stt unit (on_range (fun i -> pool_alive #(div_perm e n) p) 0 n)
             (fun () -> pool_alive #e p)

```pulse
fn spawned_f_i
  (p:pool)
  (pre : (nat -> slprop))
  (post : (nat -> slprop))
  (e:perm)
  (f : (i:nat -> stt unit (pre i) (fun () -> post i)))
  (i:nat)
  requires emp ** (pre i ** pool_alive #e p)
  ensures emp ** (pledge emp_inames (pool_done p) (post i) ** pool_alive #e p)
{
  spawn_ #(pre i) #(post i) p #e (fun () -> f i)
}
```

// In pulse, using fixpoint combinator below. Should be a ghost step eventually
```pulse
fn rec redeem_range
  (p : (nat -> slprop))
  (f : slprop)
  (n : nat)
  requires f ** on_range (fun i -> pledge emp_inames f (p i)) 0 n
  ensures f ** on_range p 0 n
{
  if (n = 0) {
    on_range_empty_elim (fun i -> pledge emp_inames f (p i)) 0;
    on_range_empty p 0;
  } else {
    on_range_unsnoc (); // (fun i -> pledge emp_inames f (p i)) n ();
    rewrite // ????
      (fun i -> pledge emp_inames f (p i)) (n-1)
    as
      pledge emp_inames f (p (n-1));
    redeem_pledge _ f (p (n-1));
    redeem_range p f (n-1);
    on_range_snoc ();
    // p_join_last p n ()
  }
}
```

```pulse
fn
parallel_for
  (pre : (nat -> slprop))
  (post : (nat -> slprop))
  (f : (i:nat -> stt unit (pre i) (fun () -> (post i))))
  (n : pos)
  requires on_range pre 0 n
  ensures on_range post 0 n
{
  let p = setup_pool 42;
  (* Use a normal for loop to *spawn* each task *)

  (* First, share the pool_alive permission among all n tasks. *)
  assert (pool_alive #1.0R p);
  frac_n n p 1.0R;

  on_range_zip
    pre
    (fun i -> pool_alive #(div_perm 1.0R n) p)
    0 n;

  simple_for
    (fun i -> pre i ** pool_alive #(div_perm 1.0R n) p)
    (fun i -> pledge emp_inames (pool_done p) (post i) ** pool_alive #(div_perm 1.0R n) p)
    emp // Alternative: pass pool_alive p here and forget about the n-way split. See below.
    (spawned_f_i p pre post (div_perm 1.0R n) f)
    n;

  on_range_unzip
    (fun i -> pledge emp_inames (pool_done p) (post i))
    (fun i -> pool_alive #(div_perm 1.0R n) p)
    0 n;

  unfrac_n n p 1.0R;
  teardown_pool p;

  redeem_range post (pool_done p) n;

  drop_ (pool_done p);

  ()
}
```


```pulse
fn spawned_f_i_alt
  (p:pool)
  (pre : (nat -> slprop))
  (post : (nat -> slprop))
  (f : (i:nat -> stt unit (pre i) (fun () -> post i)))
  (i:nat)
  requires pool_alive p ** pre i
  ensures pool_alive p ** pledge emp_inames (pool_done p) (post i)
{
  spawn_ #(pre i) #(post i) p #1.0R (fun () -> f i)
}
```

(* Alternative; not splitting the pool_alive resource. We are anyway
spawning sequentially. *)
```pulse
fn
parallel_for_alt
  (pre : (nat -> slprop))
  (post : (nat -> slprop))
  (f : (i:nat -> stt unit (pre i) (fun () -> (post i))))
  (n : pos)
  requires on_range pre 0 n
  ensures on_range post 0 n
{
  let p = setup_pool 42;

  simple_for
    pre
    (fun i -> pledge emp_inames (pool_done p) (post i))
    (pool_alive p)
    (spawned_f_i_alt p pre post f)
    n;

  teardown_pool p;
  redeem_range post (pool_done p) n;
  drop_ (pool_done p);
  ()
}
```

let wsr_loop_inv_f
  (pre : (nat -> slprop))
  (post : (nat -> slprop))
  (full_post : (nat -> slprop))
  (n : pos)
  (i : ref int)
  (b:bool)
  : Tot slprop
  =
  exists* (ii:nat).
       pts_to i ii
    ** full_post ii
    ** on_range post ii n
    ** pure (b == (Prims.op_LessThan ii n))

let wsr_loop_inv_tf
  (pre : (nat -> slprop))
  (post : (nat -> slprop))
  (full_post : (nat -> slprop))
  (n : pos)
  (i : ref int)
  : Tot slprop =
  exists* (b:bool). wsr_loop_inv_f pre post full_post n i b

(* This can be ghost. *)
```pulse
fn rec ffold
  (p : (nat -> slprop))
  (fp : (nat -> slprop))
  (ss : (i:nat -> stt_ghost unit emp_inames (p i ** fp i) (fun () -> fp (i+1))))
  (n : nat)
  (i : nat)
  requires pure (i <= n) ** fp i ** on_range p i n
  ensures fp n
{
   if (i = n) {
     on_range_empty_elim p n;
     rewrite fp i as fp n;
     ()
   } else {
     assert (fp i ** on_range p i n);
     on_range_uncons ();
     ss i;
     ffold p fp ss n (i+1);
     ()
   }
}
```

(* This can be ghost. *)
```pulse
fn rec funfold
  (p : (nat -> slprop))
  (fp : (nat -> slprop))
  (ss : (i:nat -> stt_ghost unit emp_inames (fp (i+1)) (fun () -> p i ** fp i)))
  (n : nat)
  requires fp n
  ensures fp 0 ** on_range p 0 n
{
   if (n = 0) {
     rewrite fp n as fp 0;
     on_range_empty p 0;
     ()
   } else {
     assert (fp n);
     rewrite fp n as fp ((n-1)+1);
     ss (n-1);
     assert (p (n-1) ** fp (n-1));
     funfold p fp ss (n-1);
     on_range_snoc ();
   }
}
```

```pulse
fn
parallel_for_wsr
  (pre : (nat -> slprop))
  (post : (nat -> slprop))
  (full_pre : (nat -> slprop))
  (full_post : (nat -> slprop))
  (f : (i:nat -> stt unit (pre i) (fun () -> post i)))
  (unfold_pre : (i:nat -> stt_ghost unit emp_inames (full_pre (i+1)) (fun () -> pre i ** full_pre i)))
  (fold_post : (i:nat -> stt_ghost unit emp_inames (post i ** full_post i) (fun () -> full_post (i+1))))
  (n : pos)
  requires full_pre n ** full_post 0
  ensures full_pre 0 ** full_post n
{
  funfold pre full_pre unfold_pre n;
  parallel_for pre post f n;
  ffold post full_post fold_post n 0
}
```

assume
val frame_stt_left
  (#a:Type u#a)
  (#pre:slprop) (#post:a -> slprop)
  (frame:slprop)
  (e:stt a pre post)
  : stt a (frame ** pre) (fun x -> frame ** post x)

```pulse
fn rec h_for_task
  (p:pool)
  (e:perm)
  (pre : (nat -> slprop))
  (post : (nat -> slprop))
  (f : (i:nat -> stt unit (pre i) (fun () -> post i)))
  (lo hi : nat)
  (_:unit)
  requires pool_alive #e p ** on_range pre lo hi
  ensures pledge emp_inames (pool_done p) (on_range post lo hi)
{
  if (hi - lo < 100) {
    (* Too small, just run sequentially *)
    drop_ (pool_alive #e p); // won't use the pool
    for_loop pre post emp
             (fun i -> frame_stt_left emp (f i)) lo hi;

    return_pledge (pool_done p) (on_range post lo hi)
  } else {
    let mid = (hi+lo)/2;
    assert (pure (lo <= mid /\ mid <= hi));

    share_alive p e;
    share_alive p (e /. 2.0R);

    on_range_split mid;

    spawn_ #(pool_alive #((e /. 2.0R) /. 2.0R) p ** on_range pre lo mid)
            #(pledge emp_inames (pool_done p) (on_range post lo mid))
            p
            #(e /. 2.0R)
            (h_for_task p ((e /. 2.0R) /. 2.0R) pre post f lo mid);

    spawn_ #(pool_alive #((e /. 2.0R) /. 2.0R) p ** on_range pre mid hi)
            #(pledge emp_inames (pool_done p) (on_range post mid hi))
            p
            #(e /. 2.0R)
            (h_for_task p ((e /. 2.0R) /. 2.0R) pre post f mid hi);

    (* We get this complicated pledge emp_inames from the spawns above. We can
    massage it before even waiting. *)
    assert (pledge emp_inames (pool_done p) (pledge emp_inames (pool_done p) (on_range post lo mid)));
    assert (pledge emp_inames (pool_done p) (pledge emp_inames (pool_done p) (on_range post mid hi)));

    squash_pledge (pool_done p) (on_range post lo mid);
    squash_pledge (pool_done p) (on_range post mid hi);

    join_pledge #emp_inames #(pool_done p) (on_range post lo mid) (on_range post mid hi);
    rewrite_pledge
      #emp_inames
      #(pool_done p)
      (on_range post lo mid ** on_range post mid hi)
      (on_range post lo hi)
      (fun () -> on_range_join lo mid hi);

    (* Better *)
    assert (pledge emp_inames (pool_done p) (on_range post lo hi));

    drop_ (pool_alive #(e /. 2.0R) p);

    ()
  }
}
```

(* Assuming a wait that only needs epsilon permission. We would actually
need one that takes epsilon permission + a pledge emp_inames for (1-e), or something
similar. Otherwise we cannot rule out some other thread holding permission
to the task pool, and we would not be allowed to free it. *)
assume
val wait_pool
  (p:pool)
  (e:perm)
  : stt unit (pool_alive #e p) (fun _ -> pool_done p)

```pulse
fn
parallel_for_hier
  (pre : (nat -> slprop))
  (post : (nat -> slprop))
  (f : (i:nat -> stt unit (pre i) (fun () -> (post i))))
  (n : pos)
  requires on_range pre 0 n
  ensures on_range post 0 n
{
  let p = setup_pool 42;

  if (false) { // Checking that both branches would work
    (* Spawning the first task: useless! Just call it! *)
    assert (pool_alive #1.0R p);
    share_alive p 1.0R;

    rewrite (pool_alive #(1.0R /. 2.0R) p ** pool_alive #(1.0R /. 2.0R) p)
        as (pool_alive #0.5R p ** pool_alive #0.5R p);
    assert (pool_alive #0.5R p ** pool_alive #0.5R p);


    spawn_ #(pool_alive #0.5R p ** on_range pre 0 n)
            #(pledge emp_inames (pool_done p) (on_range post 0 n))
            p
            #0.5R
            (h_for_task p 0.5R pre post f 0 n);

    (* We get this complicated pledge emp_inames from the spawn above. We can
    massage it before even waiting. *)
    assert (pledge emp_inames (pool_done p) (pledge emp_inames (pool_done p) (on_range post 0 n)));

    squash_pledge (pool_done p) (on_range post 0 n);

    assert (pledge emp_inames (pool_done p) (on_range post 0 n));

    wait_pool p 0.5R;

    redeem_pledge emp_inames (pool_done p) (on_range post 0 n);

    drop_ (pool_done p)
  } else {
    (* Directly calling is much easier, and actually better all around. *)
    share_alive p 1.0R;
    h_for_task p (1.0R /. 2.0R) pre post f 0 n ();

    wait_pool p (1.0R /. 2.0R);

    assert (pool_done p);

    redeem_pledge emp_inames (pool_done p) (on_range post 0 n);

    drop_ (pool_done p)
  }
}
```
