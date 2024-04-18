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

module P = Pulse.Lib.Pledge

```pulse
ghost
fn aux_squash_pledge (f v : vprop) (_:unit)
  requires f ** pledge emp_inames f (pledge emp_inames f v)
  ensures  f ** v
{
  P.squash_pledge emp_inames f v;
  P.redeem_pledge emp_inames f v
}
```

```pulse
ghost
fn squash_pledge (f v : vprop)
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

val range : (nat -> vprop) -> i:nat -> j:nat -> vprop
let rec range p i j : Tot vprop (decreases j-i) =
  if i < j
  then p i ** range p (i+1) j
  else emp

(* The precondition on i/j/k is needed otherwise the LHS can be stronger. *)
val p_join_equiv (p : nat -> vprop) (i j k : nat) (_ : squash (i <= j /\ j <= k))
  : Tot (vprop_equiv (range p i j ** range p j k) (range p i k)) (decreases j-i)
let rec p_join_equiv p i j k _ =
  if i = j
  then (
    assert (range p i j == emp);
    vprop_equiv_unit _
  )
  else (
    let eq : vprop_equiv (range p i j ** range p j k) ((p i ** range p (i+1) j) ** range p j k) =
      vprop_equiv_refl _
    in
    let eq : vprop_equiv (range p i j ** range p j k) (p i ** (range p (i+1) j ** range p j k)) =
      vprop_equiv_trans _ _ _ eq
        (vprop_equiv_assoc _ _ _)
    in
    let eq : vprop_equiv (range p i j ** range p j k) (p i ** range p (i+1) k) =
      vprop_equiv_trans _ _ _ eq
        (vprop_equiv_cong _ _ _ _ (vprop_equiv_refl _) (p_join_equiv p (i+1) j k ()))
    in
    eq
  )

val p_join_last_equiv (p : nat -> vprop) (n : pos)
  : Tot (vprop_equiv (range p 0 n) (range p 0 (n-1) ** p (n-1)))

let rec p_join_last_equiv p n =
  if n = 1 then vprop_equiv_comm _ _
  else (
    let eq : vprop_equiv (range p 0 n) (range p 0 (n-1) ** range p (n-1) n) =
      vprop_equiv_sym _ _ (p_join_equiv p 0 (n-1) n ())
    in
    let eq : vprop_equiv (range p 0 n) (range p 0 (n-1) ** (p (n-1) ** emp)) =
      vprop_equiv_trans _ _ _ eq
        (vprop_equiv_refl _)
    in
    let eq : vprop_equiv (range p 0 n) (range p 0 (n-1) ** (emp ** p (n-1))) =
      vprop_equiv_trans _ _ _ eq
        (vprop_equiv_cong _ _ _ _ (vprop_equiv_refl _) (vprop_equiv_comm _ _)) // (vprop_equiv_unit _)))
    in
    let eq : vprop_equiv (range p 0 n) (range p 0 (n-1) ** p (n-1)) =
      vprop_equiv_trans _ _ _ eq
        (vprop_equiv_cong _ _ _ _ (vprop_equiv_refl _) (vprop_equiv_unit _))
    in
    eq
  )

val p_combine_equiv (p1 p2 : nat -> vprop) (i j : nat)
  : Tot (vprop_equiv (range p1 i j ** range p2 i j) (range (fun i -> p1 i ** p2 i) i j))
let p_combine_equiv p1 p2 i j = magic()

let rewrite_ = Pulse.Lib.Core.rewrite

```pulse
ghost
fn p_join (p : (nat->vprop)) (i j k : nat) (_ : squash (i <= j /\ j <= k))
  requires range p i j ** range p j k
  ensures  range p i k
{
  rewrite_ _ _ (p_join_equiv p i j k ())
}
```

```pulse
fn p_split (p : (nat->vprop)) (i j k : nat) (_ : squash (i <= j /\ j <= k))
  requires range p i k
  ensures range p i j ** range p j k
{
  rewrite_ _ _ (vprop_equiv_sym _ _ (p_join_equiv p i j k ()))
}
```

```pulse
ghost
fn p_join_last (p : (nat->vprop)) (n : nat) (_ : squash (n > 0))
  requires range p 0 (n-1) ** p (n-1)
  ensures range p 0 n
{
  rewrite_ _ _ (vprop_equiv_sym _ _ (p_join_last_equiv p n))
}
```

```pulse
ghost
fn p_split_last (p : (nat->vprop)) (n : nat) (_ : squash (n > 0))
  requires range p 0 n
  ensures range p 0 (n-1) ** p (n-1)
{
  rewrite_ _ _ (p_join_last_equiv p n)
}
```

```pulse
ghost
fn p_combine (p1 p2 : (nat->vprop)) (i j : nat)
  requires range p1 i j ** range p2 i j
  ensures range (fun i -> p1 i ** p2 i) i j
{
  rewrite_ _ _ (p_combine_equiv p1 p2 i j)
//   rewrite_ _ _ (vprop_equiv_sym _ _ (p_combine_equiv p1 p2 i j))
}
```

```pulse
ghost
fn p_uncombine (p1 p2 : (nat->vprop)) (i j : nat)
  requires range (fun i -> p1 i ** p2 i) i j
  ensures range p1 i j ** range p2 i j
{
//   rewrite_ _ _ (p_combine_equiv p1 p2 i j)
  rewrite_ _ _ (vprop_equiv_sym _ _ (p_combine_equiv p1 p2 i j))
}
```

```pulse
fn __simple_for
   (pre post : (nat -> vprop))
   (r : vprop) // This resource is passed around through iterations.
   (f : (i:nat -> stt unit (r ** pre i) (fun () -> (r ** post i))))
   (kk : (
     (n : nat) ->
     stt unit (r ** range pre 0 n) (fun _ -> r ** range post 0 n)
   ))
   (n : nat)
   requires r ** range pre 0 n
   ensures r ** range post 0 n
{
  (* Couldn't use a while loop here, weird errors, try again. *)
  if (n = 0) {
    rewrite (range pre 0 n) as emp;
    rewrite emp as (range post 0 n);
    ()
  } else {
    // rewrite (range pre 0 n) as (range pre (reveal (hide 0)) (reveal (hide n)));
    p_split_last pre n ();
    f (n-1);
    kk (n-1);
    p_join_last post n ();
    ()
  }
}
```

let simple_for  :
     (pre : (nat -> vprop)) ->
     (post : (nat -> vprop)) ->
     (r : vprop) -> // This resource is passed around through iterations.
     (f : (i:nat -> stt unit (r ** pre i) (fun () -> r ** post i))) ->
     (n : nat) ->
     stt unit (r ** range pre 0 n) (fun _ -> r ** range post 0 n)
  = 
  fun pre post r f -> fix_stt_1 (__simple_for pre post r f)

```pulse
fn for_loop
   (pre post : (nat -> vprop))
   (r : vprop) // This resource is passed around through iterations.
   (f : (i:nat -> stt unit (r ** pre i) (fun () -> (r ** post i))))
   (lo hi : nat)
   requires r ** range pre lo hi
   ensures r ** range post lo hi
{
  (* TODO: implement by just shifting simple_for? *)
  admit()
}
```


assume val frac_n (n:pos) (p:pool) (e:perm)
  : stt unit (pool_alive #e p)
             (fun () -> range (fun i -> pool_alive #(div_perm e n) p) 0 n)

assume val unfrac_n (n:pos) (p:pool) (e:perm)
  : stt unit (range (fun i -> pool_alive #(div_perm e n) p) 0 n)
             (fun () -> pool_alive #e p)

```pulse
fn spawned_f_i 
  (p:pool)
  (pre : (nat -> vprop))
  (post : (nat -> vprop))
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
fn __redeem_range
  (p : (nat -> vprop))
  (f : vprop)
  (kk : (
    (n:nat) ->
    stt unit (f ** range (fun i -> pledge emp_inames f (p i)) 0 n)
             (fun _ -> f ** range p 0 n)
  ))
  (n : nat)
  requires f ** range (fun i -> pledge emp_inames f (p i)) 0 n
  ensures f ** range p 0 n
{
  if (n = 0) {
    rewrite (range (fun i -> pledge emp_inames f (p i)) 0 n) as emp;
    rewrite emp as range p 0 n;
    ()
  } else {
    p_split_last (fun i -> pledge emp_inames f (p i)) n ();
    redeem_pledge _ f (p (n-1));
    kk (n-1);
    p_join_last p n ()
  }
}
```

let redeem_range :
  (p : (nat -> vprop)) ->
  (f : vprop) ->
    (n:nat) ->
    stt unit (f ** range (fun i -> pledge emp_inames f (p i)) 0 n)
             (fun _ -> f ** range p 0 n)
  =
  fun p f -> fix_stt_1 (__redeem_range p f)

```pulse
fn
parallel_for
  (pre : (nat -> vprop))
  (post : (nat -> vprop))
  (f : (i:nat -> stt unit (pre i) (fun () -> (post i))))
  (n : pos)
  requires range pre 0 n
  ensures range post 0 n
{
  let p = setup_pool 42;
  (* Use a normal for loop to *spawn* each task *)
  
  (* First, share the pool_alive permission among all n tasks. *)
  assert (pool_alive #1.0R p);
  frac_n n p 1.0R;
  
  p_combine pre (fun i -> pool_alive #(div_perm 1.0R n) p) 0 n;

  simple_for
    (fun i -> pre i ** pool_alive #(div_perm 1.0R n) p)
    (fun i -> pledge emp_inames (pool_done p) (post i) ** pool_alive #(div_perm 1.0R n) p)
    emp // Alternative: pass pool_alive p here and forget about the n-way split. See below.
    (spawned_f_i p pre post (div_perm 1.0R n) f)
    n;
    
  p_uncombine (fun i -> pledge emp_inames (pool_done p) (post i)) (fun i -> pool_alive #(div_perm 1.0R n) p) 0 n;
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
  (pre : (nat -> vprop))
  (post : (nat -> vprop))
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
  (pre : (nat -> vprop))
  (post : (nat -> vprop))
  (f : (i:nat -> stt unit (pre i) (fun () -> (post i))))
  (n : pos)
  requires range pre 0 n
  ensures range post 0 n
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

#push-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection'"
#push-options "--retry 2 --ext 'pulse:rvalues'" // GM: Part of this VC fails on batch mode, not on ide...

let wsr_loop_inv_f
  (pre : (nat -> vprop))
  (post : (nat -> vprop))
  (full_post : (nat -> vprop))
  (n : pos)
  (i : ref int)
  (b:bool)
  : Tot vprop
  =
  exists* (ii:nat).
       pts_to i ii
    ** full_post ii
    ** range post ii n
    ** pure (b == (Prims.op_LessThan ii n))

let wsr_loop_inv_tf
  (pre : (nat -> vprop))
  (post : (nat -> vprop))
  (full_post : (nat -> vprop))
  (n : pos)
  (i : ref int)
  : Tot vprop =
  exists* (b:bool). wsr_loop_inv_f pre post full_post n i b
  
(* This can be ghost. *)
```pulse
fn
__ffold
  (p : (nat -> vprop))
  (fp : (nat -> vprop))
  (ss : (i:nat -> stt_ghost unit emp_inames (p i ** fp i) (fun () -> fp (i+1))))
  (n : nat)
  (kk: (
        (i:nat) -> stt unit (pure (i <= n) ** fp i ** range p i n) (fun _ -> fp n)
  ))
  (i : nat)
  requires pure (i <= n) ** fp i ** range p i n
  ensures fp n
{
   if (i = n) {
     rewrite (range p i n) as emp;
     rewrite fp i as fp n;
     ()
   } else {
     assert (fp i ** range p i n);
     rewrite (range p i n) as (p i ** range p (i+1) n);
     ss i;
     kk (i+1);
     ()
   }
}
```
let ffold
  (p : (nat -> vprop))
  (fp : (nat -> vprop))
  (ss : (i:nat -> stt_ghost unit emp_inames (p i ** fp i) (fun () -> fp (i+1))))
  (n:nat)
  : (i:nat) -> stt unit (pure (i <= n) ** fp i ** range p i n) (fun _ -> fp n)
  = fix_stt_1 (__ffold p fp ss n)

(* This can be ghost. *)
```pulse
fn
__funfold
  (p : (nat -> vprop))
  (fp : (nat -> vprop))
  (ss : (i:nat -> stt_ghost unit emp_inames (fp (i+1)) (fun () -> p i ** fp i)))
  (kk: (
        (n:nat) -> stt unit (fp n) (fun _ -> fp 0 ** range p 0 n)
  ))
  (n : nat)
  requires fp n
  ensures fp 0 ** range p 0 n
{
   if (n = 0) {
     rewrite fp n as fp 0;
     rewrite emp as range p 0 n;
     ()
   } else {
     assert (fp n);
     rewrite fp n as fp ((n-1)+1);
     ss (n-1);
     assert (p (n-1) ** fp (n-1));
     kk (n-1);
     p_join_last p n ()
   }
}
```
let funfold
  (p : (nat -> vprop))
  (fp : (nat -> vprop))
  (ss : (i:nat -> stt_ghost unit emp_inames (fp (i+1)) (fun () -> p i ** fp i)))
  : (n:nat) -> stt unit (fp n) (fun _ -> fp 0 ** range p 0 n)
  = fix_stt_1 (__funfold p fp ss)

```pulse
fn
parallel_for_wsr
  (pre : (nat -> vprop))
  (post : (nat -> vprop))
  (full_pre : (nat -> vprop))
  (full_post : (nat -> vprop))
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
  (#pre:vprop) (#post:a -> vprop)
  (frame:vprop)
  (e:stt a pre post)
  : stt a (frame ** pre) (fun x -> frame ** post x)

#set-options "--ext pulse:guard_policy=SMTSync"

```pulse
fn h_for_task__
  (p:pool)
  (e:perm)
  (pre : (nat -> vprop))
  (post : (nat -> vprop))
  (f : (i:nat -> stt unit (pre i) (fun () -> post i)))
  (lo hi : nat)
  (_:unit)
  requires pool_alive #e p ** range pre lo hi
  ensures pledge emp_inames (pool_done p) (range post lo hi)
{
  admit()
}
```

```pulse
fn h_for_task
  (p:pool)
  (e:perm)
  (pre : (nat -> vprop))
  (post : (nat -> vprop))
  (f : (i:nat -> stt unit (pre i) (fun () -> post i)))
  (lo hi : nat)
  (_:unit)
  requires pool_alive #e p ** range pre lo hi
  ensures pledge emp_inames (pool_done p) (range post lo hi)
{
  if (hi - lo < 100) {
    (* Too small, just run sequentially *)
    drop_ (pool_alive #e p); // won't use the pool
    for_loop pre post emp
             (fun i -> frame_stt_left emp (f i)) lo hi;

    return_pledge (pool_done p) (range post lo hi)
  } else {
    let mid = (hi+lo)/2;
    assert (pure (lo <= mid /\ mid <= hi));

    share_alive p e;
    share_alive p (e /. 2.0R);

    p_split pre lo mid hi ();

    spawn_ #(pool_alive #((e /. 2.0R) /. 2.0R) p ** range pre lo mid)
            #(pledge emp_inames (pool_done p) (range post lo mid))
            p
            #(e /. 2.0R)
            (h_for_task__ p ((e /. 2.0R) /. 2.0R) pre post f lo mid);

    spawn_ #(pool_alive #((e /. 2.0R) /. 2.0R) p ** range pre mid hi)
            #(pledge emp_inames (pool_done p) (range post mid hi))
            p
            #(e /. 2.0R)
            (h_for_task__ p ((e /. 2.0R) /. 2.0R) pre post f mid hi);

    (* We get this complicated pledge emp_inames from the spawns above. We can
    massage it before even waiting. *)
    assert (pledge emp_inames (pool_done p) (pledge emp_inames (pool_done p) (range post lo mid)));
    assert (pledge emp_inames (pool_done p) (pledge emp_inames (pool_done p) (range post mid hi)));

    squash_pledge (pool_done p) (range post lo mid);
    squash_pledge (pool_done p) (range post mid hi);

    join_pledge #emp_inames #(pool_done p) (range post lo mid) (range post mid hi);
    rewrite_pledge
      #emp_inames
      #(pool_done p)
      (range post lo mid ** range post mid hi)
      (range post lo hi)
      (p_join post lo mid hi);

    (* Better *)
    assert (pledge emp_inames (pool_done p) (range post lo hi));

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

#push-options "--print_implicits --ugly"
```pulse
fn
parallel_for_hier
  (pre : (nat -> vprop))
  (post : (nat -> vprop))
  (f : (i:nat -> stt unit (pre i) (fun () -> (post i))))
  (n : pos)
  requires range pre 0 n
  ensures range post 0 n
{
  let p = setup_pool 42;

  if (false) { // Checking that both branches would work
    (* Spawning the first task: useless! Just call it! *)
    assert (pool_alive #1.0R p);
    share_alive p 1.0R;

    rewrite (pool_alive #(1.0R /. 2.0R) p ** pool_alive #(1.0R /. 2.0R) p)
        as (pool_alive #0.5R p ** pool_alive #0.5R p);
    assert (pool_alive #0.5R p ** pool_alive #0.5R p);


    spawn_ #(pool_alive #0.5R p ** range pre 0 n)
            #(pledge emp_inames (pool_done p) (range post 0 n))
            p
            #0.5R
            (h_for_task p 0.5R pre post f 0 n);

    (* We get this complicated pledge emp_inames from the spawn above. We can
    massage it before even waiting. *)
    assert (pledge emp_inames (pool_done p) (pledge emp_inames (pool_done p) (range post 0 n)));

    squash_pledge (pool_done p) (range post 0 n);

    assert (pledge emp_inames (pool_done p) (range post 0 n));

    wait_pool p 0.5R;

    redeem_pledge emp_inames (pool_done p) (range post 0 n);

    drop_ (pool_done p)
  } else {
    (* Directly calling is much easier, and actually better all around. *)
    share_alive p 1.0R;
    h_for_task p (1.0R /. 2.0R) pre post f 0 n ();

    wait_pool p (1.0R /. 2.0R);

    assert (pool_done p);

    redeem_pledge emp_inames (pool_done p) (range post 0 n);

    drop_ (pool_done p)
  }
}
```
