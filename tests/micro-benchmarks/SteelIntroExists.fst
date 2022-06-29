(*

Experimenting with automating the introduction of existentials


1. Difficulties in applying intro_exists:

 {  A  }

    { ?p ?w }
     intro_exists ?w ?p
    { ex ?p }

 { ex ?p * ?f }

 { ... }

This requires solving, since intro_exists is framed:

  A =?=> ?p ?w * ?f

This can't be solved since we have two unknowns on the LHS.

--------------------------------------------------------------------------------
2.

One might consider turning intro_exists into the SteelF effect, so
that we don't add another frame, but that's not what's desired either.

Consider:

  val free (p:ptr) : ST _ (ex (fun v -> p `pts_to` v)) emp


let caller (p q:ptr) : ST _ (p `pts_to` 17 `star` q `pts_to` 18) =
  intro_exists _ _; //if this were not framed
                    //then we would capture both p and q under the exists
                    //and this wouldn't unify with the pre of `free p` anyway
  free p

--------------------------------------------------------------------------------

So, our idea is to enhance the framing tactic directly so that it can
introduce existentials "on the fly" without introducing additional
vprop variables, as in case 1.

i.e. we want to write


let caller (p q:ptr) : ST _ (p `pts_to` 17 `star` q `pts_to` 18) =
  free p;
  ...

And this would generate constraints like so

{  p `pts_to` 17 `star` q `pts_to` 18 }

    { ex (pts_to p) }
      free p
    { emp }

{emp * ?f }


and we would try to solve


p `pts_to` 17 `star` q `pts_to` 18
==>
ex (pts_to p) * ?f

And this has only 1 unknown, so we have some hope of solving for ?f

The basic idea is as follows:

In case the current unification heuristics fail, i.e.,

  1. let LEX = { ex p1, .., ex pn } be all the unique occurrences of
     ex terms on the LHS

  2. let REX = { ex q1, .., ex qm } be all the unique occurrences of
     ex terms on the RLHS

  3. Cancel terms in LEX with terms from REX:

     For each element l in LEX, find a unique element r in REX such
     that l unifies with r.

       - If successful, remove l and r from LEX and REX and repeat

       - If not, fail: there is an exists in LEX that cannot be
         matched in REX.

     Limitation: We are not handling AC rewriting under a quantifier, e.g.,

        ex (fun v -> p * q)  will not match
        ex (fun v -> q * p)

     We could enhance this step, so that rather than finding a unifier
     between l and r, we find instead a double implication, e.g., by
     applying lemma like equiv_exists

     Lemma (forall v. p v <==> q v)
           (ex p <==> ex q)


  4. Now, we may have some remaining terms in REX and for these we aim
     to introduce exists from the remaining terms in L


     1. For each r in REX, open the existential with a fresh
          unification variable for the witness

        This corresponds to an application of the following logical rule
       "backwards" to the goal:

       intro_exists (x:a) (v: a -> vprop)
          : Lemma (v x `can_be_split` (ex v))

     2. unifying what's left in RHS with whatever was not yet cancelled in LHS
*)
module SteelIntroExists
open Steel.Effect.Common
open Steel.ST.GenElim

module T = FStar.Tactics

#set-options "--ide_id_info_off"

assume
val ptr : Type0
assume
val pts_to0 (p: ptr) (v: nat) : vprop

assume
val write0 (p: ptr) (n: nat) : STT unit (exists_ (fun n' -> pts_to0 p n')) (fun _ -> pts_to0 p n)

// This is fine
let endure6 (p1 p2 p3 p4 p5 p6: ptr) : STT unit
  (exists_ (fun v1 -> exists_ (fun v2 -> exists_ (fun v3 -> exists_ (fun v4 -> exists_ (fun v5 -> exists_ (fun v6 ->
    pts_to0 p1 v1 `star`
    pts_to0 p2 v2 `star`
    pts_to0 p3 v3 `star`
    pts_to0 p4 v4 `star`
    pts_to0 p5 v5 `star`
    pts_to0 p6 v6
  )))))))
  (fun _ -> exists_ (fun v1 -> exists_ (fun v2 -> exists_ (fun v3 -> exists_ (fun v4 -> exists_ (fun v5 -> exists_ (fun v6 ->
    pts_to0 p1 v1 `star`
    pts_to0 p2 v2 `star`
    pts_to0 p3 v3 `star`
    pts_to0 p4 v4 `star`
    pts_to0 p5 v5 `star`
    pts_to0 p6 v6
  )))))))
= let _ = gen_elim () in
  write0 p2 18;
  write0 p4 42;
  return ()

let endure_tuple3 (opened: _) (p1 p2 p3 p4 p5 p6: ptr) : STGhostT unit opened
  (exists_ (fun (res:dtuple2 nat (fun _ -> nat)) -> exists_ (fun (fres: dtuple2 nat (fun _ -> nat)) -> exists_ (fun (dres: dtuple2 nat (fun _ -> nat)) ->
    pts_to0 p1 (dfst res) `star`
    pts_to0 p2 (dfst res) `star`
    pts_to0 p3 (dfst fres) `star`
    pts_to0 p4 (dsnd fres) `star`
    pts_to0 p5 (dfst dres) `star`
    pts_to0 p6 (dsnd dres)
  ))))
  (fun _ -> emp)
= let _ = gen_elim () in
  admit_ ()

let endure_tuple2 (opened: _) (p1 p2 p3 p4 p5 p6: ptr) : STGhostT unit opened
  (exists_ (fun (res:dtuple2 nat (fun _ -> dtuple2 nat (fun _ -> nat))) -> exists_ (fun (dres: dtuple2 nat (fun _ -> dtuple2 nat (fun _ -> nat))) ->
    pts_to0 p1 (dfst res) `star`
    pts_to0 p2 (dfst (dsnd res)) `star`
    pts_to0 p3 (dsnd (dsnd res)) `star`
    pts_to0 p4 (dfst dres) `star`
    pts_to0 p5 (dfst (dsnd dres)) `star`
    pts_to0 p6 (dsnd (dsnd dres))
  )))
  (fun _ -> emp)
= let _ = gen_elim () in
  admit_ ()

let endure_tuple1 (opened: _) (p1 p2 p3 p4 p5 p6: ptr) : STGhostT unit opened
  (exists_ (fun (res:dtuple2 nat (fun _ -> dtuple2 nat (fun _ -> dtuple2 nat (fun _ -> dtuple2 nat (fun _ -> dtuple2 nat (fun _ -> nat)))))) ->
    pts_to0 p1 (dfst res) `star`
    pts_to0 p2 (dfst (dsnd res)) `star`
    pts_to0 p3 (dfst (dsnd (dsnd res))) `star`
    pts_to0 p4 (dfst (dsnd (dsnd (dsnd res)))) `star`
    pts_to0 p5 (dfst (dsnd (dsnd (dsnd (dsnd res))))) `star`
    pts_to0 p6 (dsnd (dsnd (dsnd (dsnd (dsnd res)))))
  ))
  (fun _ -> emp)
= let _ = gen_elim () in
  admit_ ()

let endure4 (opened: _) (p1 p2 p3 p4: ptr) : STGhostT unit opened
  (exists_ (fun v1 -> exists_ (fun v2 -> exists_ (fun v3 -> exists_ (fun v4 ->
    pts_to0 p1 v1 `star`
    pts_to0 p2 v2 `star`
    pts_to0 p3 v3 `star`
    pts_to0 p4 v4
  )))))
  (fun _ -> emp)
= let _ = gen_elim () in
  admit_ ()

let endure5 (opened: _) (p1 p2 p3 p4 p5: ptr) : STGhostT unit opened
  (exists_ (fun v1 -> exists_ (fun v2 -> exists_ (fun v3 -> exists_ (fun v4 -> exists_ (fun v5 ->
    pts_to0 p1 v1 `star`
    pts_to0 p2 v2 `star`
    pts_to0 p3 v3 `star`
    pts_to0 p4 v4 `star`
    pts_to0 p5 v5
  ))))))
  (fun _ -> emp)
= let _ = gen_elim () in
  admit_ ()

let gen_elim_6_baseline (#opened: _) (#p1 #p2 #p3 #p4 #p5 #p6: ptr) () : STGhostT (Ghost.erased (dtuple2 nat (fun _ -> dtuple2 nat (fun _ -> dtuple2 nat (fun _ -> dtuple2 nat (fun _ -> dtuple2 nat (fun _ -> nat))))))) opened
  (exists_ (fun v1 -> exists_ (fun v2 -> exists_ (fun v3 -> exists_ (fun v4 -> exists_ (fun v5 -> exists_ (fun v6 ->
    pts_to0 p1 v1 `star`
    pts_to0 p2 v2 `star`
    pts_to0 p3 v3 `star`
    pts_to0 p4 v4 `star`
    pts_to0 p5 v5 `star`
    pts_to0 p6 v6
  )))))))
  (fun res ->
    pts_to0 p1 (dfst res) `star`
    pts_to0 p2 (dfst (dsnd res)) `star`
    pts_to0 p3 (dfst (dsnd (dsnd res))) `star`
    pts_to0 p4 (dfst (dsnd (dsnd (dsnd res)))) `star`
    pts_to0 p5 (dfst (dsnd (dsnd (dsnd (dsnd res))))) `star`
    pts_to0 p6 (dsnd (dsnd (dsnd (dsnd (dsnd res)))))
  )
= let x1 = elim_exists () in
  let x2 = elim_exists () in
  let x3 = elim_exists () in
  let x4 = elim_exists () in
  let x5 = elim_exists () in
  let x6 = elim_exists () in
  let res = Ghost.hide (| Ghost.reveal x1, (| Ghost.reveal x2, (| Ghost.reveal x3, (| Ghost.reveal x4, (| Ghost.reveal x5, Ghost.reveal x6 |) |) |) |) |) in
  res

let endure6_baseline (opened: _) (p1 p2 p3 p4 p5 p6: ptr) : STGhostT unit opened
  (exists_ (fun v1 -> exists_ (fun v2 -> exists_ (fun v3 -> exists_ (fun v4 -> exists_ (fun v5 -> exists_ (fun v6 ->
    pts_to0 p1 v1 `star`
    pts_to0 p2 v2 `star`
    pts_to0 p3 v3 `star`
    pts_to0 p4 v4 `star`
    pts_to0 p5 v5 `star`
    pts_to0 p6 v6
  )))))))
  (fun _ -> emp)
= let _ = gen_elim_6_baseline () in
  admit_ ()

(* // Typechecking this admit() is slow
let gen_elim_6_gen (#opened: _) (#t1: _) (#t2: t1 -> Type0) (#t3: (x1: t1) -> t2 x1 -> Type0) (#t4: (x1: t1) -> (x2: t2 x1) -> t3 x1 x2 -> Type0) (#t5: (x1: t1) -> (x2: t2 x1) -> (x3: t3 x1 x2) -> t4 x1 x2 x3 -> Type0) (#t6: (x1: t1) -> (x2: t2 x1) -> (x3: t3 x1 x2) -> (x4: t4 x1 x2 x3) -> t5 x1 x2 x3 x4 -> Type0) (#p: (x1: t1) -> (x2: t2 x1) -> (x3: t3 x1 x2) -> (x4: t4 x1 x2 x3) -> (x5: t5 x1 x2 x3 x4) -> t6 x1 x2 x3 x4 x5 -> vprop) (_: unit) : STGhostT (Ghost.erased (dtuple2 t1 (fun x1 -> dtuple2 (t2 x1) (fun x2 -> dtuple2 (t3 x1 x2) (fun x3 -> dtuple2 (t4 x1 x2 x3) (fun x4 -> dtuple2 (t5 x1 x2 x3 x4) (fun x5 -> t6 x1 x2 x3 x4 x5))))))) opened
  (exists_ (fun v1 -> exists_ (fun v2 -> exists_ (fun v3 -> exists_ (fun v4 -> exists_ (fun v5 -> exists_ (fun v6 -> p v1 v2 v3 v4 v5 v6)))))))
  (fun res -> p (dfst res) (dfst (dsnd res)) (dfst (dsnd (dsnd res))) (dfst (dsnd (dsnd (dsnd res)))) (dfst (dsnd (dsnd (dsnd (dsnd res))))) (dsnd (dsnd (dsnd (dsnd (dsnd res)))))
  )
= admit_ ()
*)

(* // Typechecking this combinator is very slow and memory-consuming
let gen_elim_6_gen (#opened: _) (#t1: _) (#t2: t1 -> Type0) (#t3: (x1: t1) -> t2 x1 -> Type0) (#t4: (x1: t1) -> (x2: t2 x1) -> t3 x1 x2 -> Type0) (#t5: (x1: t1) -> (x2: t2 x1) -> (x3: t3 x1 x2) -> t4 x1 x2 x3 -> Type0) (#t6: (x1: t1) -> (x2: t2 x1) -> (x3: t3 x1 x2) -> (x4: t4 x1 x2 x3) -> t5 x1 x2 x3 x4 -> Type0) (#p: (x1: t1) -> (x2: t2 x1) -> (x3: t3 x1 x2) -> (x4: t4 x1 x2 x3) -> (x5: t5 x1 x2 x3 x4) -> t6 x1 x2 x3 x4 x5 -> vprop) (_: unit) : STGhostT (Ghost.erased (dtuple2 t1 (fun x1 -> dtuple2 (t2 x1) (fun x2 -> dtuple2 (t3 x1 x2) (fun x3 -> dtuple2 (t4 x1 x2 x3) (fun x4 -> dtuple2 (t5 x1 x2 x3 x4) (fun x5 -> t6 x1 x2 x3 x4 x5))))))) opened
  (exists_ (fun v1 -> exists_ (fun v2 -> exists_ (fun v3 -> exists_ (fun v4 -> exists_ (fun v5 -> exists_ (fun v6 -> p v1 v2 v3 v4 v5 v6)))))))
  (fun res -> p (dfst res) (dfst (dsnd res)) (dfst (dsnd (dsnd res))) (dfst (dsnd (dsnd (dsnd res)))) (dfst (dsnd (dsnd (dsnd (dsnd res))))) (dsnd (dsnd (dsnd (dsnd (dsnd res)))))
  )
= let x1 = elim_exists () in
  let x2 = elim_exists () in
  let x3 = elim_exists () in
  let x4 = elim_exists () in
  let x5 = elim_exists () in
  let x6 = elim_exists () in
  Ghost.hide (| x1, (| x2, (| x3, (| x4, (| x5, x6 |) |) |) |) |)
*)

// typechecking this assume is fairly slow
assume val gen_elim_6_gen (#opened: _) (#t1: _) (#t2: t1 -> Type0) (#t3: (x1: t1) -> t2 x1 -> Type0) (#t4: (x1: t1) -> (x2: t2 x1) -> t3 x1 x2 -> Type0) (#t5: (x1: t1) -> (x2: t2 x1) -> (x3: t3 x1 x2) -> t4 x1 x2 x3 -> Type0) (#t6: (x1: t1) -> (x2: t2 x1) -> (x3: t3 x1 x2) -> (x4: t4 x1 x2 x3) -> t5 x1 x2 x3 x4 -> Type0) (#p: (x1: t1) -> (x2: t2 x1) -> (x3: t3 x1 x2) -> (x4: t4 x1 x2 x3) -> (x5: t5 x1 x2 x3 x4) -> t6 x1 x2 x3 x4 x5 -> vprop) (_: unit) : STGhostT (Ghost.erased (dtuple2 t1 (fun x1 -> dtuple2 (t2 x1) (fun x2 -> dtuple2 (t3 x1 x2) (fun x3 -> dtuple2 (t4 x1 x2 x3) (fun x4 -> dtuple2 (t5 x1 x2 x3 x4) (fun x5 -> t6 x1 x2 x3 x4 x5))))))) opened
  (exists_ (fun v1 -> exists_ (fun v2 -> exists_ (fun v3 -> exists_ (fun v4 -> exists_ (fun v5 -> exists_ (fun v6 -> p v1 v2 v3 v4 v5 v6)))))))
  (fun res -> p (dfst res) (dfst (dsnd res)) (dfst (dsnd (dsnd res))) (dfst (dsnd (dsnd (dsnd res)))) (dfst (dsnd (dsnd (dsnd (dsnd res))))) (dsnd (dsnd (dsnd (dsnd (dsnd res)))))
  )

let endure6_gen (opened: _) (p1 p2 p3 p4 p5 p6: ptr) : STGhostT unit opened
  (exists_ (fun v1 -> exists_ (fun v2 -> exists_ (fun v3 -> exists_ (fun v4 -> exists_ (fun v5 -> exists_ (fun v6 ->
    pts_to0 p1 v1 `star`
    pts_to0 p2 v2 `star`
    pts_to0 p3 v3 `star`
    pts_to0 p4 v4 `star`
    pts_to0 p5 v5 `star`
    pts_to0 p6 v6
  )))))))
  (fun _ -> emp)
= let _ = gen_elim_6_gen () in
  admit_ ()

assume
val pts_to1 (p: ptr) (v: Ghost.erased nat) : vprop

assume
val pts_to2 (p: ptr) (v: Ghost.erased bool) : vprop

assume
val split
  (#v: Ghost.erased nat)
  (p: ptr)
: STT ptr
    (pts_to1 p v)
    (fun res -> exists_ (fun vl -> pts_to1 p vl `star` exists_ (fun vr -> pts_to1 res vr)))

assume
val pts_to2_intro
  (#opened: _)
  (#v: Ghost.erased nat) (p: ptr)
: STGhostT (Ghost.erased bool) opened
    (pts_to1 p v)
    (fun res -> pts_to2 p res)

let test_split1
  (#v: Ghost.erased nat)
  (p: ptr)
: STT ptr
    (pts_to1 p v)
    (fun res -> exists_ (fun vl -> pts_to2 p vl `star` exists_ (fun vres -> pts_to1 res vres)))
=
  let res = split p in
  let _ = elim_exists () in
  let _ = elim_exists () in
  noop ();
  let _ = pts_to2_intro p in
  noop ();
  return res

let test_split2
  (#v: Ghost.erased nat)
  (p: ptr)
: STT ptr
    (pts_to1 p v)
    (fun res -> exists_ (fun vl -> pts_to2 p vl `star` exists_ (fun vres -> pts_to1 res vres)))
=
  let res = split p in
  let _ = gen_elim () in
  noop ();
  let _ = pts_to2_intro p in
  intro_exists _ (fun vres -> pts_to1 res vres);
  noop ();
  return res

// [@@expect_failure]
let test_split
  (#v: Ghost.erased nat)
  (p: ptr)
: STT ptr
    (pts_to1 p v)
    (fun res -> exists_ (fun vl -> pts_to2 p vl `star` exists_ (fun vres -> pts_to1 res vres)))
=
  let res = split p in
  let z = gen_elim () in
  noop ();
  let r = pts_to2_intro p in
  noop ();
  return res

assume
val pts_to (p:ptr) (v:int) : vprop

assume
val free (p:ptr) : STT unit (exists_ (fun v -> pts_to p v)) (fun _ -> emp)

let free_one_default (p q r:ptr)
  : STT unit
    (pts_to p 17 `star` pts_to q 18 `star` pts_to r 19)
    (fun _ -> pts_to p 17 `star` pts_to r 19)
 = intro_exists _ (fun v -> pts_to q v);
   let _ = free q in ()

// assume
// val intro_exists_f (#a:Type) (#opened_invariants:_) (x:a) (p:a -> vprop)
//   : STGhostF unit opened_invariants (p x) (fun _ -> exists_ (fun v -> p v)) (True) (fun _ -> True)


// // [@@expect_failure] //we incorrectly pick a too-specific solution failing to generalize over the witness
// // let free_one_explicit (p q:ptr)
// //   : STT unit
// //     (pts_to p 17)
// //     (fun _ -> emp)
// //  = let _ = intro_exists_f 17 _  in
// //    free p
// //#push-options "--tactic_trace_d 1"

let free_one (p q r:ptr)
  : STT unit
    (pts_to p 17 `star` pts_to q 18 `star` pts_to r 19)
    (fun _ -> pts_to p 17 `star` pts_to r 19)
 = let _ = free q in ()

assume
val free2 (p q:ptr) : STT unit (exists_ (fun v -> pts_to p v) `star`
                                exists_ (fun v -> pts_to q v))
                               (fun _ -> emp)


let free_two (p q r:ptr)
  : STT unit
    (pts_to p 17 `star` pts_to q 18 `star` pts_to r 19)
    (fun _ -> pts_to r 19)
 = free p; free q; ()

assume
val correlate (p q:ptr) : STT unit (exists_ (fun v -> pts_to p v `star` pts_to q v))
                                   (fun _ -> emp)

let free_correlate (p q:ptr)
  : STT unit
    (pts_to q 17 `star` pts_to p 17)
    (fun _ -> emp)
 = correlate p q; ()


let free_correlate_alt (p q:ptr)
  : STT unit
    (pts_to p 17 `star` pts_to q 17)
    (fun _ -> emp)
 = correlate p q; ()

assume
val alloc (n:nat) : STT ptr emp (fun p -> pts_to p n)

let construct () : STT ptr emp (fun p -> exists_ (fun v -> pts_to p v)) =
  let p = alloc 17 in
  p

assume
val write (p: ptr) (n: nat) : STT unit (exists_ (fun n' -> pts_to p n')) (fun _ -> pts_to p n)

assume
val pts_to_rev (n:nat) (p:ptr) : vprop

assume
val alloc_rev (n:nat) : STT ptr emp (fun p -> pts_to_rev n p)


let construct_rev () : STT ptr emp (fun p -> exists_ (fun v -> pts_to_rev v p)) =
  let p = alloc_rev 17 in
  p

let test_exists_intro_pure
  (p: ptr)
: STT unit (exists_ (fun n -> pts_to p n)) (fun _ -> exists_ (fun n -> pts_to p n `star` pure (n == 18)))
=
  write p 18;
  ()

let test_exists_intro_pure2
  (p: ptr)
: STT unit (exists_ (fun n -> pts_to p n)) (fun _ -> exists_ (fun n -> pts_to p n `star` pure (n == 18)))
=
  write p 42;
  write p 18;
  ()

let test_exists_intro_pure'
  (p: ptr)
  (i:nat)
: STT unit (exists_ (fun n -> pts_to p n)) (fun _ -> exists_ (fun n -> pts_to p n `star` pure (n == 18)))
= if i = 18
  then
    let h : squash (i == 18) = () in
    let _ = write p i in
    ()
  else let _ = write p 18 in ()

let test_exists_intro_pure''
  (p: ptr)
  (i:nat)
: STT unit (exists_ (fun n -> pts_to p n)) (fun _ -> exists_ (fun n -> pts_to p n `star` pure (n == 18)))
= if i = 18
  then
    let _ = write p i in
    ()
  else let _ = write p 18 in ()

let test_intro_pure
  (x: int)
  (sq: squash (x == 18))
: STT unit emp (fun _ -> pure (x == 18))
= 
  let _ = () in
  return ()

let test_intro_pure'
  (x: int)
: ST unit emp (fun _ -> pure (x == 18)) (requires (x == 18)) (ensures (fun _ -> True))
= 
  let _ = noop () in
  return ()

assume val decr_weak
  (p: ptr)
: STT unit (exists_ (fun x -> p `pts_to` x `star` pure (if x > 0 then True else False))) (fun _ -> exists_ (fun x -> p `pts_to` x))

let test_decr_weak
  (p: ptr)
: STT unit (exists_ (fun x -> p `pts_to` x)) (fun _ -> exists_ (fun x -> p `pts_to` x))
= write p 42; // good news: replacing with 0 will correctly make the error message point to the violated precondition in decr_weak
  decr_weak p;
  return ()

assume
val pred ([@@@smt_fallback] _ : nat) : vprop

let test (x y:nat) : ST unit (pred x) (fun _ -> pred 17 `star` pure ((x > y)==true)) (requires x == 17 /\ x > y) (ensures fun _ -> True) =
 let _ = noop () in 
 return ()

(* Testing gen_elim *)

let test_gen_elim
  (#opened: _) (p q: nat -> vprop) : STGhostT unit opened (exists_ p `star` exists_ q) (fun _ -> emp)
=
  let _ = gen_elim () in
  let _ = noop () in
  let vp = vpattern_replace p in
  let vq = vpattern_replace q in
  drop (p vp);
  drop (q vq);
  ()

let f
  (p q: vprop)
  (x: nat)
: ST bool  (exists_ (fun n -> p `star` q `star` pure (n > 42 /\ x > 18))) (fun _ -> q) True (fun _ -> x > 18)
= noop ();
  let _ = gen_elim () in
  drop p;
  return true

let f'
  (p: ptr)
  (q: vprop)
  (x: nat)
: ST bool  (exists_ (fun n -> (p `pts_to` n) `star` q `star` pure (n > 42 /\ x > 18))) (fun _ -> q) True (fun _ -> x > 18)
= noop ();
  let _ = gen_elim () in
  noop ();
  free p;
  return true

assume
val pred' ([@@@smt_fallback] _ : nat) : vprop

let g
  ()
: STT bool (exists_ (fun n -> exists_ (fun p -> pred n `star` pred' p `star` pure (n == 18 /\ p == 42)))) (fun _ -> pred 18 `star` pred' 42)
= noop ();
  let _ = gen_elim () in
  noop ();
  return true

let h
  (r: vprop)
  (f: ((#opened: _) -> unit -> STGhostT unit opened
    r
    (fun _ -> exists_ (fun n -> exists_ (fun p -> pred n `star` pred' p `star` pure (n == 18 /\ p == 42))))))
: STT bool r (fun _ -> pred 18 `star` pred' 42)
= f ();
  let _ = gen_elim () in
  noop ();
  return true

let h'
  (#opened: _)
  (r: vprop)
  (f: ((#opened: _) -> unit -> STGhostT nat opened
    r
    (fun res -> exists_ (fun n -> exists_ (fun p -> pred n `star` pred' p `star` pure (n == 18 /\ p == res))))))
: STGhostT nat opened r (fun n -> pred 18 `star` pred' n)
= let res = f () in
  let _ = gen_elim () in
  noop ();
  res

let h3
  (#opened: _)
  (r: vprop)
  (f: ((#opened: _) -> unit -> STGhostT unit opened
    r
    (fun _ -> exists_ (fun n -> exists_ (fun p -> pred n `star` pred' p `star` pure (n == 18))))))
: STGhostT nat opened r (fun n -> pred 18 `star` pred' n)
= f ();
  let _ = gen_elim () in
  let res = vpattern (fun res -> pred' res) in
  noop ();
  res

let h30
  (#opened: _)
: STGhostT nat opened (pred' 18) (fun n -> exists_ (fun q -> pred' q `star` pure (q == n)))
=
  let res = vpattern (fun res -> pred' res) in
  noop ();
  res

let h31'
  (#opened: _)
: STGhostT nat opened (exists_ (fun n -> pred' n)) (fun n -> exists_ (fun q -> pred' q `star` pure (q == n)))
= let _ = elim_exists () in
  let res = vpattern (fun res -> pred' res) in
  noop ();
  res

assume
val pred0 (_ : nat) : vprop

let h3f
  (#opened: _)
: STGhostT nat opened (exists_ (fun n -> pred0 n)) (fun n -> exists_ (fun q -> pred0 q `star` pure (q == n)))
= let _ = elim_exists () in
  let res = vpattern (fun res -> pred0 res) in
  noop ();
  res

let eqprop (#a: Type) (b1 b2: a) : Tot prop = b1 == b2

let h31
  (#opened: _)
: STGhostT nat opened (exists_ (fun n -> pred0 n)) (fun n -> exists_ (fun q -> pred0 q `star` pure (q `eqprop` n)))
=
  let v = gen_elim () in
  let res = vpattern (fun res -> pred0 res) in
  noop ();
  res

let h32
  (#opened: _)
: STGhostT nat opened (exists_ (fun n -> pred' n)) (fun n -> exists_ (fun q -> pred' q `star` pure (q == n)))
= let _ = gen_elim () in
  let res = vpattern (fun res -> pred' res) in
  noop ();
  res

let h35
  (#opened: _)
: STGhostT nat opened (exists_ (fun n -> exists_ (fun p -> pred n `star` pred' p `star` pure (n == 18)))) (fun n -> pred 18 `star` exists_ (fun q -> pred' q `star` pure (q == n)))
= noop ();
  let _ = gen_elim () in
  let res = vpattern (fun res -> pred' res) in
  noop ();
  res

let h4
  (#opened: _)
  (r: vprop)
  (f: ((#opened: _) -> unit -> STGhostT unit opened
    r
    (fun _ -> exists_ (fun n -> exists_ (fun p -> pred n `star` pred' p `star` pure (n == 18))))))
: STGhostT nat opened r (fun n -> pred 18 `star` exists_ (fun q -> pred' q `star` pure (q == n)))
= f ();
  let _ = gen_elim () in
  let res = vpattern (fun res -> pred' res) in
  noop ();
  res

(* This test illustrates that guard_vprop is necessary, otherwise we have:

Goal 1/1 (Instantiating meta argument in application)
p: Ghost.erased nat
al err ar: ptr
uu___: Ghost.erased (x: Ghost.erased nat & (Ghost.erased nat <: Prims.Tot Type0))
uu___'0: unit
--------------------------------------------------------------------------------
squash (gen_elim_prop_placeholder (VStar (pts_to1 al (dfstp (Ghost.reveal _)))
          (VStar (exists_ (fun v -> pts_to1 err v)) (pts_to1 ar (dsndp (Ghost.reveal _)))))
      (*?u8765*)
      _
      (fun x ->
          star (star (pts_to1 al ((*?u8818*) _ x)) (pts_to1 ar ((*?u8817*) _ x)))
            (exists_ (fun v -> pts_to1 err v)))
      (*?u552*)
      _)
(*?u50*) _


*)

assume val join (#opened: _) (#pl #pr: Ghost.erased nat) (al ar: ptr) : STGhostT (Ghost.erased nat) opened (pts_to1 al pl `star` pts_to1 ar pr) (fun res -> pts_to1 al res)

assume val v1 (#p: Ghost.erased nat) (a: ptr) (err: ptr) : STT unit
  (pts_to1 a p `star` pts_to1 err 0)
  (fun _ -> pts_to1 a p `star` exists_ (fun v -> pts_to1 err v))

let v2 (#p: Ghost.erased nat) (al: ptr) (err: ptr) : STT unit
  (pts_to1 al p `star` pts_to1 err 0)
  (fun _ -> exists_ (fun p -> pts_to1 al p `star` exists_ (fun v -> pts_to1 err v)))
= let ar = split al in
  let _ = gen_elim () in
  let _ = v1 ar err in
  let _ = gen_elim () in
  let _ = join al ar in
  return ()


assume
val expect_pos (p:ptr) : STT unit (exists_ (λ (v:pos) → pts_to p v)) (λ _ → emp)

[@@expect_failure]
let use_zero_as_pos (p:ptr)
  : STT unit (pts_to p 0) (λ _ → emp)
  = let _ = expect_pos p in ()


assume
val expect_nat (p:ptr) : STT unit (exists_ (λ (v:nat) → pts_to p v)) (λ _ → emp)

//this fails although it could succeed
//wips: [F*] (<input>(723,4-723,30)) Uvar solution for ?2022 was not well-typed. Expected Prims.nat got 0 : Prims.int [2 times]
//
[@@expect_failure]
let use_zero_as_nat (p:ptr)
  : STT unit (pts_to p 0) (λ _ → emp)
  = let _ = expect_nat p in ()
