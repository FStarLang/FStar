module Lang

open FStar.Seq
open FStar.Set
open FStar.Heap
open FStar.Classical

(* type addr = nat*)
type addr = ref nat

(*
type heap = {
  
  set addr * (s:seq nat{length s = size})

let dom (s:heap) :set addr = fst s

let memory (s:heap) :(s:seq nat{length s = size}) = snd s

let equal (h1:heap) (h2:heap)

let op_String_Access (s:heap) (id:addr) :nat = index (memory s) id
let op_String_Assignment (s:heap) (id:addr) (v:nat) :heap = (dom s, Seq.upd (memory s) id v)
let contains (s:heap) (id:addr) :Type0 = Set.mem id (dom s)

let disjoint (s1:heap) (s2:heap) :Type0 = Set.disjoint (dom s1) (dom s2)

let join (s1:heap) (s2:heap{disjoint s1 s2}) :(s:heap{dom s == Set.union (dom s1) (dom s2)              /\
                                                      (forall (i:addr). s1 `contains` i ==> s.[i] == s1.[i]) /\
                                                      (forall (i:addr). s2 `contains` i ==> s.[i] == s2.[i])})
  = admit ()
*)

let equal (h1:heap) (h2:heap) =
  (forall (r:addr). (h1 `contains` r) <==> (h2 `contains` r)) /\
  (forall (r:addr). (h1 `contains` r) /\ (h2 `contains` r) ==> (sel h1 r == sel h2 r))
  
type loop_result (a:Type0) =
  | Done : v:a   -> loop_result a
  | Again: acc:a -> loop_result a

noeq type command :Type0 -> Type =
  | Return: #a:Type -> v:a -> command a
  | Bind  : #a:Type0 -> #b:Type0 -> c1:command a -> c2:(a -> command b) -> command b
  | Loop  : #a:Type0 -> acc:a -> f:(a -> command (loop_result a)) -> command a
  | Fail  : #a:Type0 -> command a
  | Read  : id:addr -> command nat
  | Write : id:addr -> v:nat -> command unit
  | Alloc : command addr
  | Free  : id:addr -> command unit

(*
 * a bit hacky, since a program may not terminate
 *)
assume val interpreted_in (#a:Type0) (c:command a) (h:heap) :Tot (a * heap)

type heap_predicate = heap -> Type0

(* let emp (h:heap) :Type0 = dom h == Set.empty *)
let is_emp (h:heap) : Type0 = (h == emp)

(*
let lemma_disjoint_emp (h1:heap) (h2:heap)
  :Lemma (requires (emp h2))
         (ensures  (disjoint h1 h2))
	 [SMTPat (disjoint h1 h2); SMTPat (emp h2)]
  = assert (Set.equal (Set.intersect (dom h1) (dom h2)) Set.empty)


let lemma_join_emp (h1:heap) (h2:heap)
  :Lemma (requires (emp h2))
         (ensures  (disjoint h1 h2 /\ join h1 h2 == h1))
  = assert (Set.equal (dom h1) (dom (join h1 h2)));
    assert (Seq.equal (memory h1) (memory (join h1 h2)))
*)
   
(* let points_to (id:addr) (n:nat) (h:heap) :Type0 = dom h == Set.singleton id /\ h.[id] == n *)
let points_to (id:addr) (n:nat) (h:heap) : Type0 =
  (h == (restrict h (Set.singleton (addr_of id)))) /\ (sel h id == n)

let lift (phi:Type0) (h:heap) :Type0 = phi /\ is_emp h

let exists_x (#a:Type0) (pred:a -> heap_predicate) (h:heap) :Type0
  = exists (x:a). pred x h

let star (p:heap_predicate) (q:heap_predicate) (h:heap) :Type0
  = exists (h1:heap) (h2:heap). disjoint h1 h2 /\ (h == (join h1 h2)) /\ p h1 /\ q h2

let iff (p:heap_predicate) (q:heap_predicate) :Type0 = forall (h:heap). p h <==> q h

let imp (p:heap_predicate) (q:heap_predicate) :Type0 = forall (h:heap). p h ==> q h

(* some algebraic laws on the predicates *)
let lemma1_helper (phi:Type0) (p:heap_predicate) (q:heap_predicate) (h:heap)
  :Lemma (requires ((phi ==> (p `imp` q)) /\
                    (star p (lift phi) h)))
         (ensures  (q h))
 = assert (exists (h1:heap) (h2:heap). disjoint h1 h2 /\ (h == (join h1 h2)) /\ p h1 /\ ((lift phi) h2) /\ is_emp h2 /\ phi /\ q h1 /\ (h1 == h))
 
let lemma1 (phi:Type0) (p:heap_predicate) (q:heap_predicate)
  :Lemma (requires (phi ==> (p `imp` q)))
         (ensures ((star p (lift phi)) `imp` q))
  = Classical.forall_intro (Classical.move_requires (lemma1_helper phi p q))


let lemma2 (phi:Type0) (p:heap_predicate) (q:heap_predicate)
  :Lemma (requires (phi /\ (p `imp` q)))
         (ensures (p `imp` (star q (lift phi))))
  = assert (forall (h:heap). (p h ==> q h) /\ phi /\ ((lift phi) emp) /\ (disjoint h emp))


let lemma3 (phi:Type0) (p:heap_predicate)
  :Lemma (requires phi)
         (ensures (p `iff` (star p (lift phi)))) 
  = assert (forall (h:heap). phi /\ ((lift phi) emp) /\ (disjoint h emp) /\ (h == (join h emp)))

let lemma4 (p:heap_predicate) (q:heap_predicate) 
  :Lemma (requires True)
         (ensures (star p q) `iff` (star q p))
  = assert (forall (h1:heap) (h2:heap). (disjoint h1 h2) <==> (disjoint h2 h1))

(*
let lemma5_helper (p:heap_predicate) (q:heap_predicate) (r:heap_predicate) (h:heap)
  :Lemma (requires (star p (star q r) h))
         (ensures (star (star p q) r h))
  = assert (exists (h1:heap) (h2:heap) (h3:heap). p h1 /\ q h2 /\ r h3 /\ disjoint h2 h3 /\ (disjoint h1 (join h2 h3)) /\ (h == (join h1 (join h2 h3))) /\ (disjoint h1 h3) /\ (disjoint h3 h1 /\ disjoint h3 h2) /\ disjoint h3 (join h1 h2) /\ (h == (join h3 (join h1 h2))))

*)

let lemma5 (p:heap_predicate) (q:heap_predicate) (r:heap_predicate)
  :Lemma (requires True)
         (ensures (star p (star q r)) `iff` (star (star p q) r))
  = ()
  
  
(*   assert (exists (h1:heap) (h2:heap) (h3:heap). p h1 /\ q h2 /\ r h3 /\ (disjoint h2 h3) /\ (disjoint h1 (join h2 h3)))
*)

let lemma6 (p1:heap_predicate) (p2:heap_predicate) (q1:heap_predicate) (q2:heap_predicate)
  :Lemma (requires ((p1 `imp` p2) /\ (q1 `imp` q2)))
         (ensures ((star p1 q1) `imp` (star p2 q2)))
  = ()

let lemma7 (#a:Type0) (p:heap_predicate) (q:a -> heap_predicate)
  :Lemma (requires True)
         (ensures (star p (exists_x (fun x -> (q x)))) `iff` (exists_x (fun x -> star p (q x))))
  = ()

let lemma8 (#a:Type0) (p:a -> heap_predicate) (q:heap_predicate)
  :Lemma (requires (forall (x:a). (p x) `imp` q))
         (ensures (exists_x p) `imp` q)
  = ()
  
let lemma9 (#a:Type0) (p:heap_predicate) (q:a -> heap_predicate) (v:a)
  :Lemma (requires (p `imp` (q v)))
         (ensures (p `imp` exists_x (q)))
  = ()

type c_pre            = heap_predicate
type c_post (a:Type0) = a -> heap_predicate

type hoare_triple (#a:Type0) (pre:c_pre) (c:command a) (post:c_post a)
  = forall (h0:heap) (h1:heap) (r:a). (pre h0 /\ (c `interpreted_in` h0 == (r, h1))) ==> post r h1

(* all the following rules are conditioned on termination *)
let lemma_return (#a:Type0) (v:a) (pre:c_pre)
  :Lemma (requires True)  
         (ensures (let post :(c_post a) = fun r -> pre `star` (lift (r == v)) in
                   hoare_triple pre (Return v) post))
  = admit ()

let lemma_bind (#a:Type0) (#b:Type0) (c1:command a) (c2:a -> command b)
  (pre:c_pre) (post:c_post b)
  :Lemma (requires (exists (q:c_post a). (hoare_triple pre c1 q /\ (forall (r:a). hoare_triple (q r) (c2 r) post))))
	 (ensures  (hoare_triple pre (Bind c1 c2) post))
  = admit ()

let lemma_loop (#a:Type0) (acc:a) (f:a -> command (loop_result a)) (inv:c_post (loop_result a))
  :Lemma (requires (forall (j:a). hoare_triple (inv (Again j)) (f j) inv))
         (ensures  (hoare_triple (inv (Again acc))
	                         (Loop acc f)
				 (fun r -> inv (Done r))))
  = admit ()

let lemma_fail (#a:Type0)
  :Lemma (requires True)
         (ensures  (hoare_triple (lift False) (Fail #a) (fun _ -> lift False)))
  = admit ()

(* making it let ... = admit () does not verify *)
assume val lemma_consequence (#a:Type0) (c:command a) (p':c_pre) (q':c_post a)
  :Lemma (requires (exists (p:c_pre) (q:c_post a). hoare_triple p c q /\ p' `imp` p /\ (forall (r:a). q r `imp` q' r)))
         (ensures  (hoare_triple p' c q'))

let lemma_read (id:addr) (r:c_post nat)
  :Lemma (requires True)
         (ensures  (hoare_triple (exists_x (fun v -> id `points_to` v `star` (r v)))
	                         (Read id)
				 (fun (x:nat) -> (id `points_to` x) `star` (r x))))
  = admit ()

let lemma_write (id:addr) (v:nat)
  :Lemma (requires True)
         (ensures  (hoare_triple (exists_x (fun v' -> id `points_to` v'))
	                         (Write id v)
				 (fun _ -> id `points_to` v)))
  = admit ()

let lemma_alloc (u:unit)
  :Lemma (requires True)
         (ensures  (hoare_triple is_emp Alloc (fun r -> r `points_to` 0)))
  = admit ()

let lemma_free (id:addr)
  :Lemma (requires True)
         (ensures  (hoare_triple (exists_x (fun v -> id `points_to` v))
	                         (Free id)
				 (fun _ -> is_emp)))
  = admit ()

let lemma_frame_rule (#a:Type0) (c:command a) (p:c_pre) (q:c_post a) (r:c_pre)
  :Lemma (requires hoare_triple p c q)
         (ensures hoare_triple (p `star` r) c (fun x -> (q x) `star` r))
  = admit ()
          
(* get the nice x <-- c1; c2 syntax *)
let bind (#a:Type0) (#b:Type0) (c1:command a) (c2:a -> command b) :command b = Bind c1 c2

let lemma_hoare_triple_imp (#a:Type0) (pre:c_pre) (c:command a) (post:c_post a) (h:heap)
  :Lemma (requires (hoare_triple pre c post) /\ pre h)
         (ensures (let (r, h1) = c `interpreted_in` h in
		   post r h1))
  = ()
  
let example1 (p:ref nat) (h:heap) =
 let (a1, h1) = (Write p 3) `interpreted_in` h in
 h1

let lemma_example1_ok (p:ref nat) (a:nat) (h:heap)
  : Lemma (requires ((p `points_to` a) h))
          (ensures ((p `points_to` 3) (example1 p h)))
  = lemma_write p 3;
    let pre = (exists_x (fun v -> p `points_to` v)) in
    let post = (fun _ -> (p `points_to` 3)) in
    let c = (Write p 3) in
    lemma_hoare_triple_imp pre c post h

let example2 (p:ref nat) (q:ref nat) (h:heap) =
  let (a1, h1) = (Bind (Write p 3) (fun _ -> (Write q 4))) `interpreted_in` h in
  h1

let lemma_example2_ok (p:ref nat) (q:ref nat) (a:nat) (b:nat) (h:heap)
  :Lemma (requires (((p `points_to` a) `star` (q `points_to` b)) h))
         (ensures (((p `points_to` 3) `star` (q `points_to` 4)) (example2 p q h)))
  = lemma_write p 3;
    let pre1 = (exists_x (fun v -> p `points_to` v)) in
    let post1 = (fun x -> p `points_to` 3) in
    let c1 = (Write p 3) in
    let r1 = (q `points_to` b) in
    lemma_frame_rule c1 pre1 post1 r1;
    
    lemma_write q 4;
    let pre2 = (exists_x (fun v -> q `points_to` v)) in
    let post2 = (fun _ -> q `points_to` 4) in
    let c2 = (Write q 4) in
    let r2 = (p `points_to` 3) in
    lemma_frame_rule c2 pre2 post2 r2;

    let pre1' = (pre1 `star` r1) in
    let post1' = (fun x -> (post1 x) `star` r1) in
    let pre2' = (pre2 `star` r2) in
    let post2' = (fun x -> (post2 x) `star` r2) in

    let (_, h1) = (Write p 3) `interpreted_in` h in    
    lemma_consequence (c2) (post1' ()) (post2');     
    lemma_bind (Write p 3) (fun _ -> Write q 4) pre1' post2';

    let (r, h2) = (Bind (Write p 3) (fun _ -> Write q 4)) `interpreted_in` h in
    lemma_hoare_triple_imp pre1' (Bind (Write p 3) (fun _ -> Write q 4)) post2' h;

    let post3 = (fun x -> (p `points_to` 3) `star` (q `points_to` 4)) in
    lemma_consequence (Bind (Write p 3) (fun _ -> Write q 4)) (pre1') (post3);
    lemma_hoare_triple_imp (pre1') (Bind (Write p 3) (fun _ -> Write q 4)) (post3) h


let swap (r1:ref nat) (r2:ref nat) : (command unit) =
  n1 <-- Read r1;
  n2 <-- Read r2;
  _ <-- Write r1 n2;
  Write r2 n1

let lemma_swap_ok (r1:ref nat) (r2:ref nat) (n1:nat) (n2:nat)
  :Lemma (hoare_triple ((r1 `points_to` n1) `star` (r2 `points_to` n2))
                       (swap r1 r2)
		       (fun _ -> (r1 `points_to` n2) `star` (r1 `points_to` n1)))
  = let r_c1 = fun (r:nat) -> lift (r == n1) in
    let r_c2 = fun (r:nat) -> lift (r == n2) in
    
    let c1  = Read r1 in
    let c2  = Read r2 in
    let c3  = fun x -> Write r1 x in
    let c4  = fun x -> Write r2 x in
    let cx4 = fun tmp1 tmp2 _ -> c4 tmp1 in
    let cx3 = fun tmp1 tmp2 -> Bind (c3 tmp2) (cx4 tmp1 tmp2) in
    let cx2 = fun tmp1 -> Bind c2 (cx3 tmp1) in

    lemma_read r1 r_c1;
    let c1_pre  = (exists_x (fun v -> r1 `points_to` v `star` (r_c1 v))) in
    let c1_post = (fun r -> r1 `points_to` r `star` (r_c1 r)) in
    assert(hoare_triple c1_pre (Read r1) c1_post);

    let c2_pre = (exists_x (fun v -> r2 `points_to` v `star` (r_c2 v))) in
    let c1_pre_c2_pre  = c1_pre `star` c2_pre in
    let c1_post_c2_pre = fun r -> (c1_post r) `star` c2_pre in

    lemma_frame_rule c1 c1_pre c1_post c2_pre;
    assert (hoare_triple c1_pre_c2_pre c1 c1_post_c2_pre);

    let aux_cx2 (x1:nat) :Lemma (hoare_triple (c1_post_c2_pre x1) 
                                            (cx2 x1) 
			                    (fun _ -> (r1 `points_to` n2) `star` (r1 `points_to` n1)))
      = lemma_read r2 r_c2;
        let c2_post = (fun x -> r2 `points_to` x `star` (r_c2 x)) in
	assert (hoare_triple c2_pre c2 c2_post);

        lemma_frame_rule c2 c2_pre c2_post (c1_post x1);

        let c2_post_c1_post = fun n -> (c2_post n) `star` (c1_post x1) in
	assert (hoare_triple (c2_pre `star` (c1_post x1)) c2 c2_post_c1_post);

        let aux_cx3 (x2:nat) :Lemma (hoare_triple (c2_post_c1_post x2) (cx3 x1 x2) (fun _ -> (r1 `points_to` n2) `star` (r1 `points_to` n1)))
	  = lemma_write r1 x2;
	    let r1_v  = exists_x (fun v -> r1 `points_to` v) in
	    let r1_x2 = (fun _ -> r1 `points_to` x2) in
	    assert (hoare_triple r1_v (c3 x2) r1_x2);

            lemma_frame_rule (c3 x2) r1_v r1_x2 (r_c1 x1);
	    let r1_v_rc1  = r1_v `star` (r_c1 x1) in
	    let r1_x2_rc1 = fun x -> (r1_x2 x) `star` (r_c1 x1) in
	    assert (hoare_triple r1_v_rc1 (c3 x2) r1_x2_rc1);

            lemma_frame_rule (c3 x2) r1_v_rc1 r1_x2_rc1 (c2_post x2);
	    let r1_v_rc1_c2_post  = r1_v_rc1 `star` (c2_post x2) in
	    let r1_x2_rc1_c2_post = (fun x -> (r1_x2_rc1 x) `star` (c2_post x2)) in
	    assert (hoare_triple r1_v_rc1_c2_post (c3 x2) r1_x2_rc1_c2_post);

            let aux_cx4 (_:unit) : Lemma (hoare_triple (r1_x2_rc1_c2_post ()) 
	                                               (cx4 x1 x2 ()) 
						       (fun _ -> (r1 `points_to` n2) `star` (r2 `points_to` n1)))
	      = lemma_write r2 x1;
                let r2_v  = exists_x (fun v -> r2 `points_to` v) in
		let r2_x1 = (fun _ ->  r2 `points_to` x1) in
		assert (hoare_triple r2_v (c4 x1) r2_x1);

                lemma_frame_rule (c4 x1) (r2_v) (r2_x1) (r_c2 x2);
                let r2_v_rc2  = r2_v `star` (r_c2 x2) in
		let r2_x1_rc2 = fun x -> (r2_x1 x) `star` (r_c2 x2) in
		assert (hoare_triple r2_v_rc2 (c4 x1) r2_x1_rc2);

                lemma_frame_rule (c4 x1) r2_v_rc2 r2_x1_rc2 (r1_x2_rc1 ());
		let r2_v_rc2_r1_x2_rc1  = r2_v_rc2 `star` (r1_x2_rc1 ()) in
		let r2_x1_rc2_r1_x2_rc1 = fun _ -> (r2_x1_rc2 ()) `star` (r1_x2_rc1 ()) in
		assert (hoare_triple r2_v_rc2_r1_x2_rc1 (c4 x1) r2_x1_rc2_r1_x2_rc1);

                lemma4 (r2_v_rc2) (r1_x2_rc1 ());
		let r1_x2_rc1_r2_v_rc2 = (r1_x2_rc1 ()) `star` r2_v_rc2 in
		lemma_consequence (c4 x1) r1_x2_rc1_r2_v_rc2 r2_x1_rc2_r1_x2_rc1;

                assert (hoare_triple (r1_x2_rc1_c2_post ()) (c4 x1) r2_x1_rc2_r1_x2_rc1);       
		
	        let cx4_post = fun _  -> (r2 `points_to` n1) `star` (r1 `points_to` n2) in
		assert (forall (r:unit). r2_x1_rc2_r1_x2_rc1 r `imp` cx4_post r);
	        lemma_consequence (c4 x1) (r1_x2_rc1_c2_post ()) cx4_post;
		assert (hoare_triple (r1_x2_rc1_c2_post()) (c4 x1) cx4_post);
                
                let cx4_post' = fun _ -> (r1 `points_to` n2) `star` (r2 `points_to` n1) in
		lemma4 (r2 `points_to` n1) (r1 `points_to` n2);
		assert (forall (r:unit). cx4_post r `imp` cx4_post' r);
                lemma_consequence (c4 x1) (r1_x2_rc1_c2_post ()) cx4_post';

	(*	assert (hoare_triple (r1_x2_rc1_c2_post ()) (c4 x1) cx4_post'); *)
		admit()
	    in
            admit()
	in
	
        admit()
    in
    
    admit()
(*****)

let example3 (r1:ref nat) (r2:ref nat) :(command unit) =
  n1 <-- Read r1;
  Write r2 n1

let lemma_example3 (r1:ref nat) (r2:ref nat) (n1:nat)
  :Lemma (hoare_triple (r1 `points_to` n1 `star` (exists_x (fun v -> r2 `points_to` v)))
                       (example3 r1 r2)
		       (fun _ -> (r1 `points_to` n1) `star` (r2 `points_to` n1)))
  = let r_c1 = fun (r:nat) -> lift (r == n1) in

    let c1 = Read r1 in
    let c2 = fun n -> Write r2 n in

    lemma_read r1 r_c1;
    let c1_pre  = exists_x (fun v -> r1 `points_to` v `star` (r_c1 v)) in
    let c1_post = fun x -> r1 `points_to` x `star` (r_c1 x) in
    assert (hoare_triple c1_pre (Read r1) c1_post);

    let c1_pre_c2_pre  = c1_pre `star` (exists_x (fun v -> r2 `points_to` v)) in
    let c2_pre  = exists_x (fun v -> r2 `points_to` v) in
    let c1_post_c2_pre = fun x -> (c1_post x) `star` c2_pre in
    
    lemma_frame_rule c1 c1_pre c1_post (exists_x (fun v -> r2 `points_to` v));

    let aux (n1:nat) :Lemma (hoare_triple (c1_post_c2_pre n1) (c2 n1) (fun _ -> exists_x (fun n -> r2 `points_to` n `star` (c1_post n))))
      = lemma_write r2 n1;
        let c2_post = fun _ -> r2 `points_to` n1 in
        assert (hoare_triple c2_pre (c2 n1) c2_post);

        lemma_frame_rule (c2 n1) c2_pre c2_post (c1_post n1);

        assert (hoare_triple (c2_pre `star` (c1_post n1)) (c2 n1) (fun _ -> r2 `points_to` n1 `star` (c1_post n1)));

        lemma4 c2_pre (c1_post n1);
        lemma_consequence (c2 n1) ((c1_post n1) `star` c2_pre) (fun _ -> r2 `points_to` n1 `star` (c1_post n1));

        assert (hoare_triple ((c1_post n1) `star` c2_pre) (c2 n1) (fun _ -> r2 `points_to` n1 `star` (c1_post n1)));

        assert (hoare_triple c1_pre_c2_pre c1 c1_post_c2_pre);
        assert (hoare_triple (c1_post_c2_pre n1) (c2 n1) (fun _ -> r2 `points_to` n1 `star` (c1_post n1)))
    in

    FStar.Classical.forall_intro aux;

    assert (hoare_triple c1_pre_c2_pre c1 c1_post_c2_pre);
    assert (forall (n:nat). hoare_triple (c1_post_c2_pre n) (c2 n) (fun _ -> exists_x (fun n -> r2 `points_to` n `star` (c1_post n))));

    lemma_bind c1 c2 c1_pre_c2_pre (fun _ -> exists_x (fun n -> r2 `points_to` n `star` (c1_post n)));

    assert (hoare_triple c1_pre_c2_pre (Bind c1 c2) (fun _ -> exists_x (fun n -> r2 `points_to` n `star` (c1_post n))));
    assert (hoare_triple c1_pre_c2_pre (Bind c1 c2) (fun _ -> exists_x (fun n -> r2 `points_to` n `star` (r1 `points_to` n `star` (r_c1 n)))));
    
    assert (hoare_triple c1_pre_c2_pre (Bind c1 c2) (fun _ -> (r2 `points_to` n1) `star` (r1 `points_to` n1)));
   
    lemma4 (r2 `points_to` n1) (r1 `points_to` n1);

    let bind_post = (fun _ -> (r1 `points_to` n1) `star` (r2 `points_to` n1)) in
    lemma_consequence (Bind c1 c2) c1_pre_c2_pre bind_post;
    assert (hoare_triple c1_pre_c2_pre (Bind c1 c2) bind_post);

    lemma2 (n1 == n1) (r1 `points_to` n1) (exists_x (fun v -> r1 `points_to` v));
    assert ((r1 `points_to` n1) `imp` (exists_x (fun v -> r1 `points_to` v `star` lift (v == n1))));
    assert ((r1 `points_to` n1) `imp` c1_pre);
    lemma6 (r1 `points_to` n1) (c1_pre) (exists_x (fun v -> r2 `points_to` v))(exists_x (fun v -> r2 `points_to` v));
   
    let bind_pre = (r1 `points_to` n1) `star` (exists_x (fun v -> r2 `points_to` v)) in
    lemma_consequence (Bind c1 c2) bind_pre bind_post
     
