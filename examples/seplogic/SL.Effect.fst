module SL.Effect

open SepLogic.Heap


(*** begin heap interface ***)

(*
 * this is all the heap interface we need so far
 *)
assume val memory: Type u#1
assume val defined: memory -> Type0

assume val emp: memory
assume val ref (a:Type0): Type0

(* operations on memories and refs *)
assume val addr_of: #a:Type0 -> ref a -> Tot nat
assume val ( |> ): #a:Type0 -> r:ref a -> x:a -> Tot memory
assume val ( <*> ): m0:memory -> m1:memory -> Tot memory

(* lemmas *)
assume val lemma_join_is_commutative (m0 m1:memory)
  :Lemma (requires True) (ensures ((m0 <*> m1) == (m1 <*> m0)))
         [SMTPat (m0 <*> m1); 
          SMTPat (m1 <*> m0)]
assume val lemma_join_is_associative (m0 m1 m2:memory)
  :Lemma (requires True) (ensures ((m0 <*> (m1 <*> m2)) == ((m0 <*> m1) <*> m2)))
         [SMTPatOr [[SMTPat ((m0 <*> (m1 <*> m2)))];
	            [SMTPat ((m0 <*> m1) <*> m2)]]]
assume val lemma_emp_is_join_unit (m:memory)
  :Lemma (requires True) (ensures ((m <*> emp) == m))
         [SMTPat (m <*> emp)]
assume val lemma_emp_is_join_unit' (m:memory)
  :Lemma (requires True) (ensures ((emp <*> m) == m))
         [SMTPat (emp <*> m)]

(* addrs_in *)
assume val addrs_in (m:memory) :Set.set nat

assume val lemma_addrs_in_emp (u:unit) :Lemma (Set.equal (addrs_in emp) (Set.empty))
assume Addrs_in_emp_axiom: Set.equal (addrs_in emp) (Set.empty)
assume val lemma_addrs_in_points_to (#a:Type) (r:ref a) (x:a)
  :Lemma (requires True) (ensures (Set.equal (addrs_in (r |> x)) (Set.singleton (addr_of r))))
         [SMTPat (addrs_in (r |> x))]
assume val lemma_addrs_in_join (m0 m1:memory)
  :Lemma (requires (defined (m0 <*> m1)))
         (ensures  (Set.equal (addrs_in (m0 <*> m1)) (Set.union (addrs_in m0) (addrs_in m1))))
	 [SMTPat (addrs_in (m0 <*> m1))]

(* definedness *)
assume val lemma_defined_emp (u:unit) :Lemma (defined emp)
assume Defined_emp_axiom: defined emp
assume val lemma_defined_points_to (#a:Type) (r:ref a) (x:a)
  :Lemma (requires True) (ensures (defined (r |> x)))
         [SMTPat (defined (r |> x))]
assume val lemma_defined_join (m0 m1:memory)
  :Lemma (requires True)
         (ensures  (defined (m0 <*> m1) <==> (defined m0 /\ defined m1 /\ Set.disjoint (addrs_in m0) (addrs_in m1))))
	 [SMTPat (defined (m0 <*> m1))]

(*let lemma_bad_disjoint_without_pat_on_a_quantifier (a:eqtype) (s1 s2:Set.set a)
  :Lemma (requires (Set.disjoint s1 s2)) (ensures (forall x. Set.mem x s1 ==> ~ (Set.mem x s2)))
         [SMTPat (Set.disjoint s1 s2)]
  = ()*)


(*** end heap interface ***)


let pre = memory -> Type0
let post (a:Type) = a -> memory -> Type0
let st_wp (a:Type) = post a -> pre

unfold let return_wp (a:Type) (x:a) :st_wp a = 
  fun post m0 -> m0 == emp /\ post x m0

unfold let frame_wp (#a:Type) (wp:st_wp a) (post:memory -> post a) (m:memory) =
  exists (m0 m1:memory). defined (m0 <*> m1) /\ m == (m0 <*> m1) /\ wp (post m1) m0

unfold let frame_post (#a:Type) (p:post a) (m0:memory) :post a =
  fun x m1 -> defined (m1 <*> m0) /\ p x (m1 <*> m0)  //m1 is the frame

unfold let bind_wp (r:range) (a:Type) (b:Type) (wp1:st_wp a) (wp2:a -> st_wp b)
  :st_wp b
  = fun post m0 ->
    frame_wp wp1 (frame_post (fun x m1 -> frame_wp (wp2 x) (frame_post post) m1)) m0

unfold  let st_if_then_else (a:Type) (p:Type) (wp_then:st_wp a) (wp_else:st_wp a) (post:post a) (m0:memory) =
  l_ITE p (wp_then post m0) (wp_else post m0)

unfold  let st_ite_wp (a:Type) (wp:st_wp a) (p:post a) (m0:memory) =
  forall (k:post a).
    (forall (x:a) (m:memory).{:pattern (guard_free (k x m))} p x m ==> k x m)
    ==> wp k m0

unfold  let st_stronger (a:Type) (wp1:st_wp a) (wp2:st_wp a) =
  forall (p:post a) (m:memory). wp1 p m ==> wp2 p m

unfold let st_close_wp (a:Type) (b:Type) (wp:(b -> GTot (st_wp a))) (p:post a) (m:memory) =
  forall (b:b). wp b p m

unfold  let st_assert_p (a:Type) (p:Type) (wp:st_wp a) (q:post a) (m:memory) =
  p /\ wp q m

unfold  let st_assume_p (a:Type) (p:Type) (wp:st_wp a) (q:post a) (m:memory) =
  p ==> wp q m

unfold  let st_null_wp (a:Type) (p:post a) (m:memory) =
  forall (x:a) (m:memory). p x m

unfold let st_trivial (a:Type) (wp:st_wp a) =
  forall m0. wp (fun _ _ -> True) m0
      
new_effect {
  STATE : result:Type -> wp:st_wp result -> Effect
  with return_wp    = return_wp
     ; bind_wp      = bind_wp
     ; if_then_else = st_if_then_else
     ; ite_wp       = st_ite_wp
     ; stronger     = st_stronger
     ; close_wp     = st_close_wp
     ; assert_p     = st_assert_p
     ; assume_p     = st_assume_p
     ; null_wp      = st_null_wp
     ; trivial      = st_trivial
}

unfold let lift_div_st (a:Type) (wp:pure_wp a) (p:post a) (m:memory) = wp (fun a -> p a emp)
sub_effect DIV ~> STATE = lift_div_st

assume
val ( ! ) (#a:Type) (r:ref a)
  :STATE a (fun post m0 -> exists (x:a). m0 == (r |> x) /\ post x m0)

assume
val ( := ) (#a:Type) (r:ref a) (v:a)
  :STATE unit (fun post m0 -> exists (x:a). m0 == (r |> x) /\ post () (r |> v))
