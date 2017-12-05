module Lang

open FStar.ST
open FStar.Heap

type t = UInt64.t
type addr = ref t

noeq type command :Type0 -> Type =
  | Return: #a:Type -> v:a -> command a
  | Bind  : #a:Type0 -> #b:Type0 -> c1:command a -> c2:(a -> command b) -> command b
  | Read  : id:addr -> command t
  | Write : id:addr -> v:t -> command unit
  | Alloc : command addr

let rec wpsep_command (#a:Type0) (c:command a) :st_wp a
  = match c with
    | Return #a x ->
      fun p h0 -> (h0 == emp) /\ p x h0

    | Bind #a #b c1 c2 ->
      FStar.Classical.forall_intro (FStar.WellFounded.axiom1 #a #(command b) c2);
      fun p h3 -> exists (h2':heap) (h2'':heap). disjoint h2' h2'' /\ h3 == h2' `join` h2'' /\
     (wpsep_command c1) (fun x h1 -> exists (h1':heap) (h1'':heap). disjoint h1' h1'' /\ disjoint h1 h2'' /\ (h1 `join` h2'') == (h1' `join` h1'') /\
     (wpsep_command (c2 x)) (fun y h2 -> disjoint h2 h1'' /\ p y (h2 `join` h1'')) h1') h2'

    | Read r ->
      fun p h0 -> (exists (x:t). h0 == (r `points_to` x)) /\ (forall (x:t). h0 == (r `points_to` x) ==> p x h0)

    | Write r y ->
      fun p h0 -> (exists (x:t). h0 == (r `points_to` x)) /\ (forall (h1:heap). h1 == (r `points_to` y) ==> p () h1)

    | Alloc ->
      fun p h0 -> (h0 == emp) /\ (forall (r:addr) (h1:heap). (h1 == r `points_to` 0uL) ==> p r h1)

let lift_wpsep (#a:Type0) (wp_sep:st_wp a) :st_wp a
  = fun p h0 -> exists (h0':heap) (h0'':heap). disjoint h0' h0'' /\ h0 == (h0' `join` h0'') /\
                                       wp_sep (fun x h1' -> disjoint h1' h0'' /\ p x (h1' `join` h0'')) h0'

let lemma_read_write (phi:heap -> heap -> prop) (r:addr) (h:heap) (p1:squash (h `contains` r))
  :Lemma (requires phi (h `restrict` r) (h `minus` r))
         (ensures (exists (h':heap) (h'':heap). disjoint h' h'' /\ h == h' `join` h'' /\
	                                  ((exists x. h' == (r `points_to` x)) /\ phi h' h'')))
  = ()

let lemma_alloc_return (phi:heap -> heap -> prop) (h:heap)
  :Lemma (requires (phi emp h))
         (ensures (exists (h':heap) (h'':heap). disjoint h' h'' /\ h == h' `join` h'' /\ ((h' == emp) /\ phi h' h'')))
  = ()

let lemma_bind (phi:heap -> heap -> heap -> heap -> prop) (h:heap)
  :Lemma (requires (exists (h2':heap) (h2'':heap). disjoint h2' h2'' /\ h == h2' `join` h2'' /\
                                              phi h emp h2' h2''))
         (ensures (exists (h1':heap) (h1'':heap). disjoint h1' h1'' /\ h == h1' `join` h1'' /\
	          (exists (h2':heap) (h2'':heap). disjoint h2' h2'' /\ h1' == h2' `join` h2'' /\
		                             phi h1' h1'' h2' h2'')))
  = ()

let lemma_extract_disjoint 
  (phi:heap -> heap -> heap -> heap ->  prop) (h2':heap) (h2'':heap) (p1:squash (disjoint h2' h2''))
  :Lemma (requires (exists (h1':heap) (h1'':heap). disjoint h1' h1'' /\ join h2' h2'' == join h1' h1'' /\ phi h1' h1'' h2' h2''))
         (ensures (exists (h1':heap) (h1'':heap). disjoint h1' h1'' /\ disjoint h2' h2'' /\ join h2' h2'' == join h1' h1'' /\ phi h1' h1'' h2' h2''))
  = ()

let lemma_eq_implies_intro (phi:heap -> prop) (x:heap)
  :Lemma (requires phi x)
         (ensures (forall (y:heap). (y == x) ==> phi y))
  = ()

let lemma_addr_not_eq_refl (r1:addr) (r2:addr)
  :Lemma (requires addr_of r1 <> addr_of r2)
         (ensures addr_of r2 <> addr_of r1)
  = ()

let lemma_refl (#a:Type) 
  :Lemma (requires True)
         (ensures a <==> a) 
  = ()

let lemma_impl_l_cong (#a:Type) (#b:Type) (#c:Type) (p1:squash (a <==> b)) (p2:squash (b ==> c)) 
  :Lemma (requires True)
         (ensures a ==> c) 
  = ()

let lemma_eq_l_cong (a:heap) (b:heap) (#c:Type) (u:heap) (p1:squash (a == u)) (p2:squash (u == b ==> c))
  :Lemma (requires True)
         (ensures a == b ==> c)
  = ()

let lemma_eq_cong (h:heap) (r:addr) (n:t) (u:t) (p1:squash (sel h r == u)) (p2:squash (u == n))
  :Lemma (requires True)
         (ensures sel h r == n)
  = ()
  
