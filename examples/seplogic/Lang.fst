module Lang

open FStar.SL.ST
open FStar.SL.Heap

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
      fun p h0 -> (is_emp h0) /\ p x h0

    | Bind #a #b c1 c2 ->
      FStar.Classical.forall_intro (FStar.WellFounded.axiom1 #a #(command b) c2);
      fun p h3 -> exists (h2':heap) (h2'':heap). h3 == join_tot h2' h2'' /\
     (wpsep_command c1) (fun x h1 -> exists (h1':heap) (h1'':heap). (join_tot h1 h2'') == (join_tot h1' h1'') /\
     (wpsep_command (c2 x)) (fun y h2 -> p y (join_tot h2 h1'')) h1') h2'

    | Read r ->
      fun p h0 -> (exists (x:t). h0 == (points_to r x)) /\ (forall (x:t). h0 == (points_to r x) ==> p x h0)

    | Write r y ->
      fun p h0 -> (exists (x:t). h0 == (points_to r x)) /\ (forall (h1:heap). h1 == (points_to r y) ==> p () h1)

    | Alloc ->
      fun p h0 -> (is_emp h0) /\ (forall (r:addr) (h1:heap). (h1 == points_to r 0uL) ==> p r h1)

let lift_wpsep (#a:Type0) (wp_sep:st_wp a) :st_wp a
  = fun p h0 -> exists (h0':heap) (h0'':heap). h0 == (join_tot h0' h0'') /\ wp_sep (fun x h1' -> p x (join_tot h1' h0'')) h0'

let lemma_read_write (phi:heap -> heap -> prop) (r:addr) (h:heap{h `contains` r })
  :Lemma (requires phi (restrict h r) (minus h r))
         (ensures (exists (h':heap) (h'':heap). (h == join_tot h' h'') /\ 
	          ((exists x. h' == (points_to r x)) /\ phi h' h'')))
  = ()

let lemma_alloc_return (phi:heap -> heap -> prop) (h:heap)
  :Lemma (requires (phi (emp_with_next_addr (get_next_addr h)) h))
         (ensures (exists (h':heap) (h'':heap). h == join_tot h' h'' /\ ((is_emp h') /\ phi h' h'')))
  = ()

let lemma_bind (phi:heap -> heap -> heap -> heap -> prop) (h:heap)
  :Lemma (requires (exists (h2':heap) (h2'':heap). h == join_tot h2' h2'' /\
                                              phi h (emp_with_next_addr (get_next_addr h)) h2' h2''))
         (ensures (exists (h1':heap) (h1'':heap). h == join_tot h1' h1'' /\
	          (exists (h2':heap) (h2'':heap). h1' == join_tot h2' h2'' /\
		                             phi h1' h1'' h2' h2'')))
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
  
