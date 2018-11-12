module Lang

(*
 * An encoding of separation logic in F*.
 * We consider a deeply embedded language of commands and write a wp transformer that computes
 * the wp in separation logic style.
 * Then we manipulate those wps using tactics for finding the frames.
 * Once the wps become "first-order" (after the existentials for heap frames have been solved),
 * they are then sent to Z3.
 *)

open FStar.SL.Heap

type t = UInt64.t
type addr = ref t

let st_wp (a:Type0) = (a -> heap -> Type0) -> heap -> Type0

noeq type command :Type0 -> Type =
  | Return: #a:Type -> v:a -> command a
  | Read  : id:addr -> command t
  | Write : id:addr -> v:t -> command unit
  | Alloc : command addr
  | Bind  : #a:Type0 -> #b:Type0 -> c1:command a -> c2:(a -> command b) -> command b

(*
 * wp computation
 * The initial heap for the commands is just the footprint of the command.
 *)
let rec wpsep_command (#a:Type0) (c:command a) :st_wp a
  = match c with
    | Return #a x ->
      fun p h0 -> (is_emp h0) /\ p x h0  //Return does not touch the heap, so we run it on emp

    | Read r ->
      //Read only needs to touch the reference r in the heap, we run it on the singleton heap
      fun p h0 -> (exists (x:t). h0 == (points_to r x)) /\ (forall (x:t). h0 == (points_to r x) ==> p x h0)

    | Write r y ->
      //Write only needs to touch the reference r in the heap, we run it on the singleton heap
      fun p h0 -> (exists (x:t). h0 == (points_to r x)) /\ (forall (h1:heap). h1 == (points_to r y) ==> p () h1)

    | Alloc ->
      //Alloc also runs on emp
      fun p h0 -> (is_emp h0) /\ (forall (r:addr) (h1:heap). (h1 == points_to r 0uL) /\ (get_next_addr h1 == get_next_addr h0 + 1) ==> p r h1)
    | Bind #a #b c1 c2 ->
      (*
       * We are running (c1; c2) on an input heap h3.
       * In the separation logic style, we will partition the heaps and run commands on the partitions.
       * The way we are going to do it is, we first partition h3 into two disjoint heaps h2' and h2'',
       * and run c1 on h2', let's say the output heap of c1 is then h1.
       * We now join h1 with h2'' (the second partition of the original heap), and partition the resulting heap
       * again into h1' and h1'', where c2 runs on h1' resulting in h2.
       * The final heap is then join of h2 and h1''.
       *)
      FStar.Classical.forall_intro (FStar.WellFounded.axiom1 #a #(command b) c2);
      fun p h3 -> exists (h2':heap) (h2'':heap). h3 == join_tot h2' h2'' /\
     (wpsep_command c1) (fun x h1 -> exists (h1':heap) (h1'':heap). (join_tot h1 h2'') == (join_tot h1' h1'') /\
     (wpsep_command (c2 x)) (fun y h2 -> p y (join_tot h2 h1'')) h1') h2'

(*
 * The wp that we compute for a command only talks about the footprint of the command.
 * So, we need to partition the global heap as well, and run the command on its partition.
 *
 * Given the input heap h0, we partition it into h0' and h0'', run the command on h0', resulting in h1',
 * and return the final heap as join h1' h0''.
 *)
let lift_wpsep (#a:Type0) (wp_sep:st_wp a) :st_wp a
  = fun p h0 -> exists (h0':heap) (h0'':heap). h0 == (join_tot h0' h0'') /\ wp_sep (fun x h1' -> p x (join_tot h1' h0'')) h0'

(*
 * TODO: these lemmas should go to the heap modules.
 *)
let lemma_read_write (phi:heap -> heap -> prop) (r:addr) (h:heap{contains h r})
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

let lemma_eq_implies_intro' (phi:heap -> prop) (phi':heap -> Type0) (x:heap)
  :Lemma (requires phi' x ==> phi x)
         (ensures (forall (y:heap). (y == x) /\ phi' y ==> phi y))
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

