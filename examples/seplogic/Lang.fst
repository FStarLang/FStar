module Lang

open FStar.ST
open FStar.SepLogic.Heap

noeq type command :Type0 -> Type =
  | Return: #a:Type -> v:a -> command a
  | Bind  : #a:Type0 -> #b:Type0 -> c1:command a -> c2:(a -> command b) -> command b
  | Read  : id:addr -> command int
  | Write : id:addr -> v:int -> command unit
  | Alloc : command addr

let rec wpsep_command (#a:Type0) (c:command a) :st_wp a
  = match c with
    | Return #a x ->
      fun p h0 -> (h0 == emp) /\ p x h0

    | Bind #a #b c1 c2 ->
      FStar.Classical.forall_intro (FStar.WellFounded.axiom1 #a #(command b) c2);
      fun p h3 -> exists (h2':heap) (h2'':heap). h3 == h2' `join` h2'' /\
     (wpsep_command c1) (fun x h1 -> exists (h1':heap) (h1'':heap). (h1 `join` h2'') == (h1' `join` h1'') /\
     (wpsep_command (c2 x)) (fun y h2 -> p y (h2 `join` h1'')) h1') h2'

    | Read r ->
      fun p h0 -> (exists (x:int). h0 == (r `points_to` x)) /\ (forall (x:int). h0 == (r `points_to` x) ==> p x h0)

    | Write r y ->
      fun p h0 -> (exists (x:int). h0 == (r `points_to` x)) /\ (forall (h1:heap). h1 == (r `points_to` y) ==> p () h1)

    | Alloc ->
      fun p h0 -> (h0 == emp) /\ (forall (r:addr) (h1:heap). (h1 == r `points_to` 0) ==> p r h1)

let lift_wpsep (#a:Type0) (wp_sep:st_wp a) :st_wp a
  = fun p h0 -> exists (h0':heap) (h0'':heap). h0 == (h0' `join` h0'') /\
                                       wp_sep (fun x h1' -> p x (h1' `join` h0'')) h0'

let lemma_read_write (phi:heap -> heap -> prop) (r:addr) (h:heap)
  :Lemma (requires phi (h `restrict` r) (h `minus` r))
         (ensures (exists (h':heap) (h'':heap). h == h' `join` h'' /\
	                                  ((exists x. h' == (r `points_to` x)) /\ phi h' h'')))
  = ()

let lemma_alloc_return (phi:heap -> heap -> prop) (h:heap)
  :Lemma (requires (phi emp h))
         (ensures (exists (h':heap) (h'':heap). h == h' `join` h'' /\ ((h' == emp) /\ phi h' h'')))
  = ()

let lemma_destruct_exists_subheaps (phi:heap -> heap -> heap -> heap -> prop) (h:heap)
  :Lemma (requires (exists (h2':heap) (h2'':heap). h == h2' `join` h2'' /\
                                              phi h emp h2' h2''))
         (ensures (exists (h1':heap) (h1'':heap). h == h1' `join` h1'' /\
	          (exists (h2':heap) (h2'':heap). h1' == h2' `join` h2'' /\
		                             phi h1' h1'' h2' h2'')))
  = ()





