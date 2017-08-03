module Lang

open FStar.Seq
open FStar.Set
open FStar.Classical

open FStar.ST
open FStar.Heap  //this order of opening the modules is important, we want ref from FStar.Heap

#set-options "--lax"

type addr = ref int

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
  | Read  : id:addr -> command int
  | Write : id:addr -> v:int -> command unit
  | Alloc : command addr
  | Free  : id:addr -> command unit

(*
 * a bit hacky, since a program may not termiinte
 *)
assume val interpreted_in (#a:Type0) (c:command a) (h:heap) :Tot (a * heap)

type heap_predicate = heap -> Type0

let is_emp (h:heap) : Type0 = (h == emp)

let points_to (id:addr) (n:int) (h:heap) : Type0 =
  (h == (restrict h (Set.singleton (addr_of id)))) /\ (sel h id == n)

let lift (phi:Type0) (h:heap) :Type0 = phi /\ is_emp h

let exists_x (#a:Type0) (pred:a -> heap_predicate) (h:heap) :Type0
  = exists (x:a). pred x h

let star (p:heap_predicate) (q:heap_predicate) (h:heap) :Type0
  = exists (h1:heap) (h2:heap). disjoint h1 h2 /\ (h == (join h1 h2)) /\ p h1 /\ q h2

let iff (p:heap_predicate) (q:heap_predicate) :Type0 = forall (h:heap). p h <==> q h

let imp (p:heap_predicate) (q:heap_predicate) :Type0 = forall (h:heap). p h ==> q h

type c_pre            = heap_predicate
type c_post (a:Type0) = a -> heap_predicate

type hoare_triple (#a:Type0) (pre:c_pre) (c:command a) (post:c_post a)
  = forall (h0:heap) (h1:heap) (r:a). (pre h0 /\ (c `interpreted_in` h0 == (r, h1))) ==> post r h1

let rec wp_command (#a:Type0) (c:command a) (p:st_post a) (h:heap) :Type0
  = match c with
    | Return #a x      -> p x h
    | Bind #a #b c1 c2 ->
      FStar.Classical.forall_intro (FStar.WellFounded.axiom1 #a #(command b) c2);
      (wp_command c1) (fun x h1 -> (wp_command (c2 x)) p h1) h
    | Loop #_ _ _      -> False
    | Fail #_          -> True
    | Read r           -> p (sel h r) h
    | Write r x        -> p () (upd h r x)
    | Alloc            ->
      let (r, h) :(ref int * heap) = Heap.alloc (Heap.trivial_preorder int) h 0 false in p r h
    | Free r           -> False

(* get the nice x <-- c1; c2 syntax *)
let bind (#a:Type0) (#b:Type0) (c1:command a) (c2:a -> command b) :command b = Bind c1 c2

let distinct_and_contained (r1:addr) (r2:addr) (h:heap)
  = addr_of r1 <> addr_of r2 /\ h `contains` r1 /\ h `contains` r2

let c1 (r1:addr) (n1:int)
  :command int
  = Write r1 n1;; n <-- Read r1; Return n
  
#reset-options

let foo (r1:addr) (n1:int)
        (r2:addr) (n2:int)
        (h:heap{distinct_and_contained r1 r2 h})
  =  let p1  :st_post int = fun n h -> sel h r1 == n1 in
     admit ();
     assert_norm ((wp_command (c1 r1 n1)) (normalize_term p1) h)
