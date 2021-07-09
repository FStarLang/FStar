module AggregateRef

open FStar.PCM
open FStar.PCM.Extras
open Lens
module P = FStar.PCM
module A = Steel.Effect.Atomic

open Steel.Effect

val ref (a:Type u#1) (#b:Type) (q: refined_one_pcm b): Type

val pts_to
  (#a: Type u#1) (#b: Type u#b) (#p: refined_one_pcm b)
  (r: ref a p) ([@@@smt_fallback] v: Ghost.erased b)
: vprop

(** (ref_refine r new_re) points to x
    if r points to x and x satisfies refinement re *)
val ref_refine (#a:Type) (#b:Type) (#p:refined_one_pcm b)
  (r: ref a p) (new_re: pcm_refinement p)
: ref a (refined_pcm new_re)

(** (ref_focus r l) points to x if r points to (put l x one) *)
val ref_focus
  (#a:Type) (#b:Type) (#c:Type) (#p: refined_one_pcm b)
  (r: ref a p) (#q: refined_one_pcm c) (l: pcm_lens p q)
: ref a q

(** Fundamental operations on references *)

val split (#a:Type) (#b:Type) (#p: refined_one_pcm b) (r: ref a p) (xy x y: Ghost.erased b)
: Steel unit
    (r `pts_to` xy)
    (fun _ -> (r `pts_to` x) `star` (r `pts_to` y))
    (fun _ -> composable p x y /\ xy == Ghost.hide (op p x y))
    (fun _ _ _ -> True)

val gather (#a:Type) (#b:Type) (#p: refined_one_pcm b) (r: ref a p) (x y: Ghost.erased b)
: SteelT (_:unit{composable p x y})
    ((r `pts_to` x) `star` (r `pts_to` y))
    (fun _ -> r `pts_to` op p x y)

val addr_of_lens
  (#a:Type) (#b:Type) (#c:Type) (#p: refined_one_pcm b) (#q: refined_one_pcm c)
  (r: ref a p) (l: pcm_lens p q)
  (x: Ghost.erased b)
: Steel (ref a q)
    (r `pts_to` x)
    (fun s ->
      (r `pts_to` put l (one q) x) `star` 
      (s `pts_to` get l x))
    (requires fun _ -> True)
    (ensures fun _ r' _ -> r' == ref_focus r l)

val un_addr_of_lens
  (#a:Type) (#b:Type) (#c:Type) (#p: refined_one_pcm b) (#q: refined_one_pcm c)
  (r': ref a q) (r: ref a p) (l: pcm_lens p q)
  (x: Ghost.erased b) (y: Ghost.erased c)
: Steel unit
    ((r `pts_to` x) `star` (r' `pts_to` y))
    (fun s -> r `pts_to` put l y x)
    (requires fun _ -> r' == ref_focus r l /\ get l x == one q)
    (ensures fun _ _ _ -> True)

(** Generic read.

    Without the precondition ~ (x == one), it would be possible to read
    a completely uninformative value from a reference. This is safe
    from the model's standpoint (we can't learn anything from this value),
    but would extract to a potentially unsafe pointer dereference in C.

    For example, here's a use-after-free:
        {p `pts_to` x}
      split
        {(p `pts_to` x) `star` (p `pts_to` one)}
      free p
        {p `pts_to` one}
      read p

    Even with ~ (x == one), it's possible that x represents partial information
    about the value at r (for example, a tuple (one, z) representing a struct
    with permission to read/write from the second field only). But we should be
    safe as long as the carrier types of the PCMs involved are abstract.
    
    For example, suppose
      thread 1 has (p `pts_to` (y, one))
      thread 2 has (p `pts_to` (one, z))
    and thread 1 writes to p->fst while thread 2 performs the read (v, w) = *p.
    
    In this situation, we can't allow thread 2 to dereference (&q.fst),
    as then it'd be reading from a location while thread 1 is writing to it.

    Thread 2 can construct the pointer (&q.fst) just fine, but in
    order to dereference it, it needs to call ref_read, and ref_read
    requires that (&q.fst) point to a non-unit value (i.e., that ~ (v == one)).
    
    If v's type is suitably abstract, so that it's not possible to
    test v against the unit of its corresponding PCM, then there's no
    way to prove this precondition and we are safe from reading v
    as thread 1 is writing to it. *)
val ref_read
  (#a:Type) (#b:Type) (#p: refined_one_pcm b) (#x: Ghost.erased b) (r: ref a p)
: Steel b
    (r `pts_to` x)
    (fun _ -> r `pts_to` x)
    (requires fun _ -> ~ (Ghost.reveal x == one p))
    (ensures fun _ x' _ -> compatible p x x')

val ref_upd
  (#a:Type) (#b:Type) (#p: refined_one_pcm b)
  (r: ref a p) (x y: Ghost.erased b) (f: (b -> b){frame_pres p f x y})
: SteelT unit (r `pts_to` x) (fun _ -> r `pts_to` y)

(* TODO move to FStar.PCM.fst? *)
let whole_value (p: pcm 'a) (x: 'a) =
  p.refine x /\
  (forall (y:'a{composable p x y}).{:pattern op p y x} op p y x == x)

let valid_write (p:pcm 'a) x y =
  whole_value p x /\ whole_value p y /\
  (forall (frame:'a). composable p x frame ==> composable p y frame)

val ref_write
  (#a:Type) (#b:Type) (#p: refined_one_pcm b)
  (r: ref a p) (#x: Ghost.erased b) (y: b{valid_write p x y})
: SteelT unit (r `pts_to` x) (fun _ -> r `pts_to` y)
