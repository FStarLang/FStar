module Steel.C.Model.Ref.Base
open FStar.FunctionalExtensionality
open Steel.C.Model.PCM
open Steel.C.Model.Connection
open Steel.Effect.Common

(** A [ptr a b] is a (maybe null) pointer to some value of type b inside of a "base object" of type a. *)
val ptr (a: Type u#0) (#b: Type u#b) (p: pcm b) : Tot (Type u#b)

val null (a: Type u#0) (#b: Type u#b) (p: pcm b) : Tot (ptr a p)

val ptr_is_null (#a: Type u#0) (#b: Type u#b) (#p: pcm b) (r: ptr a p) : Ghost bool (requires True) (ensures (fun res -> res == true <==> r == null a p))

let refine (a: Type) (p: (a -> prop)) : Tot Type =
  (x: a { p x })

let not_null
  (#a: Type u#0) (#b: Type u#b) (#p: pcm b) (r: ptr a p)
: Tot prop
= ptr_is_null r == false

(** A [ref a #b q] is a [ref' a b] where the PCM inside the ref' is forced to be q *)
let ref (a: Type u#0) (#b: Type u#b) (q: pcm b) : Type u#b =
  refine (ptr a q) (not_null #a #b #q)

(** Given a reference to an element of PCM p and a connection l from p to q,
    [ref_focus r l] is a reference to an element of q. The intuition is that
    q represents a "part of" p (e.g. a struct field, union case, or array slice). *)
val ref_focus
  (#a:Type) (#b:Type) (#c:Type) (#p: pcm b)
  (r: ref a p) (#q: pcm c) (l: connection p q)
: GTot (ref a q)

val ref_focus_id
  (#a:Type) (#b:Type) (#p: pcm b)
  (r: ref a p)
: Lemma
  (ref_focus r (connection_id _) == r)

val ref_focus_comp (#p: pcm 'a) (#q: pcm 'b) (#s: pcm 'c) (r: ref 'd p)
  (l: connection p q) (m: connection q s)
: Lemma (ref_focus (ref_focus r l) m == ref_focus r (l `connection_compose` m))
  [SMTPatOr [
    [SMTPat (ref_focus (ref_focus r l) m)]; 
    [SMTPat (ref_focus r (l `connection_compose` m))]]]

val freeable
  (#a: Type0) (#b:Type0) (#p: pcm b) (r: ref a p)
: Tot prop

(** r points to PCM carrier value v *)
val pts_to
  (#a: Type u#0) (#b: Type u#b) (#p: pcm b)
  (r: ref a p) ([@@@smt_fallback] v: b)
: vprop

(** Construct a write from a frame-preserving update. *)
val base_fpu
  (#a: Type)
  (p: pcm a)
  (x: Ghost.erased a)
  (y: a)
: Pure (frame_preserving_upd p x y)
  (requires (exclusive p x /\ p_refine p y))
  (ensures (fun _ -> True))
