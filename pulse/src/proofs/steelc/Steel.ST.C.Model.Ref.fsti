module Steel.ST.C.Model.Ref
open Steel.ST.Util

include Steel.C.Model.Ref.Base

open FStar.FunctionalExtensionality
open Steel.C.Model.PCM
open Steel.C.Model.Connection

(** Allocate a reference containing value x. *)
val ref_alloc
  (#a:Type0) (p: pcm a) (x: a)
: ST (ref a p)
    emp
    (fun r -> r `pts_to` x)
    (requires p_refine p x)
    (ensures fun r -> freeable r)

(** Free a "base" (freeable) reference containing a "whole" (p_refine) value x. *)
val ref_free
  (#a #b:Type0) (#p: pcm b) (#x: Ghost.erased b) (r: ref a p)
: ST unit
    (r `pts_to` x)
    (fun _ -> emp)
    (requires p_refine p x /\ freeable r)
    (ensures fun _ -> True)


(** Take a pointer to a "substructure" of a reference. *)
val gfocus (#inames: _) (#p: pcm 'b) (r: ref 'a p)
  (#q: pcm 'c)
  (l: connection p q) (s: Ghost.erased 'b) (x: Ghost.erased 'c)
: STGhost unit inames
    (r `pts_to` s)
    (fun _ -> ref_focus r l `pts_to` x)
    (Ghost.reveal s == l.conn_small_to_large.morph x)
    (fun _ -> True)

val focus (#opened: _) (#p: pcm 'b) (r: ref 'a p)
  (#q: pcm 'c)
  (l: connection p q) (s: Ghost.erased 'b) (x: Ghost.erased 'c)
: STAtomicBase (ref 'a q)
    false opened Unobservable
    (r `pts_to` s)
    (fun r' -> r' `pts_to` x)
    (Ghost.reveal s == l.conn_small_to_large.morph x)
    (fun r' -> r' == ref_focus r l)

module M = Steel.Memory

(** Inverse of focus. *)
val unfocus (#opened:M.inames)
  (#p: pcm 'b)
  (#q: pcm 'c)
  (r: ref 'a q) (r': ref 'a p)
  (l: connection p q) (x: Ghost.erased 'c)
: STGhost unit opened
    (r `pts_to` x)
    (fun _ -> r' `pts_to` l.conn_small_to_large.morph x)
    (requires r == ref_focus r' l)
    (ensures fun _ -> True)

(** Split the permissions on a reference into two halves. *)
val split (#inames: _) (#a:Type) (#b:Type) (#p: pcm b) (r: ref a p) (xy x y: Ghost.erased b)
: STGhost unit inames
    (r `pts_to` xy)
    (fun _ -> (r `pts_to` x) `star` (r `pts_to` y))
    (composable p x y /\ xy == Ghost.hide (op p x y))
    (fun _ -> True)

(** Inverse of split. *)
val gather (#inames: _) (#a:Type) (#b:Type) (#p: pcm b) (r: ref a p) (x y: Ghost.erased b)
: STGhostT (_:unit{composable p x y}) inames
    ((r `pts_to` x) `star` (r `pts_to` y))
    (fun _ -> r `pts_to` op p x y)

(** Read a PCM carrier value. *)
val ref_read
  (#a:Type) (#b:Type) (#p: pcm b) (#x: Ghost.erased b) (r: ref a p)
: ST b
    (r `pts_to` x)
    (fun _ -> r `pts_to` x)
    (requires True)
    (ensures fun x' -> compatible p x x')

(** Write a PCM carrier value. *)
val ref_upd
  (#a:Type) (#b:Type) (#p: pcm b)
  (r: ref a p) (x: Ghost.erased b { ~ (Ghost.reveal x == one p) }) (y: Ghost.erased b) (f: frame_preserving_upd p x y)
: STT unit (r `pts_to` x) (fun _ -> r `pts_to` y)
