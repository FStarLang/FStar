module Domains

open Pulse.Main
open Pulse.Steel.Wrapper
open Steel.Effect.Common

module R = Steel.ST.Reference
module HR = Steel.ST.HigherReference
open Steel.Memory
open Steel.ST.Effect
open Steel.ST.Util

module Lock = Steel.ST.SpinLock

val unit_emp_stt_pure_pure (a:Type0) (p: a -> prop): Type0
//val domain : a:Type0 -> (a -> vprop) -> Type0
val task_queue: Type u#1

val inv_task_queue
  (q: HR.ref task_queue) // the task queue
  (c: R.ref int) // a counter of how many tasks are currently being performed
  : vprop

//= unit -> stt a emp (fun x -> pure (p x))

val pure_handler (#a:Type0) (post: a -> prop): Type0

val spawn_emp
  (#a:Type0)
  (#q: HR.ref task_queue)
  (#c: R.ref int)
  (post: (a -> prop))
  (l: Lock.lock (inv_task_queue q c))
  (f : unit_emp_stt_pure_pure a post)
: stt (pure_handler post) emp (fun _ -> emp)

val join_emp
  (#a:Type0)
  (#post: (a -> prop))
  (#q: HR.ref task_queue) (#c: R.ref int)
  (l: Lock.lock (inv_task_queue q c))
  (h: pure_handler post):
  stt a emp (fun res -> pure (post res))

val par_block_pulse_emp (#a: Type0)
  (#post: (a -> (prop)))
  (main_block: (unit_emp_stt_pure_pure a post))
: stt a emp (fun res -> pure (post res))


// -----------------------------------------------------
// Lifting the "pure" interface to resourceful tasks
// -----------------------------------------------------

val handler (#a: Type0) (post: a -> vprop): Type0

val spawn
  (#a:Type0)
  (#pre: vprop)
  (#post : (a -> vprop))
  (#q: HR.ref task_queue) (#c: R.ref int)
  (l: Lock.lock (inv_task_queue q c))
  (f : (unit -> (stt a pre post)))
  : stt (handler post) pre (fun _ -> emp)

val join
  (#a:Type0)
  (#post: (a -> vprop))
  (#q: HR.ref task_queue) (#c: R.ref int)
  (l: Lock.lock (inv_task_queue q c))
  (h: handler post)
  : stt a emp (fun res -> post res)

val par_block_pulse (#a: Type0) (#pre: vprop) (#post: a -> vprop)
  (main_block: unit -> stt a pre post)
: stt a pre (fun res -> post res)