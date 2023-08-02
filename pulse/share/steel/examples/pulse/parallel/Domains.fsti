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

let unit_emp_stt_pure_pure a p
  = unit -> stt a emp (fun x -> pure (p x))

val task_queue: Type u#1

val par_env: Type0

// ---------------------------------------------
// Pure interface (without resources)
// ---------------------------------------------

val pure_handler (#a: Type0) (post: a -> prop): Type0

val spawn_emp
  (#a:Type0)
  (p: par_env)
  (post: (a -> prop))
  (f : (par_env -> unit_emp_stt_pure_pure a post))
: stt (pure_handler post) emp (fun _ -> emp)

val join_emp
  (#a:Type0)
  (#post: (a -> prop))
  (h: pure_handler post)
: stt a emp (fun res -> pure (post res))

val worker (p: par_env): stt unit emp (fun _ -> emp)

val init_par_env (_: unit): stt par_env emp (fun _ -> emp)

val par_block_pulse_emp (#a: Type0)
  (#post: (a -> (prop)))
  (main_block: (par_env -> (unit_emp_stt_pure_pure a post)))
: stt a emp (fun res -> pure (post res))

// ---------------------------------------------
// Interface with resources
// ---------------------------------------------

val handler (#a: Type0) (post: a -> vprop): Type0

val spawn
  (#a:Type0)
  (#pre: vprop)
  (#post : (a -> vprop))
  (p: par_env)
  (f : (par_env -> unit -> stt a pre post))
: stt (handler post) pre (fun _ -> emp)

val join
  (#a:Type0)
  (#post: (a -> vprop))
  (h: handler post)
: stt a emp (fun res -> post res)

val par_block_pulse (#a: Type0) (#pre: vprop)
  (#post: (a -> vprop))
  (main_block: (par_env -> unit -> (stt a pre post)))
: stt a pre (fun res -> post res)