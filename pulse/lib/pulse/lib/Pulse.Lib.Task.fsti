(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Pulse.Lib.Task

open Pulse.Lib.Pervasives
open Pulse.Lib.Par.Pledge
module T = FStar.Tactics

val pool : Type0
val pool_alive : (#[T.exact (`full_perm)]p : perm) -> pool -> vprop
val pool_done : pool -> vprop

val setup_pool (n:pos)
  : stt pool emp (fun p -> pool_alive #full_perm p)

val task_handle : pool -> a:Type0 -> (a -> vprop) -> Type0
val joinable : #p:pool -> #a:Type0 -> #post:_ -> th:(task_handle p a post) -> vprop
val joined   : #p:pool -> #a:Type0 -> #post:_ -> th:(task_handle p a post) -> vprop

val handle_solved
  (#p : pool) 
  (#a : Type0)
  (#post : a -> vprop)
  (th : task_handle p a post)
  : vprop

(* NOTE! Spawn only requires an *epsilon* of permission over the pool.
We do not have to be exclusive owners of it in order to queue a job,
even if that modifies it. How to model this under the hood? *)
val spawn
  (#a : Type0)
  (#pre : vprop) (#post : a -> vprop)
  (p : pool)
  (#[T.exact (`full_perm)] e : perm)
  ($f : unit -> stt a pre (fun (x:a) -> post x))
  : stt (task_handle p a post)
        (pool_alive #e p ** pre)
        (fun th -> pool_alive #e p ** joinable th)

(* Spawn of a unit-returning task with no intention to join, simpler. *)
val spawn_
  (#pre #post : _)
  (p:pool)
  (#[T.exact (`full_perm)] e : perm)
  (f : unit -> stt unit pre (fun _ -> post))
  : stt unit (pool_alive #e p ** pre)
             (fun prom -> pool_alive #e p ** pledge [] (pool_done p) post)

(* If the pool is done, all pending joinable threads must be done *)
val must_be_done
  (#p : pool)
  (#a: Type0)
  (#post : a -> vprop)
  (th : task_handle p a post)
  : stt_ghost unit emp_inames (pool_done p ** joinable th) (fun () -> pool_done p ** handle_solved th)

val join0
  (#p:pool)
  (#a:Type0)
  (#post : a -> vprop)
  (th : task_handle p a post)
  : stt unit (joinable th) (fun () -> handle_solved th)

val extract
  (#p:pool)
  (#a:Type0)
  (#post : a -> vprop)
  (th : task_handle p a post)
  : stt a (handle_solved th) (fun x -> post x)
  
val share_alive
  (p:pool)
  (e:perm)
  : stt_ghost unit
              emp_inames
              (pool_alive #e p)
              (fun () -> pool_alive #(half_perm e) p ** pool_alive #(half_perm e) p)

val gather_alive
  (p:pool)
  (e:perm)
  : stt_ghost unit
              emp_inames
              (pool_alive #(half_perm e) p ** pool_alive #(half_perm e) p)
              (fun () -> pool_alive #e p)

val join
  (#p:pool)
  (#a:Type0)
  (#post : a -> vprop)
  (th : task_handle p a post)
  : stt a (joinable th) (fun x -> post x)

(* We must exclusively own the pool in order to terminate it. *)
val teardown_pool
  (p:pool)
  : stt unit (pool_alive #full_perm p) (fun _ -> pool_done p)

(* Or, have at least an epsilon of permission over it, and know that
the rest of it (1-e) is "sunk" into the pool itself. *)
val teardown_pool'
  (#is : Pulse.Lib.InvList.invlist)
  (p:pool) (f:perm{f `lesser_perm` full_perm})
  : stt unit (pool_alive #f p ** pledge is (pool_done p) (pool_alive #(comp_perm f) p))
             (fun _ -> pool_done p)
