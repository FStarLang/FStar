module NuPool

open Pulse.Lib.Pervasives
open Pulse.Lib.Pledge
module T = FStar.Tactics.V2

val handle : Type0
val pool : Type0
val pool_alive (#[T.exact (`1.0R)] f : perm) (p:pool) : slprop

val joinable (p: pool) (post: slprop) (h: handle) : slprop

val spawn
  (p: pool)
  (#pf: perm)
  (#pre: slprop)
  (#post: slprop)
  (f : unit -> stt unit pre (fun _ -> post))
  : stt handle (pool_alive #pf p ** pre)
               (fun h -> pool_alive #pf p ** joinable p post h)

val pool_done (p:pool) : slprop

val disown
  (#p : pool)
  (#post : slprop)
  (h : handle)
  : stt_ghost unit [] (joinable p post h)
                   (fun _ -> pledge [] (pool_done p) post)

(* spawn + disown *)
val spawn_
  (p: pool)
  (#pf : perm)
  (#pre : slprop)
  (#post : slprop)
  (f : unit -> stt unit (pre) (fun _ -> post))
  : stt unit (pool_alive #pf p ** pre)
             (fun _ -> pool_alive #pf p ** pledge [] (pool_done p) (post))

val await
  (#p: pool)
  (#post : slprop)
  (h : handle)
  (#f : perm)
  : stt unit (pool_alive #f p ** joinable p post h)
             (fun _ -> pool_alive #f p ** post)

val await_pool
  (p:pool)
  (#is:inames)
  (#f:perm)
  (q : slprop)
  : stt unit (pool_alive #f p ** pledge is (pool_done p) q)
             (fun _ -> pool_alive #f p ** q)

val teardown_pool
  (p:pool)
  : stt unit (pool_alive p)
             (fun _ -> pool_done p)

val share_alive
  (p:pool)
  (e:perm)
  : stt_ghost unit []
              (pool_alive #e p)
              (fun () -> pool_alive #(e /. 2.0R) p ** pool_alive #(e /. 2.0R) p)

val gather_alive
  (p:pool)
  (e:perm)
  : stt_ghost unit []
              (pool_alive #(e /. 2.0R) p ** pool_alive #(e /. 2.0R) p)
              (fun () -> pool_alive #e p)

val setup_pool
  (n: pos)
  : stt pool
         emp
         (fun p -> pool_alive p)
