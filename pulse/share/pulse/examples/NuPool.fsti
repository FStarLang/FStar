module NuPool

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Pledge
module T = FStar.Tactics.V2

val handle : Type0
val pool : Type0
val pool_alive (#[T.exact (`1.0R)] f : perm) (p:pool) : slprop

val joinable (p: pool) (post: slprop) (h: handle) : slprop

fn spawn
  (p: pool)
  (#pf: perm)
  (#pre: slprop)
  (#post: slprop)
  (f : unit -> stt unit pre (fun _ -> post))
  requires pool_alive #pf p ** pre
  returns h : handle
  ensures pool_alive #pf p ** joinable p post h

val pool_done (p:pool) : slprop

ghost
fn disown
  (#p : pool)
  (#post : slprop)
  (h : handle)
  requires joinable p post h
  ensures  pledge [] (pool_done p) post

(* spawn + disown *)
fn spawn_
  (p: pool)
  (#pf : perm)
  (#pre : slprop)
  (#post : slprop)
  (f : unit -> stt unit (pre) (fun _ -> post))
  requires pool_alive #pf p ** pre
  ensures pool_alive #pf p ** pledge [] (pool_done p) post

fn await
  (#p: pool)
  (#post : slprop)
  (h : handle)
  (#f : perm)
  requires pool_alive #f p ** joinable p post h
  ensures pool_alive #f p ** post

fn await_pool
  (p:pool)
  (#is:inames)
  (#f:perm)
  (q : slprop)
  requires pool_alive #f p ** pledge is (pool_done p) q
  ensures pool_alive #f p ** q

fn teardown_pool
  (p:pool)
  requires pool_alive p
  ensures pool_done p

ghost
fn share_alive
  (p:pool)
  (e:perm)
  requires pool_alive #e p
  ensures pool_alive #(e /. 2.0R) p ** pool_alive #(e /. 2.0R) p

ghost
fn gather_alive
  (p:pool)
  (e:perm)
  requires pool_alive #(e /. 2.0R) p ** pool_alive #(e /. 2.0R) p
  ensures pool_alive #e p

fn setup_pool
  (n: pos)
  requires emp
  returns p : pool
  ensures pool_alive p
