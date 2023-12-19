module UnixFork

(* This module assumes an unstructured unix-style fork *)

open Pulse.Lib.Pervasives
open Pulse.Lib.Par.Pledge

new
val thread : Type0

val joinable : thread -> vprop
val done     : thread -> vprop (* i.e. reapable/zombie *)

val fork 
  (#pre #post : vprop)
  (f : unit -> stt unit pre (fun () -> post))
  : stt thread pre (fun th -> joinable th ** pledge emp_inames (done th) post)

val join
  (th : thread)
  : stt unit (joinable th) (fun () -> done th)
