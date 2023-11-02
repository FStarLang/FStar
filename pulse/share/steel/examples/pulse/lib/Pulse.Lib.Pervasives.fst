module Pulse.Lib.Pervasives
include Pulse.Main
include Pulse.Lib.Core
include Pulse.Lib.Array
include Pulse.Lib.Reference
include Steel.FractionalPermission
include FStar.Ghost

(* Pulse will currently not recognize calls to anything other than
top-level names, so this allows to force it. *)
val perform
  (#a #pre #post : _)
  (f : unit -> stt a pre post)
  : stt a pre post
let perform f = f ()

val perform_ghost
  (#a #is #pre #post : _)
  (f : unit -> stt_ghost is a pre post)
  : stt_ghost is a pre post
let perform_ghost f = f ()

val perform_atomic
  (#a #is #pre #post : _)
  (f : unit -> stt_atomic is a pre post)
  : stt_atomic is a pre post
let perform_atomic f = f ()
