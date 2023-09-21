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
  : unit -> stt a pre post
let perform f () = f ()
