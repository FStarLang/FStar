#light "off"
module FStar.Profiling
open FStar.All

val init_profiler         : unit -> unit
val profile               : (unit -> 'b) -> string-> string -> bool -> 'b * int
val disable_profiler      : unit -> unit
