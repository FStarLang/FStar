#light "off"
module FStar.Profiling
open FStar.All

val init_profiler         : unit -> unit
val profile               : (unit -> 'b) -> (unit -> string) -> Options.profile_t -> 'b * int
val disable_profiler      : unit -> unit
