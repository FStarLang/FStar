#light "off"
module FStar.Profiling
open FStar.All

val profile : f:(unit -> 'b)
            -> module_name:option<string>
            -> phase_name:string
            -> 'b

val report_and_clear: tag:string -> unit
