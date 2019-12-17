(*
   Copyright 2008-2019 Microsoft Research

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
#light "off"

module FStar.Profiling
open FStar.All

// When --profile module_name
// And  --profile_component component_name
// are both true, measure the execution time of f
// and accumulate it in a profiling counter
// associated with `component_name`
val profile : f:(unit -> 'b)
            -> module_name:option<string>
            -> component_name:string
            -> 'b

// Print the elapsed time from all profiling counters
// Prefix the profiling report with the value of `tag`
// And reset all of the profiling counters
val report_and_clear: tag:string -> unit
