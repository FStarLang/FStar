(*
   Copyright 2008-2018 Microsoft Research

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

module FStar.Tactics.Load
open FStar.All
let load_tactic (tac: string) : unit = failwith "load_tactic: Not implemented in F#"
let load_tactics (tacs: list<string>) = List.iter load_tactic tacs
let load_tactics_dir (dir: string) : unit = failwith "load_tactics_dir: Not implemented in F#"
let compile_modules (dir: string) (tacs: list<string>) : unit = failwith "compile_modules: Not implemented in F#"