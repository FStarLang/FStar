#light "off"

module FStar.Tactics.Load
open FStar.All
let load_tactic (tac: string) : unit = failwith "load_tactic: Not implemented in F#"
let load_tactics (tacs: list<string>) = List.iter load_tactic tacs
let load_tactics_dir (dir: string) : unit = failwith "load_tactics_dir: Not implemented in F#"
let compile_modules (dir: string) (tacs: list<string>) : unit = failwith "compile_modules: Not implemented in F#"