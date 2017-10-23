#light "off"

module FStar.Tactics.Load

let load_tactic (tac: string) = failwith "Not implemented"
let load_tactics (tacs: list<string>) = List.iter load_tactic tacs
let load_tactics_dir (dir: string) = ()
let compile_modules (dir: string) (tacs: list<string>) = ()