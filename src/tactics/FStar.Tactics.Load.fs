#light "off"

module FStar.Tactics.Load

let load_tactic (s: string) = failwith "Not implemented"; ()
let load_tactics (ss: list<string>) = List.iter load_tactic ss
