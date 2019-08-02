#light "off"

module FStar.Tactics.Load
open FStar.All
val load_tactics: list<string> -> unit
val load_tactics_dir: string -> unit
val compile_modules: string -> list<string> -> unit