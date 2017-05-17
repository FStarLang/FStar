#light "off"
module FStar.Tactics.Native

module BU = FStar.Util

let register_tactic s = BU.print1 "Registered tactic %s\n" s

let find_tactic s = ()