module CustardPluginTest
open FStar.Tactics.V2
open CustardPlugin

(* [norm [primops]] and nothing else: the definitions are irreducible, so
   the only thing that can reduce them is the native step the loaded plugin
   registered. *)

let _ = assert (CustardPlugin.f 1 == 124)
          by (norm [primops]; trefl ())

let _ = assert (CustardPlugin.flip (CustardPlugin.A 3) == CustardPlugin.C 3 "")
          by (norm [primops]; trefl ())

let _ = assert (CustardPlugin.flip (CustardPlugin.B (3, true)) == CustardPlugin.B (-3, false))
          by (norm [primops]; trefl ())

let _ = assert (CustardPlugin.fr ({ a = 3; b = true }) == ({ a = -3; b = true } <: CustardPlugin.record))
          by (norm [primops]; trefl ())
