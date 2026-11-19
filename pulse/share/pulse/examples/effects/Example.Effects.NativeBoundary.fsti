module Example.Effects.NativeBoundary
#lang-pulse

open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference

noeq type payload = { message:string; values:list int }

fn choose (#a:Type0) (value:a) (fail:bool)
  returns result:a
  ensures pure (not fail /\ result == value)
  raises (fun (e:a) -> pure (fail /\ e == value))

// A concrete export forces Cherry calls across the unit boundary even when
// other instantiations of choose are specialized locally in the client.
fn deliver (value:payload) (fail:bool)
  returns result:payload
  ensures pure (not fail /\ result == value)
  raises (fun (e:payload) -> pure (fail /\ e == value))

fn invoke (r:ref int) (value:payload)
  (action:fn () requires R.pts_to r 0
    returns result:int ensures pure False
    raises (fun (e:payload) -> R.pts_to r 1 ** pure (e == value)))
  requires R.pts_to r 0
  returns result:int
  ensures pure False
  raises (fun (e:payload) -> R.pts_to r 1 ** pure (e == value))
