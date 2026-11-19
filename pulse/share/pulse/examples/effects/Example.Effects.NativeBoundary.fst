module Example.Effects.NativeBoundary
#lang-pulse

open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference

fn choose (#a:Type0) (value:a) (fail:bool)
  returns result:a
  ensures pure (not fail /\ result == value)
  raises (fun (e:a) -> pure (fail /\ e == value))
{
  if fail { raise value } else { value }
}

fn deliver (value:payload) (fail:bool)
  returns result:payload
  ensures pure (not fail /\ result == value)
  raises (fun (e:payload) -> pure (fail /\ e == value))
{
  choose value fail
}

fn invoke (r:ref int) (value:payload)
  (action:fn () requires R.pts_to r 0
    returns result:int ensures pure False
    raises (fun (e:payload) -> R.pts_to r 1 ** pure (e == value)))
  requires R.pts_to r 0
  returns result:int
  ensures pure False
  raises (fun (e:payload) -> R.pts_to r 1 ** pure (e == value))
{
  action ()
}
