module Example.Effects.NativeNoExtract
#lang-pulse

open Pulse.Lib.Pervasives

#push-options "--ext pulse.noextract"
fn blocked ()
  returns x:bool
  ensures pure x
  raises (fun (_:bool) -> pure False)
{
  true
}
#pop-options
