module Univs
open Pulse.Nolib
#lang-pulse

unobservable
fn stt_id u#a (#t: Type u#a) (x: t)
  returns y: t
  ensures rewrites_to x y
{
  x
}

fn use_stt_id u#b (t: Type u#(max b 100)) (x: t)
  returns y: t
{
  stt_id x
}