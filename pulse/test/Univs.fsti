module Univs
open Pulse.Nolib
#lang-pulse

unobservable
fn stt_id u#a (#t: Type u#a) (x: t)
  returns y: t
  ensures rewrites_to x y