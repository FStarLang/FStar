module FnAnnot
open Pulse.Nolib
#lang-pulse

let t (p: slprop) = stt unit (requires p ** emp) (ensures fun _ -> emp)

fn g () : t emp = { () }