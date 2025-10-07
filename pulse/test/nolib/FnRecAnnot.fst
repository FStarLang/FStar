module FnRecAnnot

#lang-pulse
open Pulse.Nolib


let t = unit -> stt unit emp (fun _ -> emp)

// This should work eventually.
[@@expect_failure]
fn rec f () : t = _ { f () }
