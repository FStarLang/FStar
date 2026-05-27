module ExtractPulseFnIface
#lang-pulse

(** Interface for ExtractPulseFnIface.
    Tests that a Pulse fn declared in .fsti extracts to C correctly.
    Regression test: previously, fn declarations in .fsti were not
    recognized by the interleaver, causing the implementation to be
    tagged KrmlPrivate and silently dropped by KaRaMeL. *)

open Pulse.Lib.Pervasives
open Pulse.Lib.Reference
module R = Pulse.Lib.Reference

val pure_add (x y : int) : int

fn pulse_read_ref
  (r: ref int)
  (#v: Ghost.erased int)
  requires R.pts_to r v
  returns x: int
  ensures R.pts_to r v ** pure (x == Ghost.reveal v)
