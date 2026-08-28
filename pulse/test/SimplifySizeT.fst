module SimplifySizeT
#lang-pulse
open Pulse.Lib.Pervasives
module SZ = FStar.SizeT


(* An opaque slprop indexed by a nat. The prover can only discharge these
goals by matching the index syntactically, so they exercise the SizeT
rewrites in Pulse.Simplify: without them, `SZ.v (SZ.add x y)` and
`SZ.v x + SZ.v y` are distinct terms and the goals below fail. *)
assume val myp (n:nat) : slprop

(* Off by default. *)
[@@expect_failure [228]]
fn add_without_flag (x:SZ.t) (y:SZ.t { SZ.fits (SZ.v x + SZ.v y) })
  requires myp (SZ.v x + SZ.v y)
  ensures myp (SZ.v (SZ.add x y))
{
  ()
}

#push-options "--ext pulse:extra_simplify"

fn add (x:SZ.t) (y:SZ.t { SZ.fits (SZ.v x + SZ.v y) })
  requires myp (SZ.v x + SZ.v y)
  ensures myp (SZ.v (SZ.add x y))
{
  ()
}

fn sub (x:SZ.t) (y:SZ.t { SZ.v x >= SZ.v y })
  requires myp (SZ.v x - SZ.v y)
  ensures myp (SZ.v (SZ.sub x y))
{
  ()
}

fn mul (x:SZ.t) (y:SZ.t { SZ.fits (SZ.v x * SZ.v y) })
  requires myp (SZ.v x * SZ.v y)
  ensures myp (SZ.v (SZ.mul x y))
{
  ()
}

fn div (x:SZ.t) (y:SZ.t { SZ.v y <> 0 })
  requires myp (SZ.v x / SZ.v y)
  ensures myp (SZ.v (SZ.div x y))
{
  ()
}

fn rem (x:SZ.t) (y:SZ.t { SZ.v y <> 0 })
  requires myp (SZ.v x % SZ.v y)
  ensures myp (SZ.v (SZ.rem x y))
{
  ()
}

(* Nested rewrite: the operator rule exposes `SZ.v 1sz`, which the SMT
solver then relates to 1. *)
fn add_literal (x:SZ.t { SZ.fits (SZ.v x + 1) })
  requires myp (SZ.v x + 1)
  ensures myp (SZ.v (SZ.add x 1sz))
{
  ()
}

#pop-options
