module Bug4239
open Pulse.Nolib
#lang-pulse

let natlt (n: nat) = i:nat { i < n }

let works #n (x: natlt n -> bool) (i: nat { i < n }) =
  let a: (natlt i -> bool) = x in
  ()

fn doesnt_work #n (x: natlt n -> bool) (i: nat { i < n }) {
  let a: (natlt i -> bool) = x;
  ()
}

module SZ = FStar.SizeT
type sz  = FStar.SizeT.t
type szlt (n:int) = i:sz{SZ.v i <  n}
fn bug
  (x y : sz {SZ.v y <= SZ.v x})
  (k : szlt (SZ.v y))
{
  assert pure (SZ.v k < SZ.v y);
  assert pure (SZ.v y <= SZ.v x);
  assert pure (SZ.v k < SZ.v x);
  let k : szlt (SZ.v x) = k; // Fails, but should work
  ();
}