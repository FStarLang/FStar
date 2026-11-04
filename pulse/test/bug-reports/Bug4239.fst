module Bug4239

(* FStarLang/FStar#4239: Core must not treat type constructors as injective.
   [natlt i <: natlt n] holds when [i <= n], by unfolding [natlt]; Core used
   to demand [i == n] from the arguments instead. It now also relates the
   unfoldings, and either guard suffices. *)
#lang-pulse
open Pulse
module SZ = FStar.SizeT

let natlt (n: nat) = i:nat { i < n }

let works #n (x: natlt n -> bool) (i: nat { i < n }) =
  let a: (natlt i -> bool) = x in
  ()

fn doesnt_work #n (x: natlt n -> bool) (i: nat { i < n })
{
  let a: (natlt i -> bool) = x;
  ()
}

type sz = SZ.t
type szlt (n:int) = i:sz{SZ.v i < n}

fn szlt_weaken
  (x y : sz {SZ.v y <= SZ.v x})
  (k : szlt (SZ.v y))
{
  let k : szlt (SZ.v x) = k;
  ()
}

fn pair_refinement ()
{
  let xx : (nat & bool) = (10, true);
  ()
}
