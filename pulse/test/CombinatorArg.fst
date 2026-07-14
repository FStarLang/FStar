module CombinatorArg
open Pulse
open Pulse.Lib.Trade
#lang-pulse

// The `emp ** emp` in the combinator argument of the ensures is purified to
// `emp`, so a body producing `emp @==> emp` satisfies it.
fn test1 ()
  ensures emp @==> (emp ** emp)
{
  intro_trade emp emp emp fn _{}
}

fn test2 ()
  ensures emp @==> (emp ** emp)
{
  intro (emp @==> emp) fn _{}
}

fn comb3 (k: unit -> stt unit emp (fun _ -> emp))
  returns n: nat
{
  42
}
fn test3 () {
  let n = comb3 fn _{};
  ()
}
