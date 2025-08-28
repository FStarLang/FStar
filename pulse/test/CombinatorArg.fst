module CombinatorArg
open Pulse
open Pulse.Lib.Trade
#lang-pulse

fn test1 ()
  ensures emp @==> (emp ** emp)
{
  intro_trade emp (emp ** emp) emp fn _{}
}

fn test2 ()
  ensures emp @==> (emp ** emp)
{
  intro (emp @==> emp ** emp) fn _{}
}