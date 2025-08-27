module CombinatorArg
open Pulse
open Pulse.Lib.Trade
#lang-pulse

fn test1 ()
  ensures emp @==> (emp ** emp)
{
  intro_trade emp (emp ** emp) emp =_{}
}