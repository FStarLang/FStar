module EverParseIssue
#lang-pulse
open Pulse
open Pulse.Lib.Trade
open Pulse.Lib.Trade.Util { rewrite_with_trade, trans }

// EverParse heavily uses rewrite_with_trade to convert unifiable slprops
let a = emp
let b = a
let c = b

fn foo ()
  requires a
  ensures c
  ensures trade c a
{
  rewrite_with_trade a b;
  rewrite_with_trade b c;
  // ambiguous: `trade b a` unifies with both `trade c b` and `trade b a`
  trans c b a;
}