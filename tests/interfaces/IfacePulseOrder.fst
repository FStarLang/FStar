module IfacePulseOrder

#lang-pulse
open Pulse

ghost
fn g ()
  ensures emp
{ (); }

#lang-pulse
open Pulse

ghost
fn f ()
  ensures emp
{ (); }
