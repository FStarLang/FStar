module Admit
open Pulse
#lang-pulse

fn test1 () {
  if true {
    admit ();
  };
  ()
}