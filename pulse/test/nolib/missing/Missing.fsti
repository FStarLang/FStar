module Missing

#lang-pulse
open Pulse

ghost fn foo ()
  ensures pure False
