module Pulse.Nolib

(* Open this file for unit-tests that depend only on the plugin
and on core files, but not anything in the Pulse library. *)

open Pulse.Main {}
include Pulse.Lib.Core
include FStar.Mul
include PulseCore.FractionalPermission
include PulseCore.Observability
include FStar.Ghost
