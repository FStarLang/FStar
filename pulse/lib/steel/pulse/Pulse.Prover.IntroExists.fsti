module Pulse.Prover.IntroExists

module T = FStar.Tactics

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Common
open Pulse.Typing.Metatheory
open Pulse.Checker.VPropEquiv
open Pulse.Prover.Util
open Pulse.Prover.Common

val intro_exists_prover_step : prover_step_t
