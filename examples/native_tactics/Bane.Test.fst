module Bane.Test
open FStar.Tactics
open Bane

let test =
   assert_by_tactic for_you12 mytac
