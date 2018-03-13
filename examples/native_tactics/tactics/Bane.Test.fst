module Bane.Test
open FStar.Tactics
open Bane.Lib

let test =
   assert_by_tactic for_you12 Bane.Lib.mytac
