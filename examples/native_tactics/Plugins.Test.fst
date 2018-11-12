module Plugins.Test

open FStar.Tactics
open Plugins

let _ = assert_norm (int_plugin 2 = 2)

let _ = assert_norm (tuple_plugin 3 true = (3, true))

let _ = assert_norm (any_plugin [3;4] = [3;4])
