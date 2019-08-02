(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module Plugins.Test

open FStar.Tactics
open Plugins

let _ = assert_norm (int_plugin 2 = 2)

let _ = assert_norm (tuple_plugin 3 true = (3, true))

let _ = assert_norm (any_plugin [3;4] = [3;4])
