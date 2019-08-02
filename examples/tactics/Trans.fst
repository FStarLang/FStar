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
module Trans

open FStar.Tactics

assume val t : Type0
assume val a : t
assume val b : t

val trans : (#a:Type) -> (#x:a) -> (#z:a) -> (#y:a) ->
                    squash (x == y) -> squash (y == z) -> Lemma (x == z)
let trans #a #x #z #y e1 e2 = ()

// Even if we admit the goals, an uninstantiated variable remains
[@expect_failure]
let _ = assert (a == b) by (apply_lemma (`trans); tadmit(); tadmit ())
