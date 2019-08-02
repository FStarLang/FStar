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
module ArgsAndQuals

(* Seems silly, but this used to complain about an inference failure instead of the
 * obviously wrong arguments. Using the right arguments fails anyway,
 * see Guido's comment on #1486 on July 30 2018,
 * https://github.com/FStarLang/FStar/issues/1486#issuecomment-408958279 *)

val test1 : #a:Type -> #wp1:pure_wp a -> $t1:(unit -> PURE a wp1) -> PURE a wp1
[@(expect_failure [91])]
let test1 #_ #_ #_ t1 = t1 ()
