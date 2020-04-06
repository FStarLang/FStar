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
module ReflectionMisc

open FStar.Tactics

let tm = `(1,2)

let _ = assert True
            by (let r = destruct_tuple tm in
                match r with
                | Some [a;b]  -> guard (a `term_eq` (`1));
                                 guard (b `term_eq` (`2))
                | _ -> fail "")
