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
module Unit1.TopLevelPats

let (x, y) = (1, 2)
let _ = assert(x == 1)
let _ = assert(y == 2)

let make n = (n / 2, 3 `op_Multiply` n + 1)
let (z, w) = make 18
let _ = assert(z == 9)
let _ = assert(w == 55)
