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
#push
module Interact
let x0 = 0
#end
#push
let x1 = 1
#end
#push
let x2 = 2
#end
#push
type t0 =
  | C0
  | C1
#end
#pop
#push
type t0 =
  | C0 : int -> t0
  | C1 : int -> t0
#end
#push
let f0 () = C0 x0
let f1 () = C1 x1
#end
#pop
#pop
#push
type t0 =
  | C0 : int * int -> t0
  | C1 : int * int -> t0
let f0 x = C0 (x0, x)
let f1 x = assert (x1=1); C1 (x1, x)
#end
#pop
#push
type t0 =
  | C0 : int * int -> t0
  | C1 : int * int -> t0
  | C2 : int * int -> t0
let f0 x = C0 (x0, x)
let f1 x = assert (x1=1); C1 (x1, x)
let f2 x = assert (x2=2); C2 (x1, x)
#end
#pop
#push
let z = assert (x2=1)
#end
#pop
#push
let z = assert (x2=2)
#end
