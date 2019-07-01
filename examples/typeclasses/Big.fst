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
module Big

type z = | X
type s (a:Type) = | Y

class c a = { x : a }

instance iz : c z = { x = X }
instance is (a:Type) (i1 : c a) (i2 : c a) : c (s a) = { x = Y }

let f (a:Type) : s (s (s (s (s (s (s (s z))))))) = x
