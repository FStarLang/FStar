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
module Ex12.BMAC

open Ex12.Pad 

let keysize = 16 (* these are the sizes for SHA1 *) 
let macsize = 20  
type key = nbytes keysize
type tag = nbytes macsize

assume type key_prop : key -> block -> Type
type pkey (p:(block -> Type)) = k:key{key_prop k == p}

assume val keygen: p:(block -> Type) -> pkey p
assume val mac:    k:key -> t:block{key_prop k t} -> tag
assume val verify: k:key -> t:block -> tag -> b:bool{b ==> key_prop k t}


