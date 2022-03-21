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
module Subtyping

assume val p : int -> Type0
assume val q : int -> Type0
assume val n : n:int{q n}

let f : int -> b:int{q b} = fun (_:int) -> n
let g : a:int{p a} -> int = f
let h : a:int{p a} -> int = fun (_:int) -> n // this used to fail before fab0d820c8e342f16e83c5e1b4734876e5a59106
let i : a:int{p a} -> b:int{p b} = fun n -> n
