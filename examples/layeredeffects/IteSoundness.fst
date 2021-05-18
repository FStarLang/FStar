(*
   Copyright 2008-2021 Microsoft Research

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

module IteSoundness

let unit : Type0 = unit
irreducible let an_attr : unit = ()

type repr (a:Type) (_:unit) = a

let return (a:Type) (x:a) : repr a () = x
let bind (a:Type) (b:Type) (f:repr a ()) (g:a -> repr b ()) : repr b () = g f

let if_then_else (a:Type)
  ([@@@ an_attr] phi:Type0)
  ([@@@ an_attr] bb:squash phi) 
  (f:repr a ())
  (g:repr a ())
  (b:bool)
  : Type
  = repr a ()

let subcomp (a:Type)
  ([@@@ an_attr] phi:Type0)
  ([@@@ an_attr] bb:squash phi)  (f:repr a ())
  : repr a () = f

open FStar.Tactics

[@@ resolve_implicits; an_attr]
let mtac () : Tac unit =
  smt ();
  smt ();
  exact (`True)

[@@ ite_soundness_by an_attr]
effect {
  M (a:Type) (_:unit)
  with {repr; return; bind; if_then_else; subcomp}
}
