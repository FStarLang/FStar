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
module FStar.DM4F.ST

(**********************************************************
 * Dijkstra Monads for Free : Simple state
 *
 * A minimal example of defining a state effect along
 * with actions, over a parametrized state type.
 *
 **********************************************************)

(* The underlying representation type *)
let st (s:Type) (a:Type) = s -> M (a * s)

(* Monad definition *)
let return_st (s:Type) (a:Type) (x:a) : st s a = fun s0 -> x, s0

let bind_st (s:Type) (a:Type) (b:Type) (f:st s a) (g:a -> st s b) : st s b
  = fun (s0:s) -> let (x,s) = f s0 in g x s //<: M (b * s)
  (* TODO : investigate why the following does not work *)
  (* let h (s0:s) : = let (x,s) = f s0 in g x s <: M (a * s) in h *)

(* Actions *)
let get (s:Type) () : st s s = fun s0 -> s0, s0

let put (s:Type) (x:s) : st s unit = fun _ -> (), x

(*
 * Do the DM4F work. Note that the heap type is a parameter
 * of the resulting effect.
 *)
total reifiable reflectable new_effect {
  STATE_h (s:Type0) : a:Type -> Effect
  with repr     = st s
     ; bind     = bind_st s
     ; return   = return_st s
     ; get      = get s
     ; put      = put s
}

// Works fine
//let repr0 = STATE_h.repr int

// I would expect STATE.get to have type (s:Type) -> unit -> STATE s int
// but this is not a valid type in F* (the effect is depedent on the input type s)
// In current F*, we need to create a new applied effect in order to use this definition
// i.e. new_effect STATE_int = STATE_h int
