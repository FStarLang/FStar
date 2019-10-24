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

   Author: Nikhil Swamy
*)

module FST

noeq
type m (s:Type0) (a:Type) = //The index `s` needs to be in Type0
  | Ret : a -> m s a
  | Get : (s -> m s a) -> m s a
  | Put : x:s -> m s a -> m s a
module W = FStar.WellFounded

let rec bind_m #s #a #b (x:m s a) (y: (a -> m s b)) : m s b =
  match x with
  | Ret x -> y x
  | Get k -> Get (fun s -> W.axiom1 k s; bind_m (k s) y)
  | Put s k -> Put s (bind_m k y)


(* Just a simply typed variant *)
let repr a s =
  unit -> m s a

let return (a:Type) (s:Type) (x:a)
  : repr a s
  = fun () -> Ret x

let rec bind a b s (f:repr a s) (g : (a -> repr b s))
  : repr b s
  = let m_f = f () in
    let m_g = fun x -> g x () in
    fun () -> bind_m #s #a #b m_f m_g

//no subsumption rule
let subcomp (a:Type) (s:Type) (f:repr a s)
  : Tot (repr a s)
  = f

let if_then_else (a:Type) (s:Type)
                 (f:repr a s)
                 (g:repr a s)
                 (p:Type0)
  : Type
  = repr a s

let get s : repr s s =
    fun () -> Get Ret

let put s (x:s) : repr unit s =
    fun () -> Put x (Ret ())

reifiable reflectable
layered_effect {
  FST : a:Type -> s:Type0 -> Effect
  with repr         = repr;
       return       = return;
       bind         = bind;
       subcomp      = subcomp;
       if_then_else = if_then_else;

       get = get;
       put = put
}

let lift_pure_fst
    (a:Type)
    (s:Type)
    (wp:pure_wp a)
    (f:unit -> PURE a wp)
  : repr a s
  = assume(wp (fun x -> True)); //to suppress the WP
    return a s (f())

sub_effect PURE ~> FST = lift_pure_fst

let incr () : FST unit int =
  let x = FST?.get int in
  let y = x + 1 in
  FST?.put int y
