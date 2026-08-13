(*
   Copyright 2008-2022 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Author: Aseem Rastogi
*)

/// This module used to derive a Hoare-style state effect using a free monad.
/// In the simplified effect system the Hoare pre/postconditions are built into
/// every computation type, so the example is now just the underlying free state
/// monad together with its definitional interpreter.

module HoareSTFree

/// The free monad contains an Act node with an atomic state action and a
/// continuation.  It can be made total by indexing it with a fuel/size, but this
/// example keeps the original potentially-diverging tree shape.

noeq
type m (st:Type0) : a:Type0 -> Type =
  | Ret : #a:Type0 -> x:a -> m st a
  | Act : #a:Type0 -> #b:Type0 -> act:(st -> Tot (a & st)) -> k:(a -> m st b) -> m st b

let return (#st:Type0) (#a:Type0) (x:a) : m st a = Ret x

let rec bind (#st:Type0) (#a #b:Type0) (f:m st a) (g:a -> m st b) : m st b =
  match f with
  | Ret x -> g x
  | Act act k -> Act act (fun x -> bind (k x) g)

let (let!) (#st:Type0) (#a #b:Type0) (f:m st a) (g:a -> m st b) : m st b = bind f g

let lift_act (#st:Type0) (#a:Type0) (act:st -> Tot (a & st)) : m st a =
  Act act (fun x -> Ret x)

let get (#s:Type0) : m s s = Act (fun x -> (x, x)) (fun x -> Ret x)

let put (#s:Type0) (x:s) : m s unit = Act (fun _ -> ((), x)) (fun y -> Ret y)

let modify (#s:Type0) (f:s -> s) : m s unit =
  let! s0 = get #s in
  put (f s0)

let rec run (#st:Type0) (#a:Type0) (f:m st a) (s0:st)
  : Div (a & st)
  = match f with
    | Ret x -> (x, s0)
    | Act act k ->
      let x, s1 = act s0 in
      run (k x) s1

assume val st : Type0
assume val p : prop
assume val q : prop
assume val st_p : st -> prop
assume val st_q : st -> prop
assume ST_axiom : forall s. st_p s ==> st_q s

assume val f : squash p -> m st unit
assume val g : unit -> Pure unit True (fun _ -> p)
assume val h : unit -> m st unit

/// The original example showed how pure refinements compose with Hoare-state
/// indices.  Here the logical obligations are ordinary Pure preconditions.
let test () : m st unit =
  g ();
  let! _ = f () in
  h ()

let incr : m int unit = modify (fun x -> x + 1)

let incr_twice : m int int =
  let! _ = incr in
  let! _ = incr in
  get

let _ : nonempty (int & int) = nonempty_intro (0, 0)
let test_run : int & int = run incr_twice 0
