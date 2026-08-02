(*
   Copyright 2019 Microsoft Research

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

module DijkstraStateMonad

/// This example used to derive a WP-indexed state effect from a free state
/// monad.  WPs and layered effects are gone, so this file keeps the genuine
/// underlying free state monad and its interpreter.

/// `m s a`: A classic free state monad
noeq
type m (s:Type0) (a:Type) =
  | Ret : a -> m s a
  | Get : (s -> m s a) -> m s a
  | Put : x:s -> m s a -> m s a

/// It's easy to sequentially compose terms in `m`
let rec bind_m #s #a #b (x:m s a) (y: (a -> m s b)) : m s b =
  match x with
  | Ret x -> y x
  | Get k -> Get (fun s -> bind_m (k s) y)
  | Put s k -> Put s (bind_m k y)

let return #s #a (x:a) : m s a = Ret x

let bind #s #a #b (x:m s a) (y: a -> m s b) : m s b =
  bind_m x y

let (let!) (#s:Type0) (#a #b:Type) (x:m s a) (y: a -> m s b) : m s b =
  bind x y

let get #s () : m s s = Get Ret

let put #s (x:s) : m s unit = Put x (Ret ())

/// Run the free state monad as a plain pure computation.
let rec run (#a:_) (#s:_) (m:m s a) (s0:s) : Pure (a & s) =
  match m with
  | Ret x -> (x, s0)
  | Get k -> run (k s0) s0
  | Put s k -> run k s

/// A stateful increment, formerly written in the derived IFST effect.
let iincr () : m int unit =
  let! x = get () in
  let y = x + 1 in
  put y

let run_iincr (s:int)
  : Pure (unit & int) (ensures fun r -> snd r == s + 1)
= run (iincr ()) s
