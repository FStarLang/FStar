(*
   Copyright 2023 Microsoft Research

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

module TaskPool

open Pulse.Lib.Pervasives
open Pulse.Lib.SpinLock
open Pulse.Lib.Par.Pledge

module T = FStar.Tactics.V2

let pool : Type0 = magic ()
let pool_alive (#[T.exact (`full_perm)]p : perm) (pool:pool) : vprop
  = magic()
let pool_done = magic ()

let setup_pool (n:nat)
  = magic ()

let task_handle pool a post = magic ()
let joinable #p #a #post th = magic ()
let joined   #p #a #post th = magic ()

let handle_solved #p #a #post th = magic()

let spawn #a #pre #post p #e = magic ()

let spawn_ #pre #post p #e = magic ()

let must_be_done = magic ()

let join0 = magic ()

#set-options "--print_universes"

#set-options "--print_universes"

```pulse
fn __extract
  (#p:pool)
  (#a:Type0)
  (#post : (a -> vprop))
  (th : task_handle p a post)
  requires handle_solved th
  returns x:a
  ensures post x
{
  admit()
}
``` 

let extract = __extract

let share_alive _ _ = admit()
let gather_alive _ _ = admit()

```pulse
fn __join
  (#p:pool)
  (#a:Type0)
  (#post : (a -> vprop))
  (th : task_handle p a post)
  requires joinable th
  returns x:a
  ensures post x
{
  join0 th;
  extract th
}
``` 
let join = __join

let teardown_pool
  (p:pool)
  : stt unit (pool_alive p) (fun _ -> pool_done p)
  = magic ()

let teardown_pool' p e = magic ()
