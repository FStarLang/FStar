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

let spawn #a #pre #post #e = magic ()

let spawn_ #pre #post #e = magic ()

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

let split_alive _ _ = admit()

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
