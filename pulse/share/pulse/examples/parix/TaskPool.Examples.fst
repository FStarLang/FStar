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

module TaskPool.Examples

open Pulse.Lib.Pervasives
open Pulse.Lib.Par.Pledge
open Pulse.Lib.Task

assume
val qsv : nat -> vprop
assume
val qsc : n:nat -> stt unit emp (fun _ -> qsv n)

let spawn_ #pre #post p f = spawn_ #pre #post p #full_perm f

```pulse
fn qs (n:nat)
  requires emp
  returns _:unit
  ensures qsv 1 ** qsv 2 ** qsv 3 ** qsv 4
{
  let p = setup_pool 42;
  spawn_ p (fun () -> qsc 1);
  spawn_ p (fun () -> qsc 2);
  spawn_ p (fun () -> qsc 3);
  spawn_ p (fun () -> qsc 4);
  teardown_pool p;
  redeem_pledge [] (pool_done p) (qsv 1);
  redeem_pledge [] (pool_done p) (qsv 2);
  redeem_pledge [] (pool_done p) (qsv 3);
  redeem_pledge [] (pool_done p) (qsv 4);
  drop_ (pool_done p);
  ()
}
```

```pulse
fn qs_joinpromises (n:nat)
  requires emp
  returns _:unit
  ensures qsv 1 ** qsv 2 ** qsv 3 ** qsv 4
{
  let p = setup_pool 42;
  spawn_ p (fun () -> qsc 1);
  spawn_ p (fun () -> qsc 2);
  spawn_ p (fun () -> qsc 3);
  spawn_ p (fun () -> qsc 4);
  join_pledge #[] #(pool_done p) (qsv 1) (qsv 2);
  join_pledge #[] #(pool_done p) (qsv 3) (qsv 4);
  teardown_pool p;
  redeem_pledge [] (pool_done p) (qsv 1 ** qsv 2);
  redeem_pledge [] (pool_done p) (qsv 3 ** qsv 4);
  drop_ (pool_done p);
  ()
}
```

```pulse
fn qs12 (_:unit)
  requires emp
  returns _:unit
  ensures qsv 1 ** qsv 2
  {
    qsc 1;
    qsc 2
  }
```

```pulse
fn qsh (n:nat)
  requires emp
  returns _:unit
  ensures qsv 1 ** qsv 2 ** qsv 3 ** qsv 4
{
  let p = setup_pool 42;
  spawn_ p qs12;
  // could do the same thing for 3&4... it's gonna work.
  // also qs12 could spawn and join its tasks, it would clearly work
  spawn_ p (fun () -> qsc 3);
  spawn_ p (fun () -> qsc 4);
  teardown_pool p;
  redeem_pledge [] (pool_done p) (qsv 1 ** qsv 2);
  redeem_pledge [] (pool_done p) (qsv 3);
  redeem_pledge [] (pool_done p) (qsv 4);
  drop_ (pool_done p);
  ()
}
```

```pulse
fn qs12_par (p:pool)
  requires pool_alive p
  returns _:unit
  ensures pool_alive p ** pledge [] (pool_done p) (qsv 1) ** pledge [] (pool_done p) (qsv 2)
  {
    spawn_ p (fun () -> qsc 1);
    spawn_ p (fun () -> qsc 2);
    ()
  }
```

[@@expect_failure]
```pulse
fn qsh_par (n:nat)
  requires emp
  returns _:unit
  ensures qsv 1 ** qsv 2 ** qsv 3 ** qsv 4
{
  let p = setup_pool 42;
  spawn p (fun () -> qs12_par p);
  (* Ah! This cannot work right now since we need to share part
  of the pool_alive vprop to the spawned task, so we have
  to index pool_alive with a permission, and allow
  share/gather. *)
  
  spawn p (fun () -> qsc 3);
  spawn p (fun () -> qsc 4);
  teardown_pool p;
  redeem_pledge (pool_done p) (qsv 1)
  redeem_pledge (pool_done p) (qsv 2);
  redeem_pledge (pool_done p) (qsv 3);
  redeem_pledge (pool_done p) (qsv 4);
  drop_ (pool_done p);
  ()
}
```
