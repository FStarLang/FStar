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
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Pledge
open NuPool

assume
val qsv : nat -> slprop
assume
val qsc : n:nat -> stt unit emp (fun _ -> qsv n)


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
  redeem_pledge emp_inames (pool_done p) (qsv 1);
  redeem_pledge emp_inames (pool_done p) (qsv 2);
  redeem_pledge emp_inames (pool_done p) (qsv 3);
  redeem_pledge emp_inames (pool_done p) (qsv 4);
  drop_ (pool_done p)
}



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
  join_pledge #emp_inames #(pool_done p) (qsv 1) (qsv 2);
  join_pledge #emp_inames #(pool_done p) (qsv 3) (qsv 4);
  teardown_pool p;
  redeem_pledge emp_inames (pool_done p) (qsv 1 ** qsv 2);
  redeem_pledge emp_inames (pool_done p) (qsv 3 ** qsv 4);
  drop_ (pool_done p)
}



fn qs12 (_:unit)
  requires emp
  returns _:unit
  ensures qsv 1 ** qsv 2
  {
    qsc 1;
    qsc 2
  }



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
  redeem_pledge emp_inames (pool_done p) (qsv 1 ** qsv 2);
  redeem_pledge emp_inames (pool_done p) (qsv 3);
  redeem_pledge emp_inames (pool_done p) (qsv 4);
  drop_ (pool_done p)
}



#set-options "--print_implicits"
fn qs12_par (#e:perm) (p:pool)
  requires pool_alive #e p
  returns _:unit
  ensures pool_alive #e p ** pledge emp_inames (pool_done p) (qsv 1) ** pledge emp_inames (pool_done p) (qsv 2)
  {
    spawn_ p (fun () -> qsc 1);
    spawn_ p (fun () -> qsc 2);
    ()
  }


fn qsh_par (n:nat)
  requires emp
  returns _:unit
  ensures qsv 1 ** qsv 2 ** qsv 3 ** qsv 4
{
  let p = setup_pool 42;
  share_alive p _;
  spawn_ p (fun () -> qs12_par p);
  (* Ah! This cannot work right now since we need to share part
  of the pool_alive slprop to the spawned task, so we have
  to index pool_alive with a permission, and allow
  share/gather. *)
  
  spawn_ p (fun () -> qsc 3);
  spawn_ p (fun () -> qsc 4);
  admit();
  teardown_pool p;
  redeem_pledge (pool_done p) (qsv 1)
  redeem_pledge (pool_done p) (qsv 2);
  redeem_pledge (pool_done p) (qsv 3);
  redeem_pledge (pool_done p) (qsv 4);
  drop_ (pool_done p)
}

