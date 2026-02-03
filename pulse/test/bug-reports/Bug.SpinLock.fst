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

module Bug.SpinLock
#lang-pulse
open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference
open Pulse.Lib.SpinLock

let test_fstar (r:R.ref int) =
  let my_lock = new_lock (exists* v. R.pts_to r v) in
  ()


fn lock_ref (r:R.ref int) (#v_:Ghost.erased int)
  requires R.pts_to r v_
  returns l:lock
  ensures lock_alive l (exists* v. R.pts_to r v)
{
  new_lock (exists* v. R.pts_to r v)
}


[@@expect_failure]

fn create_and_lock_ref ()
{
  let mut r = 0;
  let my_lock = new_lock (exists* v. R.pts_to r v);
  ()
}

