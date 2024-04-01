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

module Invariant

// #set-options "--error_contexts true"
// #set-options "--print_implicits --print_universes"
// #set-options "--ext pulse:guard_policy=SMTSync"
// #set-options "--debug Invariant --debug_level SMTQuery"

// #set-options "--trace_error"
open Pulse.Lib.Pervasives
open Pulse.Lib.Reference
open Pulse.Lib

assume val p : vprop
assume val q : vprop
assume val r : vprop

assume val f () : stt_atomic unit emp_inames (p ** q) (fun _ -> p ** r)

```pulse
atomic
fn g (i:iname_ref)
  requires ((i -~- p) ** q)
  ensures (r ** (i -~- p))
  opens (add_inv emp_inames i)
{
  with_invariants i {
    f ()
  }
}
```

assume val f_ghost () : stt_ghost unit emp_inames (p ** q) (fun _ -> p ** r)

```pulse
ghost
fn g_ghost (i:iname_ref)
  requires ((i -~- p) ** q)
  ensures (r ** (i -~- p))
  opens (add_inv emp_inames i)
{
  with_invariants i {
    f_ghost ()
  }
}
```

// let test (i:inv emp) = assert (
//   (add_inv emp_inames i)
//   ==
//   ((join_inames (((add_inv #emp) emp_inames) i)) emp_inames)
// )

// assume
// val atomic_write_int (r : ref int) (v : int) :
//   stt_atomic unit emp_inames (exists* v0. pts_to r v0) (fun _ -> pts_to r v)

// ```pulse
// atomic
// fn test_atomic (r : ref int)
//   requires pts_to r 'v
//   ensures pts_to r 0
// {
//   atomic_write_int r 0;
// }
// ```

// assume
// val unobservable_write_int (r : ref int) (v : int) :
//   stt_atomic unit #Unobservable emp_inames (exists* v0. pts_to r v0) (fun _ -> pts_to r v)

// ```pulse
// unobservable
// fn test_unobservable (r : ref int)
//   requires pts_to r 'v
//   ensures pts_to r 0
// {
//   unobservable_write_int r 0;
// }
// ```

// ```pulse
// fn package (r:ref int)
//    requires pts_to r 123
//    returns i : inv (pts_to r 123)
//    ensures emp
// {
//   let i : inv (pts_to r 123) = new_invariant (pts_to r 123);
//   i
// }
// ```

// // Fails as it is not atomic
// [@@expect_failure]
// ```pulse
// fn test2 ()
//   requires emp
//   ensures emp
// {
//   let r = alloc #int 123;
//   let i : inv (pts_to r 123) = package r;
//   with_invariants i {
//     r := 124;
//     r := 123;
//     ()
//   }
// }
// ```

//  ```pulse
//  ghost
//  fn t00 () (i:inv emp)
//    requires emp
//    ensures emp
//    opens (add_inv emp_inames i)
//  {
//   ()
//  }
// ```

// // FIXME: crashes
//  ```pulse
//  atomic
//  fn t0 () (i:inv emp)
//    requires emp
//    ensures emp
//    opens (add_inv emp_inames i)
//  {
//    with_invariants i {
//      ()
//    }
//  }
// ```


// assume val i : inv emp
// assume val i2 : inv emp


// ```pulse
// ghost
// fn basic_ghost ()
//   requires emp
//   ensures emp
// {
//   (); ()
// }
// ```

// (* Using invariants while claiming not to. *)
// [@@expect_failure]
// ```pulse
// atomic
// fn t1 ()
//   requires emp
//   ensures emp
//   opens emp_inames
// {
//   with_invariants i {
//     ()
//   }
// }
// ```

// (* Overclaiming, OK *)
// ```pulse
// atomic
// fn t3 ()
//   requires emp
//   ensures emp
//   opens (add_inv (add_inv emp_inames i) i2)
// {
//   with_invariants i {
//     ()
//   }
// }
// ```

// (* Works, no need to declare opens as its an effectful fn *)
// ```pulse
// fn t2 ()
//   requires emp
//   returns _:int
//   ensures emp
// {
//   let j = new_invariant emp;
//   with_invariants j 
//     returns _:unit
//     ensures emp {
//     ()
//   };
//   123
// }
// ```
