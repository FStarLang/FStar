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

module Promises.Examples3

open Pulse.Lib.Pervasives
open Pulse.Lib.Par.Pledge
open Pulse.Lib.InvList
module GR = Pulse.Lib.GhostReference

assume val done : ref bool
assume val res : ref (option int)
assume val claimed : GR.ref bool

let inv_p : vprop =
  exists* (v_done:bool) (v_res:option int) (v_claimed:bool).
       pts_to done #one_half v_done
    ** pts_to res #one_half v_res
    ** GR.pts_to claimed #one_half v_claimed
    ** (if not v_claimed then pts_to res #one_half v_res else emp)
    ** pure (v_claimed ==> v_done)
    ** pure (v_done ==> Some? v_res)

let goal : vprop =
  exists* v_res. pts_to res #one_half v_res ** pure (Some? v_res)


```pulse
atomic
fn proof
   (i : inv inv_p) (_:unit)
   requires pts_to done #one_half true ** GR.pts_to claimed #one_half false
   ensures pts_to done #one_half true ** goal
   opens add_inv emp_inames i
{
  with_invariants i {
    unfold inv_p;
    with v_done v_res v_claimed.
      assert (pts_to done #one_half v_done
              ** pts_to res #one_half v_res
              ** GR.pts_to claimed #one_half v_claimed
              ** (if not v_claimed then pts_to res #one_half v_res else emp)
              ** pure (v_claimed ==> v_done)
              ** pure (v_done ==> Some? v_res));

    pts_to_injective_eq #_ #one_half #one_half #v_done #true done;
    assert (pure (v_done == true));
    
    GR.gather2 #bool
      claimed
      #false #v_claimed;
    assert (pure (v_claimed == false));

    // NB: this step is very sensitive to ordering
    rewrite ((if not v_claimed then pts_to res #one_half v_res else emp) ** emp)
         as (pts_to res #one_half v_res ** (if not true then pts_to res #one_half v_res else emp));

    GR.op_Colon_Equals claimed true;
    
    fold goal;
    
    GR.share2 #_ claimed;
    
    fold inv_p;
    
    drop_ (GR.pts_to claimed #one_half true);

    ()
  }
}
```

let cheat_proof (i:inv inv_p)
  : (_:unit) ->
      stt_ghost unit
        (requires         invlist_v [(| _, i |)] ** (pts_to done #one_half true ** GR.pts_to claimed #one_half false))
        (ensures fun _ -> invlist_v [(| _, i |)] ** (pts_to done #one_half true ** goal))
  = admit() //proof is atomic, not ghost

#set-options "--debug Promises.Examples3 --debug_level SMTQuery"

```pulse
fn setup (_:unit)
   requires pts_to done v_done ** pts_to res v_res ** GR.pts_to claimed v_claimed
   returns i:inv inv_p
   ensures pts_to done #one_half false ** pledge (add_one (|inv_p, i|) []) (pts_to done #one_half true) goal
{
  done := false;
  res := None;
  GR.op_Colon_Equals claimed false;
  
  share2 #_ done;
  share2 #_ res;
  GR.share2 #_ claimed;
  
  rewrite (pts_to res #one_half None)
       as (if not false then  pts_to res #one_half None else emp);
       
  fold inv_p;
  
  let i = new_invariant inv_p;
  
  make_pledge
    (add_one (|inv_p, i|) [])
    (pts_to done #one_half true)
    goal
    (GR.pts_to claimed #one_half false)
    (cheat_proof i);

  i
}
```

[@@expect_failure] // block is not atomic/ghost
```pulse
fn worker (i : inv inv_p) (_:unit)
   requires pts_to done #one_half false
   ensures pts_to done #one_half true
{
  with_invariants i {
    unfold inv_p;
    with v_done v_res v_claimed.
      assert (pts_to done #one_half v_done
              ** pts_to res #one_half v_res
              ** GR.pts_to claimed #one_half v_claimed
              ** (if not v_claimed then pts_to res #one_half v_res else emp)
              ** pure (v_claimed ==> v_done)
              ** pure (v_done ==> Some? v_res));

    gather2 #_ done #false #v_done;
    assert (pts_to done false);
    
    assert (pure (not v_claimed)); // contrapositive from v_done=false

    rewrite (if not v_claimed then pts_to res #one_half v_res else emp)
         as pts_to res #one_half v_res;
         
    gather2 #_ res #v_res #v_res;
    assert (pts_to res v_res);
    
    
    (* The main sketchy part here: two steps! But we see how
    to fix this by either:
      - Adding a lock and a ghost bool reference
      - Using a monotonic reference for the result, so once we
        set it to Some we know it must remain so. This allows
        to not have a lock for this. It would be two with_invariant
        steps.
    *)
    res := Some 42;
    done := true;
    
    share2 #_ res;

    rewrite (pts_to res #one_half (Some 42))
        as (if not v_claimed then pts_to res #one_half (Some 42) else emp);
        
    share2 #_ done;
    
    fold inv_p;

    ()
  };
}
```
