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
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Pledge
module R  = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference

assume val done : ref bool
assume val res : ref (option int)
assume val claimed : GR.ref bool

let inv_p : timeless_slprop =
  exists* (v_done:bool) (v_res:option int) (v_claimed:bool).
       pts_to done #0.5R v_done
    ** pts_to res #0.5R v_res
    ** pts_to claimed #0.5R v_claimed
    ** (if not v_claimed then R.pts_to res #0.5R v_res else emp) // FIXME: cannot use pts_to method or a fold fails; missing unfold?
    ** pure (v_claimed ==> v_done)
    ** pure (v_done ==> Some? v_res)

(* Explicit introduction for inv_p, sometimes needed to disambiguate. *)

ghost
fn intro_inv_p (v_done:bool) (v_res:option int) (v_claimed:bool)
  requires
       pts_to done #0.5R v_done
    ** pts_to res #0.5R v_res
    ** pts_to claimed #0.5R v_claimed
    ** (if not v_claimed then pts_to res #0.5R v_res else emp)
    ** pure (v_claimed ==> v_done)
    ** pure (v_done ==> Some? v_res)
  ensures inv_p
{
  (* Unfortunate... does not happen automatically since we don't unfold
  under a match. *)
  rewrite (if not v_claimed then pts_to res #0.5R v_res else emp)
       as (if not v_claimed then R.pts_to res #0.5R v_res else emp);
  fold inv_p;
}


let goal : slprop =
  exists* v_res. pts_to res #0.5R v_res ** pure (Some? v_res)



atomic
fn proof
   (i : iname) (_:unit)
   requires inv i inv_p ** pts_to done #0.5R true ** pts_to claimed #0.5R false
   ensures inv i inv_p ** pts_to done #0.5R true ** goal
   opens [i]
{
  with_invariants i {
    later_elim_timeless _;
    unfold inv_p;
    with (v_done : bool) v_res v_claimed.
      assert (pts_to done #0.5R v_done
              ** pts_to done #0.5R true
              ** pts_to res #0.5R v_res
              ** pts_to claimed #0.5R v_claimed
              ** (if not v_claimed then R.pts_to res #0.5R v_res else emp)
              ** pure (v_claimed ==> v_done)
              ** pure (v_done ==> Some? v_res));

    pts_to_injective_eq #_ #0.5R #0.5R #v_done #true done;
    assert (pure (v_done == true));
    
    GR.gather2 #bool
      claimed
      #false #v_claimed;
    assert (pure (v_claimed == false));

    // NB: this step is very sensitive to ordering
    rewrite ((if not v_claimed then R.pts_to res #0.5R v_res else emp) ** emp)
         as (R.pts_to res #0.5R v_res ** (if not true then pts_to res #0.5R v_res else emp));

    GR.op_Colon_Equals claimed true;
    
    fold goal;
    
    GR.share2 #_ claimed;
    
    // If we just try to:
    //   fold inv_p;
    // we get:
    //   - Cannot prove:
    //       pts_to done ?v_done
    //   - In the context:
    //       goal **
    //       pts_to done (reveal v_done) **
    //       pts_to done true **
    //       pts_to claimed true
    // since the choice of ?v_done is ambiguous. Further, we don't have a
    // way of saying "fold using the (pts_to done v_done)", or "fold ignoring
    // the pts_to done true". So we use the explicit introduction.
    intro_inv_p v_done v_res true;
    
    drop_ (pts_to claimed #0.5R true);

    later_intro inv_p;

    ()
  }
}


let cheat_proof (i:iname)
  : (_:unit) ->
      stt_ghost unit (add_inv emp_inames i)
        (requires pts_to done #0.5R true ** (inv i inv_p ** pts_to claimed #0.5R false))
        (ensures fun _ -> pts_to done #0.5R true ** goal)
  = admit() //proof is atomic, not ghost

// #set-options "--debug SMTQuery"


fn setup (_:unit)
   requires pts_to done 'v_done ** pts_to res 'v_res ** pts_to claimed 'v_claimed
   returns i:iname
   ensures pts_to done #0.5R false **
           pledge (add_inv emp_inames i) (pts_to done #0.5R true) goal
{
  done := false;
  res := None;
  GR.op_Colon_Equals claimed false;
  
  share2 #_ done;
  share2 #_ res;
  GR.share2 #_ claimed;
  
  rewrite (pts_to res #0.5R None)
       as (if not false then pts_to res #0.5R None else emp);
       
  fold inv_p;
  
  let i = new_invariant inv_p;
  inames_live_inv i inv_p;
  GhostSet.lemma_equal_intro (add_inv emp_inames i) (single i);
  make_pledge
    (add_inv emp_inames i)
    (pts_to done #0.5R true) //f
    goal  //v
    (inv i inv_p ** pts_to claimed #0.5R false)  //extra
    (cheat_proof i);

  i
}


[@@expect_failure] // block is not atomic/ghost

fn worker (i : iname) (_:unit)
   requires inv i inv_p ** pts_to done #0.5R false
   ensures  inv i inv_p ** pts_to done #0.5R true
{
  with_invariants i {
    later_elim_storable _;
    unfold inv_p;
    with v_done v_res v_claimed.
      assert (pts_to done #0.5R v_done
              ** pts_to done #0.5R false
              ** pts_to res #0.5R v_res
              ** pts_to claimed #0.5R v_claimed
              ** (if not v_claimed then pts_to res #0.5R v_res else emp)
              ** pure (v_claimed ==> v_done)
              ** pure (v_done ==> Some? v_res));

    gather2 #_ done #false #v_done;
    assert (pts_to done false);
    
    assert (pure (not v_claimed)); // contrapositive from v_done=false

    rewrite (if not v_claimed then pts_to res #0.5R v_res else emp)
         as pts_to res #0.5R v_res;
         
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

    rewrite (pts_to res #0.5R (Some 42))
        as (if not v_claimed then pts_to res #0.5R (Some 42) else emp);
        
    share2 #_ done;
    
    fold inv_p;

    ()
  };
}

