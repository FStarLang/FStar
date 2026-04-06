module BugNBEPrimops
module T = FStar.Tactics.V2

let test () =
  assert (FStar.UInt32.lt 97ul 127ul == true)
      by (
        T.norm [primops; nbe];
        T.trefl();
        T.qed()
      )