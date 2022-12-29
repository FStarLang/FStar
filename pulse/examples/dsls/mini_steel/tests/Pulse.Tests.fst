module Pulse.Tests
module T = FStar.Tactics
open Pulse.Steel.Wrapper
open Pulse.Syntax
open Pulse.Main

%splice_t[write] (parse_and_check "
  fun (n1:Pulse.Steel.Wrapper.erased)
      (n2:Pulse.Steel.Wrapper.erased)
      (r1:Pulse.Steel.Wrapper.ref)
      (r2:Pulse.Steel.Wrapper.ref)
        {Pulse.Steel.Wrapper.pts_to r1 n1 * Pulse.Steel.Wrapper.pts_to r2 n2}
        {_.Pulse.Steel.Wrapper.pts_to r1 n2 * Pulse.Steel.Wrapper.pts_to r2 n1} ->

        let x = Pulse.Steel.Wrapper.read_refine (n1, r1);
        let y = Pulse.Steel.Wrapper.read_refine (n2, r2);
        let z = Pulse.Steel.Wrapper.write (n1, r1, y);
        Pulse.Steel.Wrapper.write (n2, r2, x)
  ")
