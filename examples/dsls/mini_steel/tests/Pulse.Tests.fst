module Pulse.Tests
module T = FStar.Tactics
open Pulse.Steel.Wrapper
open Pulse.Syntax
open Pulse.Main
open Steel.ST.Util 
open Steel.ST.Reference
open Steel.FractionalPermission
open FStar.Ghost
#push-options "--print_universes --print_implicits"

%splice_t[swap] (parse_and_check "
    fun (n1:FStar.Ghost.erased u#0 Pulse.Steel.Wrapper.u32)
        (n2:FStar.Ghost.erased u#0 Pulse.Steel.Wrapper.u32)
        (r1:Steel.ST.Reference.ref Pulse.Steel.Wrapper.u32)
        (r2:Steel.ST.Reference.ref Pulse.Steel.Wrapper.u32)
          requires (Steel.ST.Reference.pts_to #Pulse.Steel.Wrapper.u32 r1 Steel.FractionalPermission.full_perm (FStar.Ghost.reveal u#0 #Pulse.Steel.Wrapper.u32 n1) *
                    Steel.ST.Reference.pts_to #Pulse.Steel.Wrapper.u32 r2 Steel.FractionalPermission.full_perm (FStar.Ghost.reveal u#0 #Pulse.Steel.Wrapper.u32 n2))
          ensures _.(Steel.ST.Reference.pts_to #Pulse.Steel.Wrapper.u32 r1 Steel.FractionalPermission.full_perm (FStar.Ghost.reveal u#0 #Pulse.Steel.Wrapper.u32 n2) *
                     Steel.ST.Reference.pts_to #Pulse.Steel.Wrapper.u32 r2 Steel.FractionalPermission.full_perm (FStar.Ghost.reveal u#0 #Pulse.Steel.Wrapper.u32 n1)) ->

          let x = Pulse.Steel.Wrapper.read_refine r1;
          let y = Pulse.Steel.Wrapper.read_refine r2;
          Pulse.Steel.Wrapper.write r1 y;
          Pulse.Steel.Wrapper.write r2 x
    ")
