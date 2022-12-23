module Pulse.Tests
module T = FStar.Tactics
open Pulse.Steel.Wrapper
open Pulse.Syntax
open Pulse.Main

%splice_t[foo] (parse_and_check "true")

%splice_t[read] (parse_and_check "
  fun (n:Pulse.Steel.Wrapper.erased)
      (r:Pulse.Steel.Wrapper.ref)
        {Pulse.Steel.Wrapper.pts_to r n} ->
        Pulse.Steel.Wrapper.read (n, r)
  ")

%splice_t[read_alt_with_post] (parse_and_check "
  fun (n:Pulse.Steel.Wrapper.erased)
      (r:Pulse.Steel.Wrapper.ref)
        {Pulse.Steel.Wrapper.pts_to r n}
        {_.Pulse.Steel.Wrapper.pts_to r n} ->
        Pulse.Steel.Wrapper.read_alt (n, r)
  ")

%splice_t[read_alt_with_post2] (parse_and_check "
  fun (n:Pulse.Steel.Wrapper.erased)
      (r1:Pulse.Steel.Wrapper.ref)
      (r2:Pulse.Steel.Wrapper.ref)
        {Pulse.Steel.Wrapper.pts_to r1 n * Pulse.Steel.Wrapper.pts_to r2 n}
        {_.Pulse.Steel.Wrapper.pts_to r1 n * Pulse.Steel.Wrapper.pts_to r2 n} ->
        Pulse.Steel.Wrapper.read_alt (n, r2)
  ")

%splice_t[read_refine] (parse_and_check "
   fun (n:Pulse.Steel.Wrapper.erased)
       (r:Pulse.Steel.Wrapper.ref)
         {Pulse.Steel.Wrapper.pts_to r n} ->
         Pulse.Steel.Wrapper.read_refine (n, r)
   ")

 %splice_t[write] (parse_and_check "
  fun (n:Pulse.Steel.Wrapper.erased)
      (r1:Pulse.Steel.Wrapper.ref)
      (x:Pulse.Steel.Wrapper.u32)
      (r2:Pulse.Steel.Wrapper.ref)
        {Pulse.Steel.Wrapper.pts_to r1 n * Pulse.Steel.Wrapper.pts_to r2 n} ->
        Pulse.Steel.Wrapper.write (n, r2, x)
  ")

//Bound variable escapes scope
[@@ expect_failure]
%splice_t[read_alt_write] (parse_and_check  "
    fun (n:Pulse.Steel.Wrapper.erased)
        (r:Pulse.Steel.Wrapper.ref)
          { Pulse.Steel.Wrapper.pts_to r n } ->
          let x:Pulse.Steel.Wrapper.u32 = Pulse.Steel.Wrapper.read_alt (n, r);
          Pulse.Steel.Wrapper.write (n, r, x)
    ")


%splice_t[read_alt_write_alt] (parse_and_check  "
    fun (n:Pulse.Steel.Wrapper.erased)
        (r:Pulse.Steel.Wrapper.ref)
          { Pulse.Steel.Wrapper.pts_to r n } ->
          let x:Pulse.Steel.Wrapper.u32 = Pulse.Steel.Wrapper.read_alt (n, r);
          Pulse.Steel.Wrapper.write_alt (n, r, x)
    ")
