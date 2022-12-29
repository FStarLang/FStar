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
          let x = Pulse.Steel.Wrapper.read_alt (n, r);
          Pulse.Steel.Wrapper.write (n, r, x)
    ")


%splice_t[read_alt_write_alt] (parse_and_check  "
    fun (n:Pulse.Steel.Wrapper.erased)
        (r:Pulse.Steel.Wrapper.ref)
          { Pulse.Steel.Wrapper.pts_to r n } ->
          let x = Pulse.Steel.Wrapper.read_alt (n, r);
          Pulse.Steel.Wrapper.write_alt (n, r, x)
    ")

%splice_t[swap] (parse_and_check "
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
