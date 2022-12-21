module Pulse.Tests
module T = FStar.Tactics
open Pulse.Steel.Wrapper
open Pulse.Syntax
open Pulse.Main

%splice_t[foo] (parse_and_check "true")

%splice_t[bar] (parse_and_check "\
  fun (n:Pulse.Steel.Wrapper.erased) \
      (r1:Pulse.Steel.Wrapper.ref) \
      (x:Pulse.Steel.Wrapper.u32) \
      (r2:Pulse.Steel.Wrapper.ref) \
   {Pulse.Steel.Wrapper.pts_to r1 n * Pulse.Steel.Wrapper.pts_to r2 n} -> \
      Pulse.Steel.Wrapper.write (n, r2, x) \
  ")

//Bound variable escapes scope
[@@ expect_failure]
%splice_t[baz] (parse_and_check  "\
   fun (n:Pulse.Steel.Wrapper.erased) \
       (r:Pulse.Steel.Wrapper.ref) \
         { Pulse.Steel.Wrapper.pts_to r n } -> \
         let x:Pulse.Steel.Wrapper.u32 = Pulse.Steel.Wrapper.read_alt (n, r); \
         Pulse.Steel.Wrapper.write (n, r, x) \
   ")


%splice_t[baz_alt] (parse_and_check  "\
   fun (n:Pulse.Steel.Wrapper.erased) \
       (r:Pulse.Steel.Wrapper.ref) \
         { Pulse.Steel.Wrapper.pts_to r n } -> \
         let x:Pulse.Steel.Wrapper.u32 = Pulse.Steel.Wrapper.read_alt (n, r); \
         Pulse.Steel.Wrapper.write_alt (n, r, x) \
   ")
