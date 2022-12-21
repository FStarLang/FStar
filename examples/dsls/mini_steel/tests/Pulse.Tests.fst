module Pulse.Tests
module T = FStar.Tactics
open Pulse.Steel.Wrapper
open Pulse.Syntax
open Pulse.Main

// %splice_t[foo] (main (Tm_Constant (Bool true)) Tm_Emp)
// %splice_t[bar] (check_bar ())
// %splice_t[baz] (check_baz ())

let foo_s = "true"
let bar_s = "
fun (n:Pulse.Steel.Wrapper.erased) (r1:Pulse.Steel.Wrapper.ref) (x:Pulse.Steel.Wrapper.u32) (r2:Pulse.Steel.Wrapper.ref) \
  {Pulse.Steel.Wrapper.pts_to r1 n * Pulse.Steel.Wrapper.pts_to r2 n} -> \
    Pulse.Steel.Wrapper.write (n, r3, x) \
"

%splice_t[foo] (parse_and_check foo_s)
%splice_t[bar] (parse_and_check bar_s)
