module Pulse.Tests
module T = FStar.Tactics
open Pulse.Steel.Wrapper
open Pulse.Syntax
open Pulse.Main

// %splice_t[foo] (main (Tm_Constant (Bool true)) Tm_Emp)
// %splice_t[bar] (check_bar ())
// %splice_t[baz] (check_baz ())

let foo_s = "true"
let bar_s = "\
fun (n:Pulse.Steel.Wrapper.erased) { emp } -> \
  (fun (r:Pulse.Steel.Wrapper.ref) { emp } -> \
    (fun (x:Pulse.Steel.Wrapper.u32) {((Pulse.Steel.Wrapper.pts_to r) (Pulse.Steel.Wrapper.reveal n))} -> \
      (Pulse.Steel.Wrapper.write (n, r, x)))) \
"

%splice_t[foo] (parse_and_check foo_s)
%splice_t[bar] (parse_and_check bar_s)
