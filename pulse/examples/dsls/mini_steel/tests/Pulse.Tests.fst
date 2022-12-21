module Pulse.Tests
module T = FStar.Tactics
open Pulse.Steel.Wrapper
open Pulse.Syntax
open Pulse.Main

// %splice_t[foo] (main (Tm_Constant (Bool true)) Tm_Emp)
// %splice_t[bar] (check_bar ())
// %splice_t[baz] (check_baz ())

%splice_t[foo] (parse_and_elab ())
