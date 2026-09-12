(* Section 92.  EverParse's and Kuiper's error 390 reduced at last: the index
   is a *local let*, not a parameter substituted by beta.  [SZ.v tm] with
   [tm] bound to [16sz] is not a constant to rule 4d, because delta re-spells
   the sizet constant as [uint_to_t <lit>] rather than the lazy embedding
   section 86 taught [const_of_arg] to force.  [TmplLet2] is the same file
   without the [let], and passed throughout. *)
module TmplLet
module SZ = FStar.SizeT

[@@custard_extern "wm::nfrag<{0}>"; custard_c_header "TmplMono_stubs.h"]
assume val frag (tm: nat) : Type0

(* Not deduced from its argument, so as in [TmplMono] the factory is
   written per size on the target side; the index is here only so that the
   result can be ascribed. *)
[@@custard_extern "wm::nmk16"; custard_c_header "TmplMono_stubs.h"]
assume val mk (tm: nat) (seed: SZ.t) : FStar.All.ML (frag tm)

[@@custard_extern "wm::nfill"; custard_c_header "TmplMono_stubs.h"]
assume val fill (#tm: nat) (f: frag tm) (v: SZ.t) : FStar.All.ML unit

let go (seed: SZ.t) : FStar.All.ML unit =
  let tm = 16sz in
  let f : frag (SZ.v tm) = mk (SZ.v tm) seed in
  fill f seed

let main () : FStar.All.ML FStar.Int32.t = go 8sz; 0l
