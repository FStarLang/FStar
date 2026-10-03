(* Section 92.  [TmplLet] with the local [let] written out: the control that
   says the [let] is the whole difference.  This one passed throughout. *)
module TmplLet2
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
  let f : frag (SZ.v 16sz) = mk (SZ.v 16sz) seed in
  fill f seed

let main () : FStar.All.ML FStar.Int32.t = go 8sz; 0l
