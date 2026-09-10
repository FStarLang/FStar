(* Section 92.  The other half of the local-[let] shape: the index is bound
   to a name of its own and used more than once, so it is reached after the
   binder has been opened and arrives as a free variable rather than inside
   the [let] the normalizer could have inlined. *)
module TmplLet3
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
  let n = SZ.v tm in
  let f = mk n seed in
  fill #n f seed;
  fill #n f seed

let main () : FStar.All.ML FStar.Int32.t = go 8sz; 0l
