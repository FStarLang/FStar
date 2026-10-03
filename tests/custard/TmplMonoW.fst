(* Section 88.  Rule 4d finds a template application by looking for its head,
   and a type abbreviation is exactly what removes that head from the term.
   Kuiper reaches [wmma_fragment] through [array (fragment et FragAcc tm tn tk
   FragLAcc)], where [fragment] is an [inline_for_extraction] alias; the
   scan saw [fragment], not the template, so no demand was made, [tm] stayed
   [Poly], and error 390 fired with the index still a free variable --
   "What it reduced to was: FStar.SizeT.v tm", as against section 86's "16".

   Same file as [TmplMonoV] but for the two abbreviations in front of [frag].
   Two of them rather than one so that the rescan has to reach the template
   through an unfolding of its own result, which is what the fuel is for. *)
module TmplMonoW
module SZ = FStar.SizeT

[@@custard_extern "wm::frag<{0}>"; custard_c_header "TmplMono_stubs.h"]
assume val frag (tm: nat) : Type0

[@@custard_extern "wm::fill"; custard_c_header "TmplMono_stubs.h"]
assume val fill (#tm: nat) (f: frag tm) (v: SZ.t) : FStar.All.ML unit

[@@custard_extern "wm::mk16"; custard_c_header "TmplMono_stubs.h"]
assume val mk16 (seed: SZ.t) : FStar.All.ML (frag 16)

(* The template application is behind an [inline_for_extraction] abbreviation,
   which is how Kuiper reaches [wmma_fragment]: the term says
   [array (fragment et FragAcc tm tn tk FragLAcc)] and the head [frag] is
   nowhere in it.  Two levels, so that the rescan has to reach the second one
   through the first rather than seeing the template immediately. *)
inline_for_extraction noextract
let fragab (tm: nat) = frag tm

inline_for_extraction noextract
let fragab2 (tm: nat) = fragab tm

let g_gemm (tm: SZ.t) (f: fragab2 (SZ.v tm)) (rows: SZ.t) : FStar.All.ML unit =
  fill f rows

let dispatch (rows: SZ.t) : FStar.All.ML unit =
  let f = mk16 rows in
  g_gemm 16sz f rows

let main () : FStar.All.ML FStar.Int32.t = dispatch 8sz; 0l
