(* The same program as [SzWidth], extracted with --custard_sizet_width 32.
   A separate module because a test's name is its entry module's name. *)
module SzWidth32

let main () : FStar.All.ML Int32.t = SzWidth.main ()
