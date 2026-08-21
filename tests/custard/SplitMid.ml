(* Hand written, not generated: this is the shape of F*'s own realizations in
   src/ml and ulib/ml.  It refers to the Custard output of SplitLo by the
   plain names of section 12.9, which is the whole point of the test. *)
let bump x = SplitLo.add_one (SplitLo.add_one x)

let name c =
  match SplitLo.flip c with
  | SplitLo.Red -> "red"
  | SplitLo.Green -> "green"
