(* This is a slightly edited version of lib/pulse/lib/ml/Pulse_Lib_Dv.ml, to make it work in OCaml 5 (just remove the val) *)

let while_ cond body =
  while (cond ()) do
    body ()
  done

let rec unreachable () : 'a = unreachable ()
