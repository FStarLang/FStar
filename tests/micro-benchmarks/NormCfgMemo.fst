module NormCfgMemo

let rec countdown (n:nat) : bool =
  if n = 0 then true else countdown (n-1)

(* This should be very quick, it takes ~140ms in my current
setup. Before fixing the cfg check in Normalizer.read_memo,
this would take much longer, possibly hours. *)
let _ = assert_norm (countdown 20000)
