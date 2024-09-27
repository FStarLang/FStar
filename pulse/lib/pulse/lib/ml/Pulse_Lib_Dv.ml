let while_ cond body =
  while (cond ()) do
    body ()
  done

val unreachable : unit -> 'a
let unreachable () = unreachable ()
