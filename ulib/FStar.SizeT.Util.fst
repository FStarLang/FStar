module FStar.SizeT.Util

open FStar.SizeT

let size_t_max = 0xffffsz //This is a safe platform-independent upper bound for size_t

let safe_add (x y:t) : o:option t { Some? o ==> v (Some?.v o) == v x + v y } =
  if x <^ size_t_max && y <^ size_t_max
  then (
    if y <^ (size_t_max -^ x)
    then Some (x +^ y)
    else None
  )
  else None