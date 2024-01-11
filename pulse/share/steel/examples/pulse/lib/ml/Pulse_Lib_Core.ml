let rec while_ cond body =
  let b = cond () in
  if b then (
    body ();
    while_ cond body
  ) else ()
