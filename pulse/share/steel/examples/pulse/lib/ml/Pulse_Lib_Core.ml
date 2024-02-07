let while_ cond body =
  while (cond ()) do
    body ()
  done
