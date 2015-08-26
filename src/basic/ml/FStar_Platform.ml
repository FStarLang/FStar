let exe name =
  if Sys.unix then
    name
  else
    name^".exe"
