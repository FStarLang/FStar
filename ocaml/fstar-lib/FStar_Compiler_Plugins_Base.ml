open Dynlink

exception DynlinkError of string

let dynlink_loadfile (fname:string) : unit =
  try
    Dynlink.loadfile fname
  with Dynlink.Error e ->
    raise (DynlinkError (Dynlink.error_message e))
