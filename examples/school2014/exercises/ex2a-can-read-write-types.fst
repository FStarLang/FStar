module ACLs
  type filename = string

  val canWrite : unit (* write a correct and precise type here *)
  let canWrite f = 
    match f with 
      | "C:/temp/tempfile" -> true
      | _ -> false

  val canRead : unit (* write correct and precise type here *)
  let canRead f = 
    canWrite f || f="C:/public/README"
