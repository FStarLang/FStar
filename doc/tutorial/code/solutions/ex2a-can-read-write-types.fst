module ACLs
  type filename = string

  val canWrite : filename -> Tot bool
  let canWrite f = 
    match f with 
      | "C:/temp/tempfile" -> true
      | _ -> false

  val canRead : filename -> Tot bool
  let canRead f = 
    canWrite f || f="C:/public/README"
