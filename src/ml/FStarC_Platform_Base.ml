type sys =
  | Unix
  | Win32
  | Cygwin

let system =
  match Sys.os_type with
  | "Unix" -> Unix
  | "Win32" -> Win32
  | "Cygwin" -> Cygwin
  | s -> failwith ("Unrecognized system: " ^ s)

let kernel () : string =
  try
    List.hd (Process.read_stdout "uname" [| |])
  with
  | _ -> Sys.os_type
