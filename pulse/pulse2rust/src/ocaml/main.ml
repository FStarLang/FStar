let _ =
  if Array.length Sys.argv < 2 then
    Printf.printf "Usage: %s <file1> <file2> ...\n" Sys.argv.(0)
  else
  let files = Array.sub Sys.argv 1 (Array.length Sys.argv - 1) in
  Pulse2Rust.extract (Array.to_list files)
  
  (* Pulse2Rust.test_rust() *)