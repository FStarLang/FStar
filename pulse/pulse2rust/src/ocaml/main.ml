let input_files = ref []
let odir = ref ""

let _ =
  (*if Array.length Sys.argv < 2 then
    Printf.printf "Usage: %s [-o <file>] <file1> <file2> ...\n" Sys.argv.(0)
  else*)
  
  let usage_msg = "Usage: main.exe [-odir ...] <file1> <file2> ..." in
  let speclist = [ ("-odir", Arg.Set_string odir, "Output directory") ] in
  let add_inp filename = input_files := filename :: !input_files in
  Arg.parse speclist add_inp usage_msg;
  (*let files = Array.sub Sys.argv 1 (Array.length Sys.argv - 1) in
  (Array.to_list files)*)
  Pulse2Rust.extract !input_files !odir
(*  match !output_file with
  | "" -> print_endline s
  | out ->
    let oc = open_out out in
    Printf.fprintf oc "%s\n" s;
    close_out oc *)
  (* Pulse2Rust.test_rust() *)