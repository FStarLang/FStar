(*
List fstarlib files not included in the compiler.

We need this to compile a clean version of fstar-tactics-lib, containing no
duplicate copies of modules included in the compiler.

Usage: ocaml fstarlib_leftovers.ml {+|-}dir1 {+|-}dir2 ...

NOTE: each dir MUST NOT end with / or \
*)

let starts_with input prefix =
  let len_prefix = String.length prefix in
  String.length input >= len_prefix &&
  String.sub input 0 len_prefix = prefix

let libs marker exts =
  let len_marker = String.length marker in
  Array.fold_left
    (fun accu folder ->
      if starts_with folder marker
      then
        let folder = String.sub folder len_marker (String.length folder - len_marker) in
        if Sys.file_exists folder && Sys.is_directory folder
	then
	  Array.fold_left
	    (fun accu fname ->
	      let name = Filename.remove_extension fname in
	      let ext = Filename.extension fname in
              if List.mem ext exts
              then
                (name, Filename.concat folder fname) :: accu
              else
                accu	    
	    )
	    accu
	    (Sys.readdir folder)
	else
          accu
      else
        accu  
    )
    []
    Sys.argv

let _ =
  let excluded = List.map fst (libs "-" [".cmi"]) in
  List.iter
    (fun (name, path) ->
      if not (List.mem name excluded)
      then print_endline path
    )
    (libs "+" [".ml"])
