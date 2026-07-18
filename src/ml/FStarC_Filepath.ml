
let get_file_extension (fn:string) : string = snd (BatString.rsplit fn ".")

(* NOTE: Working around https://github.com/ocaml-batteries-team/batteries-included/issues/1136 *)
let is_absolute_windows (path_str : string) : bool =
  if FStarC_Platform.windows then
    match BatString.to_list path_str with
    | '\\' :: _ -> true
    | letter :: ':' :: '\\' :: _ -> BatChar.is_letter letter
    | _ -> false
  else
    false

let is_path_absolute path_str =
  let open Batteries.Incubator in
  let open BatPathGen.OfString in
  let path = of_string path_str in
  is_absolute path || is_absolute_windows path_str

let join_paths path_str0 path_str1 =
  let open Batteries.Incubator in
  let open BatPathGen.OfString in
  let open BatPathGen.OfString.Operators in
  to_string ((of_string path_str0) //@ (of_string path_str1))

let canonicalize path_str =
  let open Batteries.Incubator in
  let open BatPathGen.OfString in
  let open BatPathGen.OfString.Operators in
  let path = of_string path_str in
  to_string (normalize_in_tree path)

let normalize_file_path (path_str:string) =
  let open Batteries.Incubator in
  let open BatPathGen.OfString in
  let open BatPathGen.OfString.Operators in
  let path = of_string path_str in
  let path =
    (* If not absolute, prepend the cwd *)
    if is_path_absolute path_str
    then path
    else
      let cwd = of_string (BatSys.getcwd ()) in
      cwd //@ path
  in
  (* Normalize *)
  to_string (normalize_in_tree path)

let basename = Filename.basename
let dirname = Filename.dirname

let getcwd = Sys.getcwd

let readdir dir = Array.to_list (Sys.readdir dir)

let paths_to_same_file f g =
  let open Unix in
  let { st_dev = i; st_ino = j } = stat f in
  let { st_dev = i'; st_ino = j' } = stat g in
  (i,j) = (i',j')

let file_exists = Sys.file_exists
(* Sys.is_directory raises Sys_error if the path does not exist *)
let is_directory f = Sys.file_exists f && Sys.is_directory f

