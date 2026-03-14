
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

(* Compute a relative path from base_dir to target_path.
   Both paths should be absolute. Returns a relative path if they share
   a common prefix; otherwise returns the target unchanged. *)
let make_relative_to (base_dir:string) (target_path:string) : string =
  (* Normalize paths to use forward slashes *)
  let normalize_sep s = 
    if FStarC_Platform.windows 
    then BatString.nreplace ~str:s ~sub:"\\" ~by:"/"
    else s
  in
  let base_dir = normalize_sep base_dir in
  let target_path = normalize_sep target_path in
  
  (* Split paths into components *)
  let split_path s = 
    BatString.nsplit s "/" 
    |> List.filter (fun x -> x <> "") 
  in
  let base_parts = split_path base_dir in
  let target_parts = split_path target_path in
  
  (* Find common prefix length *)
  let rec common_prefix_len acc b t =
    match b, t with
    | bh :: bt, th :: tt when String.lowercase_ascii bh = String.lowercase_ascii th ->
        common_prefix_len (acc + 1) bt tt
    | _ -> acc
  in
  let prefix_len = common_prefix_len 0 base_parts target_parts in
  
  (* If no common prefix, return target as-is *)
  if prefix_len = 0 then target_path
  else
    (* Compute relative path *)
    let base_remaining = List.length base_parts - prefix_len in
    let target_remaining = BatList.drop prefix_len target_parts in
    let ups = List.init base_remaining (fun _ -> "..") in
    let rel_parts = ups @ target_remaining in
    if rel_parts = [] then "."
    else String.concat "/" rel_parts

