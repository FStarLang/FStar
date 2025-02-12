(*
   Copyright 2008-2024 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStarC.Find.Z3

open FStarC
open FStarC.Effect
open FStarC.List
module BU = FStarC.Util
module Find = FStarC.Find

open FStarC.Class.Show

let z3url = "https://github.com/Z3Prover/z3/releases"

let packaged_z3_versions = ["4.8.5"; "4.13.3"]

let z3_install_suggestion (v : string) : list Pprint.document =
  let open FStarC.Errors.Msg in
  let open FStarC.Pprint in
  [
    prefix 4 1 (text <| BU.format1 "Please download version %s of Z3 from" v)
              (url z3url) ^/^
      group (text "and install it into your $PATH as" ^/^ squotes
        (doc_of_string (Platform.exe ("z3-" ^ v))) ^^ dot);
    if List.mem v packaged_z3_versions then
      text <| BU.format1 "Version %s of Z3 should be included in binary packages \
              of F*. If you are using a binary package and are seeing
              this error, please file a bug report." v
    else
      empty
  ]

(* Check if [path] is potentially a valid z3, by trying to run
it with -version and checking for non-empty output. Alternatively
we could call [which] on it (if it's not an absolute path), but
we shouldn't rely on the existence of a binary which. *)
let z3_inpath (path:string) : bool =
  try
    let s = BU.run_process "z3_pathtest" path ["-version"] None in
    s <> ""
  with
  | _ -> false

(* Find the Z3 executable that we should invoke for a given version.

- If the user provided the --smt option, use that binary unconditionally.
- We then look in $LIB/z3-VER/z3, where LIB is the F* library root, for example
  /usr/local/lib/fstar/z3-4.8.5/bin/z3, for an installed package. We ship Z3 4.8.5
  and 4.13.3 in the binary package in these paths, so F* automatically find them
  without relying on PATH or adding more stuff to the user's /usr/local/bin.
  Each $PREFIX/lib/fstar/z3-VER directory roughly contains an extracted Z3
  binary package, but with many files removed (currently we just keep LICENSE
  and the executable).

- Else we check the PATH:
  - If z3-VER (or z3-VER.exe) exists in the PATH use it.
  - Otherwise, default to "z3" in the PATH.

We cache the chosen executable for every Z3 version we've ran.
*)
let do_locate_z3 (v:string) : option string =
  let open FStarC.Class.Monad in
  let guard (b:bool) : option unit = if b then Some () else None in
  let (<|>) o1 o2 () =
    match o1 () with
    | Some v -> Some v
    | None -> o2 ()
  in
  let path =
    let in_lib () : option string =
      let! root = Find.lib_root () in
      let path = Platform.exe (root ^ "/z3-" ^ v ^ "/bin/z3") in
      let path = Filepath.normalize_file_path path in
      guard (Filepath.file_exists path);!
      Some path
    in
    let from_path (cmd : string) () =
      let cmd = Platform.exe cmd in
      guard (z3_inpath cmd);!
      Some cmd
    in
    (Options.smt <|>
    in_lib <|>
    from_path ("z3-" ^ v) <|>
    from_path "z3" <|> (fun _ -> None)) ()
  in
  if Debug.any () then
    BU.print2 "do_locate_z3(%s) = %s\n" (Class.Show.show v) (Class.Show.show path);
  path

let locate_z3 (v : string) : option string =
  let cache : SMap.t (option string) = SMap.create 5 in
  let find_or (k:string) (f : string -> option string) : option string =
    match SMap.try_find cache k with
    | Some v -> v
    | None ->
      let v = f k in
      SMap.add cache k v;
      v
  in
  find_or v do_locate_z3
