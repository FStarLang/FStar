(*
   Copyright 2008-2026 Microsoft Research

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
module FStarC.Getopt

(* The Cherry implementation: the OCaml one, with the command line of
   ulib/c/cherry.c. *)

open FStarC.Effect
open FStarC.BaseTypes
module I = FStarC.SmallInt
module S = FStarC.String

let noshort = FStar.Char.char_of_int 0
let nolong = ""

private
let bind (r:parse_cmdline_res) (f:unit -> ML parse_cmdline_res) : ML parse_cmdline_res =
  match r with
  | Error _ -> r
  | _ -> f ()

(* None if [s] is not an option (does not start with "-").  Otherwise
   Some (o, strim), where [strim] is [s] without its dashes and [o] is the
   matching spec, if any (none should trigger an error). *)
private
let find_matching_opt (specs:list opt) (s:string) : ML (option (option opt & string)) =
  let len = S.byte_length s in
  if I.(len < of_int 2) then None
  else if S.byte_substring s I.zero (I.of_int 2) = "--" then
    let strim = S.byte_substring s (I.of_int 2) len in
    Some (FStarC.List.tryFind (fun (_, option, _) -> option = strim) specs, strim)
  else if S.byte_at s I.zero = I.of_char '-' then
    let strim = S.byte_substring s I.one len in
    Some (FStarC.List.tryFind (fun (shortoption, _, _) -> S.string_of_list [shortoption] = strim) specs, strim)
  else None

(* remark: doesn't work with files starting with -- *)
private
let rec parse (opts:list opt) (def:string -> ML parse_cmdline_res) (args:list string)
  : ML parse_cmdline_res =
  match args with
  | [] -> Success
  | arg :: rest ->
    match find_matching_opt opts arg with
    | None -> bind (def arg) (fun () -> parse opts def rest)
    | Some (None, _) -> Error ("unrecognized option '" ^ arg ^ "'\n", arg)
    | Some (Some (_, opt, ZeroArgs f), _) -> f (); parse opts def rest
    | Some (Some (_, opt, OneArg (f, _)), argtrim) ->
      match rest with
      | [] -> Error ("last option '" ^ argtrim ^ "' takes an argument but has none\n", opt)
      | a :: rest ->
        let r =
          try f a; Success
          with _ -> Error ("wrong argument given to option `" ^ argtrim ^ "`\n", opt)
        in
        bind r (fun () -> parse opts def rest)

(* In ulib/c/cherry.c: main's argc and argv. *)
[@@custard_extern "cherry_argc"]
private assume val c_argc : unit -> int
[@@custard_extern "cherry_argv"]
private assume val c_argv : int -> string

private
let argv () : ML (list string) =
  let rec go (i:nat) (acc:list string) : Tot (list string) (decreases i) =
    if i = 0 then acc else go (i - 1) (c_argv (i - 1) :: acc) in
  let n = c_argc () in
  go (if n < 0 then 0 else n) []

let parse_cmdline specs others =
  match argv () with
  | [] | [_] -> Empty
  | _ :: args -> parse specs others args

(* Splits [str] into arguments at spaces and tabs, except between single
   quotes: [a 'b c' d] is [a], [b c] and [d]. *)
private
let split_quoted (str:string) : option (list string) =
  let split_spaces (s:string) = List.Tot.filter (fun s -> s <> "") (S.split [' '; '\t'] s) in
  let rec go (pieces:list string) : Tot (option (list string)) (decreases pieces) =
    match pieces with
    | [] -> Some []
    | [unquoted] -> Some (split_spaces unquoted)
    | unquoted :: quoted :: pieces ->
      match go pieces with
      | None -> None
      | Some rest -> Some (split_spaces unquoted @ quoted :: rest)
  in
  match S.split_on_string str "'" with
  | [] -> Some []
  | pieces ->
    (* an even number of pieces means an odd number of quotes *)
    if List.Tot.length pieces % 2 = 0 then None else go pieces

let parse_string specs others str =
  match split_quoted str with
  | None -> Error ("Failed to parse options; unmatched quote \"'\"", "")
  | Some args -> parse specs others args

let parse_list specs others lst = parse specs others lst

let cmdline () = argv ()
