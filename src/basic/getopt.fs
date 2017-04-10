(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
module FStar.Getopt
(* A simplified re-implementation of Getopt, a command line parsing tool *)
let noshort='\000'
let nolong=""

type opt_variant<'a> =
  | ZeroArgs of (unit -> 'a)
  | OneArg of (string -> 'a) * string

type opt'<'a> = char * string * opt_variant<'a> * string
type opt = opt'<unit>
type parse_cmdline_res =
  | Help
  | Error of string
  | Success

(* remark: doesn't work with files starting with -- *)
let rec parse (opts:list<opt>) def ar ix max i =
  if ix > max then Success
  else
    let arg = ar.(ix) in
    let go_on () = let _ = def arg in parse opts def ar (ix + 1) max (i + 1) in
      if String.length arg < 2 then
        go_on ()
      else
        let hd = String.sub arg 0 2 in
          if hd = "--" then
            let argtrim = String.sub arg 2 ((String.length arg) - 2) in
              match List.tryFind (fun (_, option, _, _) -> option = argtrim) opts with
                | Some (_, _, p, _) ->
                    (match p with
                       | ZeroArgs f -> f (); parse opts def ar (ix + 1) max (i + 1)
                       | OneArg (f, _) ->
                           if ix + 1 > max then Error ("last option '" + argtrim + "' takes an argument but has none\n")
                           else
                             try
                               f (ar.(ix + 1));
                               parse opts def ar (ix + 2) max (i + 1)
                             with _ ->
                                  Error ("wrong argument given to option '" + argtrim + "'\n"))
                | None -> Error ("unrecognized option '" + arg + "'\n")
          else go_on ()

let parse_cmdline specs others =
  let len = Array.length Sys.argv in
  let go_on () = parse specs others Sys.argv 1 (len - 1) 0 in
    if len = 1 then Help
    else go_on ()

let parse_string specs others (str:string) =
    let args = str.Split([|' '|]) in
    parse specs others args 0 (args.Length - 1) 0


