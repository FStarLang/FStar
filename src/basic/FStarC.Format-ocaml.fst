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
module FStarC.Format

open FStarC.Effect
open FStarC.Json

[@@custard_extern "(fun () -> Unix.isatty Unix.stdout)"]
private assume val isatty : unit -> bool

(* NOTE: this is deciding whether or not to color by looking
   at stdout_isatty(), which may be a wrong choice if
   we're instead outputting to stderr. e.g.
     fstar.exe Blah.fst 2>errlog
   will colorize the errors in the file if stdout is not
   also redirected.
*)
private
let colorize_with (s:string) (oc:string & string) : string =
  if isatty () then fst oc ^ s ^ snd oc else s

[@@custard_extern "(fun s -> Stdlib.print_string s; Stdlib.flush Stdlib.stdout)"]
private assume val out_flush : string -> ML unit

[@@custard_extern "Stdlib.print_string"]
private assume val out : string -> ML unit

[@@custard_extern "(fun s -> Stdlib.prerr_string s; Stdlib.flush Stdlib.stdout; Stdlib.flush Stdlib.stderr)"]
private assume val err_flush : string -> ML unit

let default_printer = {
  printer_prinfo = out_flush;
  printer_prwarning = (fun s -> err_flush (colorize_with s ("\x1b[33;1m", "\x1b[0m")));
  printer_prerror = (fun s -> err_flush (colorize_with s ("\x1b[31;1m", "\x1b[0m")));
  printer_prgeneric = (fun label get_string get_json -> out (label ^ ": " ^ get_string ()));
}

private
let current_printer : ref printer = mk_ref default_printer

let set_printer printer = current_printer := printer

[@@custard_extern "(fun s -> Stdlib.set_binary_mode_out Stdlib.stdout true; Stdlib.print_string s; Stdlib.flush Stdlib.stdout)"]
let print_raw _ = admit ()

let print_generic label to_string to_json a =
  (!current_printer).printer_prgeneric label (fun () -> to_string a) (fun () -> to_json a)

[@@custard_extern "(fun x -> Marshal.to_string x [])"]
private assume val marshal (#a:Type) : a -> string

let print_any x = (!current_printer).printer_prinfo (marshal x)

let print_string s = (!current_printer).printer_prinfo s

[@@custard_extern "Stdlib.failwith"]
private assume val fail (#a:Type) : string -> a

private
let rec interleave (frags args:list string) : list string =
  match frags, args with
  | frag :: frags, arg :: args -> arg :: frag :: interleave frags args
  | _ -> []

let fmt spec args =
  let frags = if spec = "" then [""] else FStarC.String.split_on_string spec "%s" in
  match frags with
  | frag :: frags' ->
    if List.Tot.length frags' = List.Tot.length args
    then FStarC.String.concat "" (frag :: interleave frags' args)
    else fail ("Not enough arguments to format string " ^ spec
               ^ " : expected " ^ string_of_int (List.Tot.length frags)
               ^ " got [" ^ FStarC.String.concat ", " args
               ^ "] frags are [" ^ FStarC.String.concat ", " frags ^ "]")
  | [] -> spec

let fmt1 f a = fmt f [a]
let fmt2 f a b = fmt f [a;b]
let fmt3 f a b c = fmt f [a;b;c]
let fmt4 f a b c d = fmt f [a;b;c;d]
let fmt5 f a b c d e = fmt f [a;b;c;d;e]
let fmt6 f a b c d e g = fmt f [a;b;c;d;e;g]

let print f args = print_string (fmt f args)
let print1 a b = print_string (fmt1 a b)
let print2 a b c = print_string (fmt2 a b c)
let print3 a b c d = print_string (fmt3 a b c d)
let print4 a b c d e = print_string (fmt4 a b c d e)
let print5 a b c d e f = print_string (fmt5 a b c d e f)
let print6 a b c d e f g = print_string (fmt6 a b c d e f g)

let print_error s = (!current_printer).printer_prerror s
let print1_error a b = print_error (fmt1 a b)
let print2_error a b c = print_error (fmt2 a b c)
let print3_error a b c d = print_error (fmt3 a b c d)

let print_warning s = (!current_printer).printer_prwarning s
let print1_warning a b = print_warning (fmt1 a b)
let print2_warning a b c = print_warning (fmt2 a b c)
let print3_warning a b c d = print_warning (fmt3 a b c d)

[@@custard_extern "(fun () -> Stdlib.flush Stdlib.stdout)"]
let flush_stdout _ = admit ()

let stdout_isatty () = Some (isatty ())

let colorize s oc = colorize_with s oc
let colorize_bold s = colorize_with s ("\x1b[39;1m", "\x1b[0m")
let colorize_red s = colorize_with s ("\x1b[31;1m", "\x1b[0m")
let colorize_yellow s = colorize_with s ("\x1b[33;1m", "\x1b[0m")
let colorize_cyan s = colorize_with s ("\x1b[36;1m", "\x1b[0m")
let colorize_green s = colorize_with s ("\x1b[32;1m", "\x1b[0m")
let colorize_magenta s = colorize_with s ("\x1b[35;1m", "\x1b[0m")
