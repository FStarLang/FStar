(** Cleanup interactive transcript received on standard input.

This mostly consists in pretty-pretting JSON messages and sorting their
fields, to permit text-based comparisons against reference transcripts.

Usage: ocaml cleanup.ml < dirty > clean *)

#use "topfind";;
#require "yojson";;

let cleanup_one line =
  let open Yojson.Safe in
  try
    to_string (sort (from_string line))
  with Yojson.Json_error _ -> line

let _ =
  try
    while true do
      print_string (cleanup_one (read_line ()));
      print_newline ();
    done
  with _ -> ()
