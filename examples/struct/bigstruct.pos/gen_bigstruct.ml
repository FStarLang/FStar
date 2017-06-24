#!/usr/bin/env ocaml

#use "topfind";;
#require "mustache";;

let tmpl_file, n =
  match Sys.argv |> Array.to_list with
  | _ :: tmpl :: ns :: [] -> tmpl, int_of_string ns
  | _ ->
    Printf.printf "usage: %s template n" Sys.argv.(0);
    exit 1

let file_contents filename =
  let chan = open_in filename in
  let len = in_channel_length chan in
  let s = String.make (len+1) '\n' in
  ignore (input chan s 0 len);
  close_in chan;
  s


let tmpl =
  file_contents tmpl_file
  |> Mustache.of_string

let j =
  `O ["iter", `A (Array.init n (fun i -> `O ["i", `Float (float_of_int (i+1))])
                  |> Array.to_list);
      "n", `Float (float_of_int n)
     ]

let () =
  Mustache.render ~strict:true tmpl j
  |> print_endline
