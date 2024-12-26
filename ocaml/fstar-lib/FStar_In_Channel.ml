(*
   Copyright 2024 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: Brian G. Milnes 
*)

open In_channel
type t = In_channel.t

(*
   As In_channel.t are the subtypes here:
   of_t maps In_channel t to t        - used on the outputs
   to_t maps t      to In_channel.t   - used on the inputs
*)

let of_char c : FStar_Char.char = FStar_Char.char_of_u32 (Stdint.Uint32.of_int (Char.code c)) 
let to_char c : char = Char.chr (Z.to_int (FStar_Char.int_of_char c))

type open_flag = | Open_rdonly | Open_wronly | Open_append | Open_creat | Open_trunc   
  | Open_excl | Open_binary    | Open_text   | Open_nonblock

let to_open_flag (o : open_flag) =
  match o with
  | Open_rdonly   -> In_channel.Open_rdonly 
  | Open_wronly   -> In_channel.Open_wronly 
  | Open_append   -> In_channel.Open_append 
  | Open_creat    -> In_channel.Open_creat 
  | Open_trunc    -> In_channel.Open_trunc   
  | Open_excl     -> In_channel.Open_excl 
  | Open_binary   -> In_channel.Open_binary    
  | Open_text     -> In_channel.Open_text   
  | Open_nonblock -> In_channel.Open_nonblock

let of_open_flag (o: In_channel.open_flag) =
  match o with
  | In_channel.Open_rdonly   -> Open_rdonly 
  | In_channel.Open_wronly   -> Open_wronly 
  | In_channel.Open_append   -> Open_append 
  | In_channel.Open_creat    -> Open_creat 
  | In_channel.Open_trunc    -> Open_trunc   
  | In_channel.Open_excl     -> Open_excl 
  | In_channel.Open_binary   -> Open_binary    
  | In_channel.Open_text     -> Open_text   
  | In_channel.Open_nonblock -> Open_nonblock

let of_list_open_flag lof = List.map of_open_flag lof
let to_list_open_flag lof = List.map to_open_flag lof

let stdin          = In_channel.stdin
let open_bin       = In_channel.open_bin
let open_text      = In_channel.open_text
let with_open_bin  = In_channel.with_open_bin
let with_open_text = In_channel.with_open_text

let open_gen ofl i s = In_channel.open_gen (to_list_open_flag ofl) i s
let with_open_gen ofl i s fn = 
  In_channel.with_open_gen (to_list_open_flag ofl) i s fn

let close                = In_channel.close
let close_noerr          = In_channel.close_noerr
let input_char t         =
  match In_channel.input_char t with
  | None -> None
  | Some c -> Some (of_char c)

let input_byte           = In_channel.input_byte
let input_line           = In_channel.input_line
let really_input_string  = In_channel.really_input_string
let input_all            = In_channel.input_all

let input t (start: Z.t) (len : Z.t) : Z.t * FStar_Bytes.bytes = 
  let len'   = Z.to_int len      in
  let start' = Z.to_int start    in
  let bs'    = Bytes.create len' in
  let read   = In_channel.input t bs' start' len' in
    (Z.of_int read, Bytes.to_string bs')

(* unit option here is kinda silly, it could be a bool. *)
let really_input t pos len : (unit option * FStar_Bytes.bytes)   = 
  let bs   = Bytes.create len in
  let read = In_channel.really_input t bs pos len in
   (read, Bytes.to_string bs)

let seek             = In_channel.seek
let pos              = In_channel.pos
let length           = In_channel.length
let set_binary_mode  = In_channel.set_binary_mode
