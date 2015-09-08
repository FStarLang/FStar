open CBuffer

type fd = Unix.file_descr
type buffer = { content : bytes; start_idx : int; length : int;}

external ocaml_writev: fd -> buffer array -> int -> int = "ocaml_writev"
external ocaml_readv: fd -> buffer array -> int -> int = "ocaml_readv"

let char_array_to_bytes a b idx len =
  for i = 0 to len - 1 do
    Bytes.set b i a.(i+idx)
  done

let bytes_to_char_array a b idx len =
  for i = 0 to len - 1 do
    a.(i+idx) <- Bytes.get b i
  done

let cbuffer_to_buffer (cbuff:CBuffer.buffer) =
  let tot_len = Array.length cbuff.content in
  let c = Bytes.create tot_len in
  char_array_to_bytes cbuff.content c 0 tot_len;
  let (buff:buffer) = { content = c;
                        start_idx = cbuff.start_idx;
                        length = cbuff.length; } in
  buff

type open_flag =
  | READ_ONLY
  | WRITE_ONLY
  | READ_WRITE
  | APPEND
  | CREATE

let map_flag f =
  match f with
  | READ_ONLY -> Unix.O_RDONLY
  | WRITE_ONLY -> Unix.O_WRONLY
  | READ_WRITE -> Unix.O_RDWR
  | APPEND -> Unix.O_APPEND
  | CREATE -> Unix.O_CREAT
  | _ -> failwith "Unhandled flag"

(* Hack : converts (array char) ~> bytes and back *)
(* TODO : better hack with bigarray ? *)
let read f (b:CBuffer.buffer) idx len =
  let buff = Bytes.create len in
  let n = Unix.read f buff 0 len in
  bytes_to_char_array b.content buff b.start_idx b.length;
  n

(* TODO: same as read so that it works *)
let write = Unix.write

let openfile f l i = Unix.openfile f (List.map map_flag l) i
let close = Unix.close

(* TODO : test *)
let readv fd buffers =
  let buffs = Array.of_list buffers in
  let buff_len = Array.length buffs in
  let buffs = Array.map cbuffer_to_buffer buffs in
  ocaml_readv fd buffs buff_len

(* Conversions and call to C writev function *)
let writev fd (buffers:CBuffer.buffer list) =
  let buffs = Array.of_list buffers in
  let buff_len = Array.length buffs in
  let buffs = Array.map cbuffer_to_buffer buffs in
  ocaml_writev fd buffs buff_len


(*
TODO : implement these functions 
let get_inet_tcp_socket = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:get_inet_tcp_socket"))

let accept = (fun ( f ) -> (Support.All.failwith "Not yet implemented:accept"))

let bind = (fun ( _ ) ( _ ) ( _ ) -> (Support.All.failwith "Not yet implemented:bind"))

let listen = (fun ( _ ) ( _ ) -> (Support.All.failwith "Not yet implemented:listen"))
*)
