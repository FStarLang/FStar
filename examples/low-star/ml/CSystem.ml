open CBuffer

type fd = Unix.file_descr
type buffer = { content : bytes; start_idx : int; length : int;}

external ocaml_writev: fd -> buffer array -> int -> int = "ocaml_writev"
external ocaml_readv: fd -> buffer array -> int -> int = "ocaml_readv"

let char_array_to_bytes a =
  let b = Bytes.create (Array.length a) in
  for i = 0 to Array.length a - 1 do
    Bytes.set b i a.(i)
  done;
  b

let bytes_to_char_array a b =
  for i = 0 to Array.length a - 1 do
    a.(i) <- Bytes.get b i
  done

let cbuffer_to_buffer (cbuff:CBuffer.buffer) =
  let (buff:buffer) = { content = char_array_to_bytes cbuff.content;
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

let read f (b:CBuffer.buffer) idx len =
  let buff = char_array_to_bytes b.content in
  let n = Unix.read f buff idx len in
  print_string ("Content read : " ^ (Bytes.sub_string buff 0 n) ^ "\n");
  bytes_to_char_array b.content buff;
  n

let write = Unix.write
let openfile f l i = Unix.openfile f (List.map map_flag l) i
let close = Unix.close

let readv fd buffers =
  let buffs = Array.of_list buffers in
  let buff_len = Array.length buffs in
  ocaml_readv fd buffs buff_len

let writev fd (buffers:CBuffer.buffer list) =
  let buffs = Array.of_list buffers in
  for i = 0 to Array.length buffs - 1 do
    print_string "Buffer content :\n";
    for j = buffs.(i).start_idx to buffs.(i).start_idx + buffs.(i).length do
      print_char buffs.(i).content.(j) ;
    done;
    print_string "\n";
  done;
  let buff_len = Array.length buffs in
  let buffs = Array.map cbuffer_to_buffer buffs in
  ocaml_writev fd buffs buff_len

(*
let get_inet_tcp_socket = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:get_inet_tcp_socket"))

let accept = (fun ( f ) -> (Support.All.failwith "Not yet implemented:accept"))

let bind = (fun ( _ ) ( _ ) ( _ ) -> (Support.All.failwith "Not yet implemented:bind"))

let listen = (fun ( _ ) ( _ ) -> (Support.All.failwith "Not yet implemented:listen"))


let is_O_RDONLY = (fun ( _discr_ ) -> (match (_discr_) with
| Support.System.O_RDONLY -> begin
true
end
| _ -> begin
false
end))

let is_O_WRONLY = (fun ( _discr_ ) -> (match (_discr_) with
| Support.System.O_WRONLY -> begin
true
end
| _ -> begin
false
end))

let is_O_RDWR = (fun ( _discr_ ) -> (match (_discr_) with
| Support.System.O_RDWR -> begin
true
end
| _ -> begin
false
end))

let is_O_APPEND = (fun ( _discr_ ) -> (match (_discr_) with
| Support.System.O_APPEND -> begin
true
end
| _ -> begin
false
end))

let is_O_CREAT = (fun ( _discr_ ) -> (match (_discr_) with
| Support.System.O_CREAT -> begin
true
end
| _ -> begin
false
end))

*)
