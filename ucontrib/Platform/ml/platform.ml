module Error = struct
  type ('a,'b) optResult =
      | Error of 'a
      | Correct of 'b

  let perror (file:string) (line:Z.t) (text:string) =
      text

  let uu___is_Correct = function
    | Correct _ -> true
    | _ -> false

  let uu___is_Error = function
    | Error _ -> true
    | _ -> false

  let correct x = Correct x
  let if_ideal f x = x

  let unexpected info = failwith info
  let unreachable info = failwith info
end

module StdBytes = Bytes

module Bytes = struct

  type byte = char
  type nat = int
  type cbytes = string

  let rec getByte (bl:cbytes list) (i:int) =
      match bl with
       [] -> failwith "getByte: array out of bounds"
     | h::t when i >= String.length h -> getByte t (i-String.length h)
     | h::t -> String.get h i

  let rec getByte2 (bl: cbytes list) i : byte*byte =
      match bl with
       [] -> failwith "array out of bounds"
     | h::t when i >= String.length h -> getByte2 t (i - String.length h)
     | h::t when (String.length h) - i >= 2 -> String.get h i, String.get h (i+1)
     | h1::h2::t when (String.length h1) - i = 1 && (String.length h2) > 0 -> String.get h1 i, String.get h2 0
     | _ -> failwith "getByte2: array out of bounds"

  let rec getBytes (bl:cbytes list) i n  =
      match bl with
       [] -> if n > 0 then failwith "getBytes: array out of bounds" else ""
     | h::t ->
          if i >= (String.length h)
          then getBytes t (i- (String.length h)) n
          else let curr = (String.length h) - i in
               if curr >= n
               then String.sub h i n
               else (String.sub h i curr) ^ (getBytes t 0 (n-curr))

  (* This type represents a subset of a sequence of bytes; the sequence of bytes
   * is represented as a list of strings. *)
  type bytes = {
      (*  A series of strings whose total concatenated length is [max]. *)
      bl: cbytes list;
      max: int;
      (* The length of the subset. *)
      length: int;
      (* The start index of the subset. *)
      index: int;
  }

  let lemma_repr_bytes_values n = ()

  let cbyte (b:bytes) =
      if b.length = 1 then
        let b1 = getByte b.bl b.index in b1
      else failwith "cbyte: expected an array of length 1"

  let cbyte2 (b:bytes) =
      if b.length = 2 then
        let (b1,b2) = getByte2 b.bl b.index in b1,b2
      else failwith "cbyte2: expected an array of length 2"

  let index (b:bytes) i =
    let i = Z.to_int i in
    if b.length >= i then
      let s = getBytes b.bl b.index b.length in
      String.get s i
    else failwith "index: index out of range"

  let get_cbytes (b:bytes) =
      if b.length = b.max && b.index = 0 then
        let bl' = String.concat "" b.bl in  bl'
      else
        let bl' = getBytes b.bl b.index b.length in bl'

  let abytes (ba:cbytes) =
      {bl = [ba]; length = String.length ba; index = 0; max = String.length ba}
  let abytes_max (ba:cbytes) (max:int) =
      let arr = String.make max (char_of_int 0) in
      let len = String.length ba in
      (for i = 0 to len-1 do Bytes.set arr i ba.[0] done);
      {bl = [arr]; length = len; index = 0; max = len}

  let abyte (ba:byte) =
      {bl = [String.make 1 ba]; length = 1; index = 0; max = 1}

  let abyte2 (ba1,ba2) =
      let s = String.make 2 ba1 in
      Bytes.set s 1 ba2;
      {bl = [s]; length = 2; index = 0; max = 2}

  (* JP: this makes the operator right-associative; is that desired? *)
  let (@|) (a:bytes) (b:bytes) =
      if a.length + a.index = a.max && b.index = 0 then
        {bl = (a.bl @ b.bl);
         length = a.length + b.length;
         index = a.index;
         max = a.max + b.max}
      else
        {bl = [(get_cbytes a)^(get_cbytes b)];
         length = a.length + b.length;
         index = 0;
         max = a.length + b.length}

  let op_At_Bar a b = a @| b
  let op_AtBar a b = a @| b

  let split (b:bytes) i : bytes * bytes =
    let i = Z.to_int i in
      {bl = b.bl;
       length = i;
       index = b.index;
       max = b.max},
      {bl = b.bl;
       length = b.length - i;
       index = b.index + i;
       max = b.max}

  let split_eq = split

  let length (d:bytes) = Z.of_int d.length


  let empty_bytes = abytes ""
  let createBytes len (value:char) : bytes =
      let len = Z.to_int len in
      try abytes (String.make len value)
      with _ -> failwith "Default integer for createBytes was greater than max_value"

  let initBytes len f : bytes =
      let len = Z.to_int len in
      try abytes (String.init len (fun i -> f (Z.of_int i)))
      with _ -> failwith "Platform.Bytes.initBytes: invalid char returned"

  type 'a lbytes = bytes

  let bytes_of_int nb i =
    let nb = Z.to_int nb in
    let i = Z.to_int64 i in
    if Int64.compare i Int64.zero < 0 then failwith "Negative 64bit.";
    let rec put_bytes bb lb n =
      if lb = 0 then failwith "not enough bytes"
      else
        begin
          let lown = Int64.logand n (Int64.of_int 255) in
          Bytes.set bb (lb-1) (char_of_int (Int64.to_int lown));
          let ns = Int64.div n (Int64.of_int 256) in
          if Int64.compare ns Int64.zero > 0 then
            put_bytes bb (lb-1) ns
          else bb
        end
    in
    let b = String.make nb (char_of_int 0) in
      abytes(put_bytes b nb i)

  let int_of_bytes (b:bytes) =
      let x = ref 0 in
      let c = get_cbytes b in
      for y = 0 to b.length-1 do
          x := 256 * !x + (int_of_char (String.get c y))
      done;
      Z.of_int !x

  let equalBytes (b1:bytes) (b2:bytes) =
      if length b1 = length b2 then
         let cb1 = get_cbytes b1 in
         let cb2 = get_cbytes b2 in
         let ok = ref true in
         for x = 0 to b1.length-1 do
             ok := String.get cb1 x = String.get cb2 x && !ok;
         done;
         !ok
      else false

  let xor len s1 s2 =
      let len = Z.to_int len in
      let s1 = get_cbytes s1 in
      let s2 = get_cbytes s2 in
      let res = String.make len (char_of_int 0) in
      for i=0 to len-1 do
        Bytes.set res i (char_of_int ((int_of_char s1.[i]) lxor (int_of_char s2.[i])))
      done;
      abytes res


  let split2 (b:bytes) i j : bytes * bytes * bytes =
    let b1,b2 = split b i in
    let b2a,b2b = split b2 j in
    (b1,b2a,b2b)


  let utf8 (x:string) : bytes = abytes x (* TODO: use Camomile *)
  let iutf8 (x:bytes) : string = get_cbytes x (* TODO: use Camomile *)
  let iutf8_opt (x:bytes) : string option = Some (get_cbytes x)

  let print_bytes (x:bytes) : string =
    let s = get_cbytes x in
    let res = ref "" in
    for i = 0 to String.length s - 1 do
      res := !res ^ (Printf.sprintf "%x " (int_of_char s.[i]));
    done;
    !res

  (*
  let utf8 (x:string) : bytes = abytes (System.Text.Encoding.UTF8.GetBytes x)
  let iutf8 (x:bytes) : string = System.Text.Encoding.UTF8.GetString (cbytes x)
  *)

  let byte_of_int i =
    char_of_int (Z.to_int i)

  (* Some helpers to deal with the conversation from hex literals to bytes and
   * conversely. Mostly for tests. *)

  let digit_to_int c = match c with
    | '0'..'9' -> Char.code c - Char.code '0'
    | 'a'..'f' -> 10 + Char.code c - Char.code 'a'
    | _ -> failwith "hex_to_char: invalid hex digit"

  let hex_to_char a b =
    Char.chr ((digit_to_int a) lsl 4 + digit_to_int b)

  let char_to_hex c =
    let n = Char.code c in
    let digits = "0123456789abcdef" in
    digits.[n lsr 4], digits.[n land 0x0f]

  let hex_of_string s =
    let n = String.length s in
    let buf = Buffer.create n in
    for i = 0 to n - 1 do
      let d1,d2 = char_to_hex s.[i] in
      Buffer.add_char buf d1;
      Buffer.add_char buf d2;
    done;
    Buffer.contents buf

  let string_of_hex s =
    let n = String.length s in
    if n mod 2 <> 0 then
      failwith "string_of_hex: invalid length"
    else
      let res = Bytes.create (n/2) in
      let rec aux i =
        if i >= n then ()
        else (
          Bytes.set res (i/2) (hex_to_char s.[i] s.[i+1]);
          aux (i+2)
        )
      in
      aux 0;
      res

  let string_of_bytes b = get_cbytes b
  let bytes_of_string s = abytes s

  let bytes_of_hex s = bytes_of_string (string_of_hex s)
  let hex_of_bytes b = hex_of_string (string_of_bytes b)

end


module Tcp = struct
  open Bytes
  open Error
  open Unix

  type networkStream = file_descr
  type tcpListener = file_descr

  let listen s i =
      let i = Z.to_int i in
      let server_sock = socket PF_INET SOCK_STREAM 0 in
      (setsockopt server_sock SO_REUSEADDR true ;
       let address = inet_addr_of_string s in
       bind server_sock (ADDR_INET (address, i)) ;
       listen server_sock 10;
       server_sock)

  let accept s =
      let (client_sock, client_addr) = accept s in
      client_sock

  let acceptTimeout t s = accept s

  let stop s = shutdown s SHUTDOWN_ALL

  let connect s i =
      let i = Z.to_int i in
      let client_sock = socket PF_INET SOCK_STREAM 0 in
      let hentry = gethostbyname s in
      connect client_sock (ADDR_INET (hentry.h_addr_list.(0), i)) ;
      client_sock

  let connectTimeout t s i = connect s i

  let sock_send sock str =
      let str = get_cbytes str in
      let len = String.length str in
      send sock str 0 len []

  let sock_recv sock maxlen =
      let str = StdBytes.create maxlen in
      let recvlen = recv sock str 0 maxlen [] in
      let str = String.sub str 0 recvlen in
      abytes str

  type 'a recv_result = 
  | RecvWouldBlock
  | RecvError of string
  | Received of Bytes.bytes

  let recv_async s i =
      let i = Z.to_int i in
      try Received (sock_recv s i) with
      | Unix_error ((EAGAIN | EWOULDBLOCK),_,_) -> RecvWouldBlock
      | Unix_error (e,s1,s2) -> RecvError (Printf.sprintf "%s: %s(%s)" (error_message e) s1 s2)

  let set_nonblock = set_nonblock 
  let clear_nonblock = clear_nonblock

  let recv s i =
      let i = Z.to_int i in
      try Correct (sock_recv s i)
      with Unix_error (e,s1,s2) ->
       Error (Printf.sprintf "%s: %s(%s)" (error_message e) s1 s2)

  let rec send s b =
      try (
          let n = sock_send s b in 
          let m = Z.to_int (Bytes.length b) in 
          if n < m
          then 
              (* send s (String.sub str n (m - n) *)
              Error(Printf.sprintf "Network error, wrote %d bytes" n) 
          else Correct())
      with 
      | Unix_error ((EAGAIN | EWOULDBLOCK),_,_) -> send s b
      | Unix_error (e,s1,s2) -> Error (Printf.sprintf "%s: %s(%s)" (error_message e) s1 s2)

  let close s =
      close s


  (*
  open Unix

  (* Convert human readable form to 32 bit value *)
  let packed_ip = inet_addr_of_string "208.146.240.1" in


  (* Convert 32 bit value to ip adress *)
  let ip_address = string_of_inet_addr (packed_ip) in

  (* Create socket object *)
  let sock = socket PF_INET SOCK_STREAM 0 in

  (* Get socketname *)
  let saddr = getsockname sock ;;

  let sock_send sock str =
      let len = String.length str in
      send sock str 0 len []

  let sock_recv sock maxlen =
      let str = String.create maxlen in
      let recvlen = recv sock str 0 maxlen [] in
      String.sub str 0 recvlen

  let client_sock = socket PF_INET SOCK_STREAM 0 in
  let hentry = gethostbyname "coltrane" in
  connect client_sock (ADDR_INET (hentry.h_addr_list.(0), 25)) ; (* SMTP *)

  sock_recv client_sock 1024 ;

  sock_send client_sock "mail from: <pleac@localhost>\n" ;
  sock_recv client_sock 1024 ;

  sock_send client_sock "rcpt to: <erikd@localhost>\n" ;
  sock_recv client_sock 1024;

  sock_send client_sock "data\n" ;
  sock_recv client_sock 1024 ;

  sock_send client_sock "From: Ocaml whiz\nSubject: Ocaml rulez!\n\nYES!\n.\n" ;
  sock_recv client_sock 1024 ;

  close client_sock ;;

  let server_sock = socket PF_INET SOCK_STREAM 0 in

  (* so we can restart our server quickly *)
  setsockopt server_sock SO_REUSEADDR true ;

  (* build up my socket address *)
  let address = (gethostbyname(gethostname())).h_addr_list.(0) in
  bind server_sock (ADDR_INET (address, 1029)) ;

  (* Listen on the socket. Max of 10 incoming connections. *)
  listen server_sock 10 ;

  (* accept and process connections *)
  while true do
          let (client_sock, client_addr) = accept server_sock in
          let str = "Hello\n" in
          let len = String.length str in
          let x = send client_sock str 0 len [] in
          shutdown client_sock SHUTDOWN_ALL
          done ;;

  *)
end

module Udp = struct
  open Bytes
  open Error
  open Unix


  type socket = file_descr
  type udpListener = file_descr

  (* Default network input buffer size *)
  let default_buffer_size = 2048

  (* Close the network socket *)
  let stop s =
    shutdown s SHUTDOWN_ALL

  let close s =
    close s

  (* Initiate a connection *)
  let connect ip port =
    let port = Z.to_int port in
    let client_sock = socket PF_INET SOCK_DGRAM 0 in
    let addr = inet_addr_of_string ip in
    connect client_sock (ADDR_INET(addr,port));
    client_sock

  (* Send abstract bytes through the socket after making them concrete *)
  let sock_send sock str =
    let str = get_cbytes str in
    let len = String.length str in
    send sock str 0 len []

  (* Receive bytes from the socket and make them abstract *)
  let sock_recv sock maxlen =
    let str = StdBytes.create maxlen in
    let recvlen = recv sock str 0 maxlen [] in
    let str = String.sub str 0 recvlen in
    abytes str

  (* Receive bytes from the netwok *)
  let recv s i =
    let i = Z.to_int i in
    try Correct (sock_recv s i)
    with Unix_error (e,s1,s2) ->
      Error (Printf.sprintf "%s: %s(%s)" (error_message e) s1 s2)

  (* Send bytes to the network *)
  let send s b =
    try
      (let n = sock_send s b in
       if n < Z.to_int (Bytes.length b) then
         Error(Printf.sprintf "Network error, wrote %d bytes" n)
       else Correct())
    with Unix_error (e,s1,s2) ->
      Error (Printf.sprintf "%s: %s(%s)" (error_message e) s1 s2)

  (* Extract input and output channels from the socket *)
  let sock_split s =
    let oc = out_channel_of_descr s in
    let ic = in_channel_of_descr s in
    ic,oc

  (* Flush output channel of the socket *)
  let flush oc =
    flush oc

(*
  (* Read helper function *)
  let rec read_acc s nbytes prev =
    if nbytes = 0 then
      abytes prev
    else
      try
        let buf = String.create nbytes in
        let r = read s buf 0 nbytes in
        if r = 0 then
          failwith "UDP connection closed: Read returned 0 bytes"
        else
          let rem = nbytes - r in
          read_acc s rem (String.cat prev (String.sub buf 0 r))
      with
      | _ -> failwith "UDP connection: Not enough bytes to read"

  (* Read the network *)
  let read s nbytes =
    try
      (read_acc s nbytes String.empty)
    with Unix_error (e,s1,s2) ->
       Error (Printf.sprintf "%s: %s(%s)" (error_message e) s1 s2)

  (* Read all bytes from the network up to default_buffer_size *)
  let read_all s =
    try
      let buf = String.create default_buffer_size in
      let r = Unix.read s buf 0 default_buffer_size in
      r,(abytes (String.sub buf 0 r))
    with Unix_error (e,s1,s2) ->
       Error (Printf.sprintf "%s: %s(%s)" (error_message e) s1 s2)

  (* Write to the network *)
  let write s b =
    let oc = out_channel_of_descr s in
    output_string oc b; flush oc
 *)
end

module Date = struct
  type dateTime = DT of float
  type timeSpan = TS of float
  let now () = DT (Unix.gettimeofday())
  let secondsFromDawn () = Int64.of_float (Unix.time()) |> Z.of_int64
  let newTimeSpan d h m s = TS (((((float_of_int (Z.to_int d)) *. 24.0) +. (float_of_int (Z.to_int h))) *. 60.0 +. (float_of_int (Z.to_int m))) *. 60.0 +. (float_of_int (Z.to_int s)))
  let addTimeSpan (DT(a)) (TS(b)) = DT (a +. b)
  let greaterDateTime (DT(a)) (DT(b)) = a > b
end

module Option = struct
  let map f = function
    | Some x -> Some (f x)
    | None -> None

  let must = function
    | Some x -> x
    | None -> invalid_arg "Option.must"
end
