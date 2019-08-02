  open FStar_Bytes
  open FStar_Error
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
    send_substring sock str 0 len []

  (* Receive bytes from the socket and make them abstract *)
  let sock_recv sock maxlen =
    let str = Bytes.create maxlen in
    let recvlen = recv sock str 0 maxlen [] in
    let str = Bytes.sub_string str 0 recvlen in
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
       if n < String.length b then
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
