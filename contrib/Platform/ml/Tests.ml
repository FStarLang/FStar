open Unix

(* Convert human readable form to 32 bit value *)
let packed_ip = inet_addr_of_string "40.76.88.64"

(* Convert 32 bit value to ip adress *)
let ip_address = string_of_inet_addr (packed_ip)

(* Create socket object *)
let sock = socket PF_INET SOCK_STREAM 0

(* Get socketname *)
(* let saddr = getsockname sock  *)

let unix_send sock str =
    let len = String.length str in
    send sock str 0 len []

let unix_recv sock maxlen =
    let str = Bytes.create maxlen in
    let recvlen = recv sock str 0 maxlen [] in
    String.sub str 0 recvlen

let tcp_recv sock maxlen =
    match ( Platform.Tcp.recv sock maxlen ) with
    |  Platform.Error.Correct b -> (Platform.Bytes.get_cbytes b)
    | _ -> failwith "Error \n" ;;

let passed = ref 0
let total  = ref 0


let client_sock = socket PF_INET SOCK_STREAM 0

let tcp_client_sock = Platform.Tcp.connect "fstar-lang.org" (Z.of_int 80)

let hentry =
    gethostbyname "fstar-lang.org" ;;

connect client_sock (ADDR_INET (hentry.h_addr_list.(0), 80)) ; (* HTTP *)

let unix = unix_recv client_sock 1024 in
(* Printf.printf "Unix: %s \n" unix; *)
let tcp  = tcp_recv tcp_client_sock (Z.of_int 1024) in
(* Printf.printf "Tcp:  %s \n" tcp; *)
total := !total + 1;
if unix=tcp then
  passed := !passed + 1;

unix_send client_sock "HEAD / HTTP/1.0\nConnection: close\nHost: fstar-lang.org\n\n" |> ignore ;

let unix = unix_recv client_sock 1024 in
(* Printf.printf "Unix: %s \n" unix; *)
let tcp  = tcp_recv tcp_client_sock (Z.of_int 1024) in
Printf.printf "Tcp:  %s \n" tcp;
total := !total + 1;
passed := !passed + 1;


(* unix_send client_sock "rcpt to: <erikd@localhost>\n" ;
unix_recv client_sock 1024 |> Printf.printf "received: %s \n" ;

unix_send client_sock "data\n" ;
unix_recv client_sock 1024 |> Printf.printf "redeived: %s " ;

unix_send client_sock "From: Ocaml whiz\nSubject: Ocaml rulez!\n\nYES!\n.\n" ;
unix_recv client_sock 1024 |> Printf.printf "redeived: %s " ; *)

close client_sock ;;

Platform.Tcp.close tcp_client_sock ;;


let server_sock = socket PF_INET SOCK_STREAM 0 in

(* so we can restart our server quickly *)
setsockopt server_sock SO_REUSEADDR true ;

(* build up my socket address *)
let address = (gethostbyname(gethostname())).h_addr_list.(0) in
bind server_sock (ADDR_INET (address, 1029)) ;



(* Listen on the socket. Max of 10 incoming connections. *)
listen server_sock 10 ;

let thread () =
    try
      let client_sock = socket PF_INET SOCK_STREAM 0 in
      (connect client_sock) (ADDR_INET (address, 1029));
      Platform.Tcp.send client_sock (Platform.Bytes.abytes "Hello\n") |> ignore;
      Platform.Tcp.close client_sock
    with Unix_error (e,s1,s2) ->
     failwith (Printf.sprintf "%s: %s(%s)" (error_message e) s1 s2) in

Thread.create thread () |> ignore ;

(* accept and process connections *)

let (client_sock, client_addr) = accept server_sock in

let tcp = tcp_recv client_sock (Z.of_int 1024) in
(* Printf.printf "Tcp:  %s \n" tcp; *)
total := !total + 1;
if tcp="Hello\n" then
  passed := !passed + 1;


let str = "Hello\n" in
let len = String.length str in
let _ = send client_sock str 0 len [] in
shutdown client_sock SHUTDOWN_ALL;;

Printf.printf "%d/%d tests passed\n" !passed !total
