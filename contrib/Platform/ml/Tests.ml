open Platform
open Unix

(* Convert human readable form to 32 bit value *)
let packed_ip = inet_addr_of_string "81.200.64.50" (* now fstar-lang, was 208.146.240.1? *)

(* Convert 32 bit value to ip adress *)
let ip_address = string_of_inet_addr (packed_ip)

(* Create socket object *)
let sock = socket PF_INET SOCK_STREAM 0

(* Get socketname *)
(* let saddr = getsockname sock  *)

let sock_send sock str =
    Printf.printf "sock_send\n" ;
    let len = String.length str in
    send sock str 0 len []

let sock_recv sock maxlen =
      Printf.printf "sock_recv\n" ;
    let str = String.create maxlen in
    let recvlen = recv sock str 0 maxlen [] in
    String.sub str 0 recvlen

let client_sock = socket PF_INET SOCK_STREAM 0

let hentry =
    Printf.printf "gethostbyname\n" ;
    gethostbyname "fstar-lang.org" ;;

connect client_sock (ADDR_INET (hentry.h_addr_list.(0), 25)) ; (* SMTP *)

Printf.printf "connected\n" ;


sock_recv client_sock 1024 |> Printf.printf "redeived: %s " ;

sock_send client_sock "mail from: <pleac@localhost>\n" ;
sock_recv client_sock 1024 |> Printf.printf "redeived: %s " ;

sock_send client_sock "rcpt to: <erikd@localhost>\n" ;
sock_recv client_sock 1024 |> Printf.printf "redeived: %s " ;

sock_send client_sock "data\n" ;
sock_recv client_sock 1024 |> Printf.printf "redeived: %s " ;

sock_send client_sock "From: Ocaml whiz\nSubject: Ocaml rulez!\n\nYES!\n.\n" ;
sock_recv client_sock 1024 |> Printf.printf "redeived: %s " ;

close client_sock ;;

Printf.printf "closed" ;

failwith "closed" ;

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
        Printf.printf "loop\n" ;
        let (client_sock, client_addr) = accept server_sock in
        let str = "Hello\n" in
        let len = String.length str in
        let x = send client_sock str 0 len [] in
        shutdown client_sock SHUTDOWN_ALL
        done ;;

Printf.printf "tests passed\n" ;
