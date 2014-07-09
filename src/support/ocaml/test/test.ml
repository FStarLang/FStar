(* -------------------------------------------------------------------- *)
let _ =
  let open BatPervasives in

  let filename = "test.sqlite3" in

  finally
    (fun () -> try Unix.unlink filename with _ -> ())
    (fun () ->
      let db = DB.opendb filename in
      finally
        (fun () -> DB.closedb db)
        (fun () ->
          DB.put db "k1" "v1";
          DB.put db "k2" "v2";
          Printf.printf "%b\n%!" (DB.get db "XX" = None);
          Printf.printf "%b\n%!" (DB.get db "k1" = Some "v1");
          Printf.printf "%b\n%!" (DB.get db "k2" = Some "v2");
          Printf.printf "%b\n%!" (List.length (DB.all  db) = 2);
          Printf.printf "%b\n%!" (List.length (DB.keys db) = 2))
        ())
    ()

(* -------------------------------------------------------------------- *)
let tohex (s : string) =
  let buffer = Buffer.create (2 * (String.length s)) in
    for i = 0 to (String.length s) - 1 do
      Buffer.add_string buffer
        (Printf.sprintf "%.2x" (Char.code s.[i]));
    done;
    Buffer.contents buffer

let oget = function Some x -> x | _ -> assert false

let _ =
  let ctx = Evp.MD.create (Evp.MD.md5 ()) in
  Evp.MD.update ctx "Hello World!";
  Printf.fprintf stderr "%s\n%!" (tohex (Evp.MD.final ctx))

let _ =
  let txt = "1234567890123456" in
  let key = "1234567890123456" in

  let ctx1 = Evp.CIPHER.create (Evp.CIPHER.aes_128_ecb ()) true  in
  let ctx2 = Evp.CIPHER.create (Evp.CIPHER.aes_128_ecb ()) false in

    List.iter (fun ctx -> Evp.CIPHER.set_key ctx key) [ctx1; ctx2];
    Printf.fprintf stderr "%s\n%!"
      (Evp.CIPHER.process ctx2 (Evp.CIPHER.process ctx1 txt));
    List.iter (fun ctx -> Evp.CIPHER.fini ctx) [ctx1; ctx2]

let _ =
  let txt = "Hello World!"     in
  let key = "1234567890123456" in

    Printf.fprintf stderr "%s\n%!"
      (tohex (Evp.HMAC.hmac (Evp.MD.md5 ()) key txt))

let _ =
  Printf.fprintf stderr "%b\n%!" (Evp.RANDOM.status ());
  Printf.fprintf stderr "%s\n%!" (tohex (Evp.RANDOM.bytes 32))

let _ =
  let key = Evp.RSA.genkey 1024 3 in
  let rsa = Evp.RSA.create () in
    Evp.RSA.setkey rsa key;

  let msg = "Hello World!" in
  let msg = Evp.RSA.encrypt rsa false Evp.RSA.PD_PKCS1 msg in
  let msg = Evp.RSA.decrypt rsa true  Evp.RSA.PD_PKCS1 msg in
    Printf.printf "%d: %s\n%!" (String.length msg) msg;

  let msg = "Hello World!" in
  let msg = Evp.RSA.encrypt rsa true  Evp.RSA.PD_PKCS1 msg in
  let msg = Evp.RSA.decrypt rsa false Evp.RSA.PD_PKCS1 msg in
    Printf.printf "%d: %s\n%!" (String.length msg) msg

let _ =
  let key = Evp.RSA.genkey 1024 3 in
  let rsa = Evp.RSA.create () in
    Evp.RSA.setkey rsa key;

  let msg  = "Hello World!" in
  let sig_ = Evp.RSA.sign rsa Evp.RSA.MD5 msg in
    Printf.printf "%b\n%!" (Evp.RSA.verify rsa Evp.RSA.MD5 msg sig_);
    sig_.[0] <- Char.chr ((Char.code sig_.[0] + 1) mod 256);
    Printf.printf "%b\n%!" (Evp.RSA.verify rsa Evp.RSA.MD5 msg sig_)

let _ =
  let params = Evp.DSA.genparams 512 in
  let key = Evp.DSA.genkey params in
  let dsa = Evp.DSA.create () in
    Evp.DSA.setkey dsa key;

  let msg  = "Hello World!" in
  let sig_ = Evp.DSA.sign dsa msg in
    Printf.printf "%b\n%!" (Evp.DSA.verify dsa msg sig_);
    sig_.[0] <- Char.chr ((Char.code sig_.[0] + 1) mod 256);
    Printf.printf "%b\n%!" (Evp.DSA.verify dsa msg sig_)

let _ =
  let params = Evp.DH.genparams 512 2 in
  let key1   = Evp.DH.genkey params in
  let key2   = Evp.DH.genkey params in
  let dh1    = Evp.DH.create () in
    Evp.DH.setkey dh1 key1;
    ignore (Evp.DH.compute dh1 key2.Evp.DH.k_public)

let dhparams = "-----BEGIN DH PARAMETERS-----
MIIBBwKBgQCctCTvtt225fYth0f8s/s+3K27xVqzrDf4fvgrmLj7OGSoJlghp6pQ
8nEGD+8jRQWak9JMrz1OlQ00YnaYuHb9QyO92O5ZVoBTXcZ07EUycXCWPmJaXUm2
X9XGm5BGhfncqc354ixfrt/+oi9h1PscSfiJvjC0rAjtfcE5xVHMNwKBgE/5q47Z
JhFd6fQhUYfiVyNuolP6z0FCZKrmLa9C6UgPLVTfEEOiW6KsCFh5uiCNYcINDZnb
lInlgrHXG2tlv4/QNCXmXBQeUBkVM+4EXOl2ZciEvFv2zAlkUig/CUcLGo/OwsJV
c8o7MMjRcCH7fDi4BIAzdEKdDYB7uEqnGJgn
-----END DH PARAMETERS-----"

let _ =
  let _params = Evp.DH.params_of_string dhparams in
    ()

let _ = Gc.major ()
