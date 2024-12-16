(* -------------------------------------------------------------------- *)
open BatPervasives

(* -------------------------------------------------------------------- *)
exception DBError of string

(* -------------------------------------------------------------------- *)
type db   = Sqlite3.db
type data = string

(* -------------------------------------------------------------------- *)
module Internal = struct
  (* ------------------------------------------------------------------ *)
  let db_must_ok (status : Sqlite3.Rc.t) : unit =
    match status with
    | Sqlite3.Rc.OK -> ()
    | err -> raise (DBError (Sqlite3.Rc.to_string err))

  (* ------------------------------------------------------------------ *)
  let db_must_done (status : Sqlite3.Rc.t) : unit =
    match status with
    | Sqlite3.Rc.DONE -> ()
    | err -> raise (DBError (Sqlite3.Rc.to_string err))

  (* ------------------------------------------------------------------ *)
  let asblob (data : Sqlite3.Data.t) : data =
    match data with
    | Sqlite3.Data.BLOB value -> value
    | _ -> assert false

  (* ------------------------------------------------------------------ *)
  let dorequest (db : db) (request : string) =
      db_must_ok (Sqlite3.exec db request)

  (* ------------------------------------------------------------------ *)
  let opendb (filename : string) : db =
    FileUtil.mkdir ~parent:true (FilePath.dirname filename);
    let request = "CREATE TABLE IF NOT EXISTS map(key BLOB PRIMARY KEY, value BLOB NOT NULL)" in
    let db      = Sqlite3.db_open filename in

      try  dorequest db request; db
      with e -> (ignore (Sqlite3.db_close db); raise e)

  (* ------------------------------------------------------------------ *)
  let closedb (db : db) : unit =
    ignore (Sqlite3.db_close db)

  (* ------------------------------------------------------------------ *)
  let put (db : db) (key : data) (value : data) : unit =
    let request = "INSERT OR REPLACE INTO map (key, value) VALUES (?, ?)" in
    let request = Sqlite3.prepare db request in

    db_must_ok (Sqlite3.bind request 1 (Sqlite3.Data.BLOB key  ));
    db_must_ok (Sqlite3.bind request 2 (Sqlite3.Data.BLOB value));

    finally
      (fun () -> db_must_ok   (Sqlite3.finalize request))
      (fun () -> db_must_done (Sqlite3.step request))
      ()

  (* ------------------------------------------------------------------ *)
  let get (db : db) (key : data) : data option =
    let request = "SELECT value FROM map WHERE key = ? LIMIT 1" in
    let request = Sqlite3.prepare db request in

    finally
      (fun () -> db_must_ok (Sqlite3.finalize request))
      (fun () ->
        db_must_ok (Sqlite3.bind request 1 (Sqlite3.Data.BLOB key));

        match Sqlite3.step request with
        | Sqlite3.Rc.DONE -> None
        | Sqlite3.Rc.ROW  -> Some (asblob (Sqlite3.column request 0))
        | err             -> raise (DBError (Sqlite3.Rc.to_string err)))
      ()

  (* ------------------------------------------------------------------ *)
  let remove (db : db) (key : data) =
    let request = "DELETE FROM map WHERE key = ?" in
    let request = Sqlite3.prepare db request in

    finally
      (fun () -> db_must_ok (Sqlite3.finalize request))
      (fun () ->
        db_must_ok   (Sqlite3.bind request 1 (Sqlite3.Data.BLOB key));
        db_must_done (Sqlite3.step request);
        true)
      ()

  (* ------------------------------------------------------------------ *)
  let all (db : db) =
    let request = "SELECT key, value FROM map" in
    let request = Sqlite3.prepare db request in

    finally
      (fun () -> db_must_ok (Sqlite3.finalize request))
      (fun () ->
        let rec read aout =
          match Sqlite3.step request with
          | Sqlite3.Rc.DONE -> aout
          | Sqlite3.Rc.ROW  ->
              let key   = asblob (Sqlite3.column request 0) in
              let value = asblob (Sqlite3.column request 1) in
              read ((key, value) :: aout)
          | err -> raise (DBError (Sqlite3.Rc.to_string err))
        in read [])
      ()

  (* ------------------------------------------------------------------ *)
  let keys (db : db) =
    let request = "SELECT key FROM map" in
    let request = Sqlite3.prepare db request in

    finally
      (fun () -> db_must_ok (Sqlite3.finalize request))
      (fun () ->
        let rec read aout =
          match Sqlite3.step request with
          | Sqlite3.Rc.DONE -> aout
          | Sqlite3.Rc.ROW  ->
              let key   = asblob (Sqlite3.column request 0) in
              read (key :: aout)
          | err -> raise (DBError (Sqlite3.Rc.to_string err))
        in read [])
      ()

  (* ------------------------------------------------------------------ *)
  let tx (db : db) (cb : db -> 'a) : 'a =
    finally
      (fun () -> db_must_ok (Sqlite3.exec db "END TRANSACTION"))
      (fun () ->
        db_must_ok (Sqlite3.exec db "BEGIN IMMEDIATE TRANSACTION");
        cb db)
      ()

  (* ------------------------------------------------------------------ *)
  let wrap fn =
    try fn () with
    | Sqlite3.Error      err -> raise (DBError err)
    | Sqlite3.RangeError _   -> raise (DBError "range-error")

  (* ------------------------------------------------------------------ *)
  let wrap1 fn x     = wrap (fun () -> fn x)
  let wrap2 fn x y   = wrap (fun () -> fn x y)
  let wrap3 fn x y z = wrap (fun () -> fn x y z)
end

(* -------------------------------------------------------------------- *)
let opendb  = Internal.wrap1 Internal.opendb
let closedb = Internal.wrap1 Internal.closedb
let put     = Internal.wrap3 Internal.put
let get     = Internal.wrap2 Internal.get
let remove  = Internal.wrap2 Internal.remove
let all     = Internal.wrap1 Internal.all
let keys    = Internal.wrap1 Internal.keys

let tx db cb =
  Internal.wrap (fun () -> Internal.tx db cb)
