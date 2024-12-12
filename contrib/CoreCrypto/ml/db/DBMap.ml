(* -------------------------------------------------------------------- *)
type ('a, 'b) dbmap = DB.db

(* -------------------------------------------------------------------- *)
let create (db : DB.db) : ('a, 'b) dbmap =
  db

(* -------------------------------------------------------------------- *)
let put (k : 'a) (v : 'b) (db : ('a, 'b) dbmap) =
  DB.put db
    (Marshal.to_string k [])
    (Marshal.to_string v [])

(* -------------------------------------------------------------------- *)
let get (k : 'a) (db : ('a, 'b) dbmap) : 'b =
  match DB.get db (Marshal.to_string k []) with
  | None   -> None
  | Some v -> Some (Marshal.from_string v 0)
