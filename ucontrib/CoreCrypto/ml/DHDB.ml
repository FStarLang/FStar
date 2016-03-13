open CoreCrypto

type bytes = Platform.Bytes.bytes
let string_of_bytes b = Platform.Bytes.get_cbytes b
let bytes_of_string s = Platform.Bytes.abytes s

type key   = bytes * bytes
type value = bytes * bool

type dhdb = DB.db

let defaultFileName = ""
let defaultDHPrimeConfidence = 0
let defaultPQMinLength = (1024, 512)

let ser_key (k:key) =
  let u,v = k in
  let u,v = string_of_bytes u, string_of_bytes v in
  Marshal.to_string (u,v) [Marshal.No_sharing]

let ser_val (v:value) =
  let u,v = v in
  let u = string_of_bytes u in
  Marshal.to_string (u,v) []

let unser_key (s:string) =
  let (u,v) = Marshal.from_string s 0 in
  (bytes_of_string u, bytes_of_string v)

let unser_val (s:string) =
  let (u,v) : (string * bool) = Marshal.from_string s 0 in
  (bytes_of_string u, v)

(* let create s = DB.create s *)
let create s = DB.opendb s

let select db key =
  match DB.get db (ser_key key) with
  | None -> None
  | Some v -> Some (unser_val v)

let insert db k v =
  DB.put db (ser_key k) (ser_val v);
  db

let remove db k =
  DB.remove db (ser_key k);
  db

let keys db = List.map unser_key (DB.keys db)

let merge db s = db

let dh_check_params db u (a,b) x y = Some (db, {dh_p = x; dh_g = y; dh_q = None; safe_prime = true})

let dh_check_element dhp b = true

let load_default_params s db (a,b) = (DB.opendb s, {dh_p=bytes_of_string "";dh_g=bytes_of_string "";dh_q=None;safe_prime=true})
