module StringOps =
  struct
    type t = string
    let equal (x:t) (y:t) = x=y
    let compare (x:t) (y:t) = BatString.compare x y
    let hash (x:t) = BatHashtbl.hash x
  end
module StringHashtbl = BatHashtbl.Make(StringOps)

type 'value t = 'value StringHashtbl.t
let create (i:Z.t) : 'value t = StringHashtbl.create (Z.to_int i)
let clear (s:('value t)) = StringHashtbl.clear s
let add (m:'value t) k (v:'value) = StringHashtbl.replace m k v
let of_list (l: (string * 'value) list) =
  let s = StringHashtbl.create (BatList.length l) in
  FStar_List.iter (fun (x,y) -> add s x y) l;
  s
let try_find (m:'value t) k = StringHashtbl.find_option m k
let fold (m:'value t) f a = StringHashtbl.fold f m a
let remove (m:'value t) k = StringHashtbl.remove m k
let keys (m:'value t) = fold m (fun k _ acc -> k::acc) []
let copy (m:'value t) = StringHashtbl.copy m
let size (m:'value t) = Z.of_int (StringHashtbl.length m)
let iter (m:'value t) f = StringHashtbl.iter f m
