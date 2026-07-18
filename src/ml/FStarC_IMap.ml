module ZHashtbl = BatHashtbl.Make(Z)

type 'value imap = 'value ZHashtbl.t
let create (i:Z.t) : 'value imap = ZHashtbl.create (Z.to_int i)
let clear (s:('value imap)) = ZHashtbl.clear s
let add (m:'value imap) k (v:'value) = ZHashtbl.replace m k v
let of_list (l: (Z.t * 'value) list) =
  let s = ZHashtbl.create (BatList.length l) in
  FStar_List.iter (fun (x,y) -> add s x y) l;
  s
let try_find (m:'value imap) k = ZHashtbl.find_option m k
let fold (m:'value imap) f a = ZHashtbl.fold f m a
let remove (m:'value imap) k = ZHashtbl.remove m k
let keys (m:'value imap) = fold m (fun k _ acc -> k::acc) []
let copy (m:'value imap) = ZHashtbl.copy m
