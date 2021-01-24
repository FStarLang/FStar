type hash_code = int
let of_int (i:Z.t) = Z.to_int i
let of_string (s:string) = BatHashtbl.hash s
let mix (h1: hash_code) (h2:hash_code) =
  let h2 = h2 - h1 in
  let h2 = h2 lxor (h1 lsl 16) in
  let h1 = h1 - h2 in
  let h2 = h2 lxor (h1 lsl 32) in
  let h2 = h2 - h1 in
  let h2 = h2 lxor (h1 lsl 20) in
  h2
type 'a cmp = 'a -> 'a -> bool
module HashKey =
  struct
    type t = hash_code
    let equal (x:t) (y:t) = x=y
    let hash (x:t) = x
  end
module HT = BatHashtbl.Make(HashKey)
type ('a, 'b) hashtable = (('a * 'b) list) HT.t * 'a cmp
type 'a hashable = 'a * ('a -> hash_code)
let create (c:'a cmp) = HT.create 10000, c
let insert (x: 'a hashable) (y:'b) (ht:('a,'b) hashtable) =
    let x, hc = fst x, snd x (fst x) in
    try
      let l = HT.find (fst ht) hc in
      HT.remove (fst ht) hc;
      HT.add (fst ht) hc ((x,y)::l)
    with
      | Not_found -> HT.add (fst ht) hc [x,y]
let lookup (x: 'a hashable) (ht:('a,'b) hashtable) : 'b option =
  try
    let x, hc = fst x, snd x (fst x) in
    let ht, cmp = ht in
    let l = HT.find ht hc in
    Some (snd (BatList.find (fun (xx, _) -> cmp x xx) l))
  with
    | Not_found -> None
let clear (ht: ('a,'b) hashtable) = HT.clear (fst ht)
