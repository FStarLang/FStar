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
type stats = {
  max_hash_code : hash_code;
  max_bucket_size : int
}
let init_stats = { max_hash_code = 0; max_bucket_size = 0}
type ('a, 'b) hashtable = (('a * 'b) list) HT.t * 'a cmp * stats ref
type 'a hashable = 'a * ('a -> hash_code)
let create (c:'a cmp) = HT.create 100000, c, ref init_stats
let insert (x: 'a hashable) (y:'b) (ht:('a,'b) hashtable) =
    let x, hc = fst x, snd x (fst x) in
    let htbl, _, stats_ref = ht in
    try
      let l = HT.find htbl hc in
      HT.remove htbl hc;
      HT.add htbl hc ((x,y)::l);
      let stats = !stats_ref in
      let n = List.length l + 1 in
      if n > stats.max_bucket_size
      then stats_ref := { max_bucket_size = n; max_hash_code = hc }
    with
      | Not_found -> HT.add htbl hc [x,y]
module BU = FStar_Compiler_Util
let lookup (x: 'a hashable) (ht:('a,'b) hashtable) : 'b option =
  try
    let x, hc = fst x, snd x (fst x) in
    let ht, cmp, _ = ht in
    let l = HT.find ht hc in
(*    
    if FStar_Options.profile_enabled None "FStar.TypeChecker.Core"
    then BU.print2 "Hash %s: Bucket size is %s\n" 
                   (string_of_int hc)
                   (BU.string_of_int (FStar_List.length l));
*)                                                        
    Some (snd (BatList.find (fun (xx, _) -> cmp x xx) l))
  with
    | Not_found -> None
let clear ((htbl, _, stats): ('a,'b) hashtable) = HT.clear htbl; stats := init_stats
let max_bucket_stats (ht: ('a, 'b) hashtable) (cb: Z.t option -> ('a * 'b) list -> unit) : unit = 
  try 
    let htbl, _, stats_ref = ht in
    let stats = !stats_ref in 
    let l = HT.find htbl stats.max_hash_code in
    cb (Some (Z.of_int stats.max_hash_code)) l
  with
    | Not_found -> cb None []
let string_of_hash_code h = string_of_int h
