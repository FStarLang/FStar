module LowStar.Permissions.Buffer

module B = LowStar.Buffer
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
open FStar.HyperStack.ST
module F = FStar.FunctionalExtensionality
module G = FStar.Ghost

open FStar.Real

let perm_id = pos
let permission = (r:real{r >=. 0.0R /\ r <=. 1.0R})

private noeq
type perms_rec (a:Type) = {
  current_max : pos;
  perm_map    : F.restricted_t pos (fun (x:pos) -> (permission * a))
}

let rec sum_until (#a:Type) (f:pos -> permission * a) (n:nat) : GTot real =
  if n = 0 then 0.0R
  else fst (f n) +. sum_until f (n - 1)

let value_perms (#a:Type) (v:a) = p:perms_rec a{
  (forall (n:nat). n > p.current_max ==> fst (p.perm_map n) = 0.0R) /\        // Permissions are null above currently split objects
  (sum_until p.perm_map p.current_max = 1.0R) /\                  // The sum of permissions is 1
  (forall (n:pos). fst (p.perm_map n) >. 0.0R ==> snd (p.perm_map n) == v)}  // All readable perms agree

let b_val (a:Type) = v:a & G.erased (value_perms v)

let buffer (a:Type) = B.buffer (b_val a) & G.erased perm_id

let live_cell (#a:Type) (h:HS.mem) (b:B.buffer (b_val a)) (i:nat{i < B.length b}) (pid:G.erased perm_id) =
  let (| v, perms |) = B.get h b i in
  fst ((G.reveal perms).perm_map (G.reveal pid)) >. 0.0R

let live (#a:Type) (h:HS.mem) (b:buffer a) =
  let b, pid = b in
  B.live h b /\
  (forall (i:nat{i < B.length b}). {:pattern (B.get h b i)} live_cell h b i pid)

let writeable_cell (#a:Type) (h:HS.mem) (b:B.buffer (b_val a)) (i:nat{i < B.length b}) (pid:G.erased perm_id) =
  let (| v, perms |) = B.get h b i in
  fst ((G.reveal perms).perm_map (G.reveal pid)) == 1.0R

let writeable (#a:Type) (h:HS.mem) (b:buffer a) =
  let b, pid = b in
  B.live h b /\
  (forall (i:nat{i < B.length b}). {:pattern (B.get h b i)} writeable_cell h b i pid)

let length (#a:Type) (b:buffer a) = B.length (fst b)

let get (#a:Type) (h:HS.mem) (b:buffer a) (i:nat{i < length b /\ live_cell h (fst b) i (snd b)}) =
  let (| v, perms |) = B.get h (fst b) i in
  snd ((G.reveal perms).perm_map (G.reveal (snd b)))

val index (#a:Type) (h:HS.mem) (b:buffer a) (i:UInt32.t{UInt32.v i < length b})
  : Stack a (requires fun h -> live h b)
            (ensures fun h0 y h1 -> h0 == h1 /\ y == get h0 b (UInt32.v i))

let index #a h b i =
  let (| v, _ |) = B.index (fst b) i in
  v

let as_seq (#a:Type) (h:HS.mem) (b:buffer a) : GTot (s:Seq.seq a{Seq.length s == length b}) =
  let s = B.as_seq h (fst b) in
  Seq.init (length b) (fun x -> dfst (Seq.index s x)) 

let equiv_get_as_seq (#a:Type) (h:HS.mem) (b:buffer a) (i:nat{i < length b /\ live_cell h (fst b) i (snd b)})
  : Lemma (Seq.index (as_seq h b) i == get h b i)
  = ()
