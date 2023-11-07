(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module MerkleTree
open FStar.String
module L = FStar.List.Tot

//SNIPPET_START: preliminaries

//Length-indexed strings
let lstring (n:nat) = s:string{String.length s == n}

//Concatenating strings sums their lengths
let concat #n #m (s0:lstring n) (s1:lstring m)
  : lstring (m + n)
  = FStar.String.concat_length s0 s1;
    s0 ^ s1

//A parameter, length of the hash in characters, 
//e.g., this would be 32, if a character is 1 byte
//and we're using SHA-256
assume
val hash_size:nat

//The type of a hashed value
let hash_t = lstring hash_size

//The hash function itself
assume
val hash (m:string) : hash_t

//The type of resources stored in the tree
let resource = string
//SNIPPET_END: preliminaries


// Merkle tree, indexed by the depth of the tree and hash for the
// node. All data is stored in leaves, trees are complete.

//SNIPPET_START: mtree
type mtree: nat -> hash_t -> Type =
  | L:
     res:resource ->
     mtree 0 (hash res)
       
  | N:
     #n:nat ->
     #hl:hash_t ->
     #hr:hash_t ->
     left:mtree n hl ->
     right:mtree n hr ->
     mtree (n + 1) (hash (concat hl hr))
//SNIPPET_END: mtree

// get takes a path in the tree, true goes left, false goes right

//SNIPPET_START: get
let resource_id = list bool

let rec get #h 
            (ri:resource_id)
            (tree:mtree (L.length ri) h)
  : Tot resource (decreases ri)
  = match ri with
    | [] -> L?.res tree
    | b::ri' ->
      if b then
	get ri' (N?.left tree)
      else
	get ri' (N?.right tree)
//SNIPPET_END: get

//SNIPPET_START: prover
type resource_with_evidence : nat -> Type =
  | RES:
      res:resource ->
      ri:resource_id ->
      hashes:list hash_t { L.length ri == L.length hashes } ->
      resource_with_evidence (L.length ri)

/// Retrieves data references by the path, together with the hashes
/// of the sibling nodes along that path
let rec get_with_evidence (#h:_)
                          (rid:resource_id)
                          (tree:mtree (L.length rid) h)
  : Tot (resource_with_evidence (L.length rid))
	(decreases rid)
  = match rid with
    | [] ->
      RES (L?.res tree) [] []

    | bit::rid' ->
      let N #_ #hl #hr left right = tree in
      let p = get_with_evidence rid' left in
      if bit then
	let p = get_with_evidence rid' left in
	RES p.res rid (hr :: p.hashes)
      else
	let p = get_with_evidence rid' right in
	RES p.res rid (hl :: p.hashes)
//SNIPPET_END: prover


//SNIPPET_START: compute_root_hash
let tail #n (p:resource_with_evidence n { n > 0 })
  : resource_with_evidence (n - 1)
  = RES p.res (L.tail p.ri) (L.tail p.hashes)

let rec compute_root_hash (#n:nat)
                          (p:resource_with_evidence n)
  : hash_t
  = let RES d ri hashes = p in
    match ri with
    | [] -> hash p.res

    | bit::ri' ->
      let h' = compute_root_hash (tail p) in
      if bit then
        hash (concat h' (L.hd hashes))
      else
        hash (concat (L.hd hashes) h')
//SNIPPET_END: compute_root_hash

//SNIPPET_START: verify
let verify #h #n (p:resource_with_evidence n) 
                 (tree:mtree n h)
  : bool
  = compute_root_hash p = h
//SNIPPET_END: verify

//SNIPPET_START: correctness

// Correctness theorem: 
//
// Using get_with_evidence's with compute_root_hash correctly
// reconstructs the root hash
let rec correctness (#h:hash_t)
                    (rid:resource_id)
                    (tree:mtree (L.length rid) h)
  : Lemma (ensures (verify (get_with_evidence rid tree) tree))
          (decreases rid)
  = match rid with
    | [] -> ()
    | bit::rid' ->
      let N left right = tree in
      if bit then
	correctness rid' left
      else
	correctness rid' right
//SNIPPET_END: correctness

//SNIPPET_START: hash_collision
type hash_collision =
  | Collision :
      s1:string ->
      s2:string {hash s1 = hash s2 /\ not (s1 = s2)} ->
      hash_collision
//SNIPPET_END: hash_collision

//SNIPPET_START: security

(* 
 * If [verify] can be tricked into accepting the evidence of [p] when
 * [p.res] is not actually present in the tree at [p.ri], then
 * we can exhibit a hash collision
 *)
let rec security (#n:nat) (#h:hash_t)
                 (tree:mtree n h)
                 (p:resource_with_evidence n {
                   verify p tree /\
                   not (get p.ri tree = p.res)
                 })
  : hash_collision
  = match p.ri with
    | [] -> Collision p.res (L?.res tree)
    | bit::rid' ->
      let N #_ #h1 #h2 left right = tree in
      let h' = compute_root_hash (tail p) in
      let hd :: _ = p.hashes in
      if bit then
	if h' = h1 then
	  security left (tail p)
	else (
          String.concat_injective h1 h' h2 hd;
          Collision (concat h1 h2) (concat h' hd)
        )
      else
	if h' = h2 then
	  security right (tail p)
	else (
          String.concat_injective h1 hd h2 h';
	  Collision (concat h1 h2) (concat hd h')
        )

//SNIPPET_END: security

//SNIPPET_START: update
let rec update #h 
               (rid:resource_id)
               (res:resource) 
               (tree:mtree (L.length rid) h)
   : Tot (h':_ & mtree (L.length rid) h')
         (decreases rid)
   = match rid with
     | [] -> (| _, L res |)
     | hd :: rid' -> 
       if hd
       then (
         let (| _, t |) = update rid' res (N?.left tree) in
         (| _, N t (N?.right tree) |)
       )
       else (
         let (| _, t |) = update rid' res (N?.right tree) in
         (| _, N (N?.left tree) t|)
       )
//SNIPPET_END: update


//SNIPPET_START: update_hint
type mtree' (n:nat) =
  | MTree : h:hash_t -> mtree n h -> mtree' n

val update_mtree'  (#h:hash_t)
                   (rid:resource_id)
                   (res:resource) 
                   (tree:mtree (L.length rid) h)
   : mtree' (L.length rid)
//SNIPPET_END: update_hint

//SNIPPET_START: update_mtree'
let rec update_mtree' #h 
                      (rid:resource_id)
                      (res:resource) 
                      (tree:mtree (L.length rid) h)
   : Tot (mtree' (L.length rid))
         (decreases rid)
   = match rid with
     | [] -> MTree _ (L res)
     | hd :: rid' -> 
       if hd
       then (
         let MTree _ t = update_mtree' rid' res (N?.left tree) in
         MTree _ (N t (N?.right tree))
       )
       else (
         let MTree _ t = update_mtree' rid' res (N?.right tree) in
         MTree _ (N (N?.left tree) t)
       )
//SNIPPET_END: update_mtree'
