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
module Part2.MerkleTreeUpdate_V0
open FStar.String
module L = FStar.List.Tot

//Length-indexed strings
let lstring (n:nat) = s:string{String.length s == n}

//Concatenating strings sums their lengths
let concat #n #m (s0:lstring n) (s1:lstring m)
  : lstring (m + n)
  = FStar.String.concat_length s0 s1;
    s0 ^ s1

//A parameter, lenght of the hash in characters, 
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


// Merkle tree, indexed by the depth of the tree and hash for the
// node. All data is stored in leaves, trees are complete.

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

type mtree' (n:nat) =
  | MTree : h:hash_t -> mtree n h -> mtree' n


let resource_id = list bool

let rec update_mtree'  (#h:hash_t)
                       (rid:resource_id)
                       (res:resource) 
                       (tree:mtree (L.length rid) h)
   : mtree' (L.length rid)
   = admit()
