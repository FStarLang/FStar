module MerkleTree

open FStar.Constructive

(* type of data and hashes, length indexed strings *)
type mstring :nat -> Type =
  | Base:  n:nat -> mstring n
  | Concat:#n:nat -> s1:mstring n -> s2:mstring n -> mstring (n + n)

assume val hash_size:nat
assume val data_size:nat

type data = mstring data_size
type hash = mstring hash_size

(* hash function *)
assume val gen_hash: #n:nat -> mstring n -> Tot (mstring hash_size)

let len = List.length

(*
 * merkel tree, indexed by the depth of the tree and hash for the present node
 * all data is stored in leaves, trees are complete
 *)
type mtree: nat -> hash -> Type =
  | L: data:data -> mtree 0 (gen_hash data)
  | N: #n:nat -> #h1:hash -> #h2:hash ->
       left:mtree n h1 ->
       right:mtree n h2 ->
       mtree (n + 1) (gen_hash (Concat h1 h2))

(* lookup function takes a path in the tree, true goes left, false goes right *)
type path = list bool

val get_elt: #h:hash -> path:path -> tree:mtree (len path) h -> Tot data
             (decreases path)
let rec get_elt #h path tree =
  match path with
    | [] -> L?.data tree
    | bit::path' ->
      if bit then
	get_elt #(N?.h1 tree) path' (N?.left tree)
      else
	get_elt #(N?.h2 tree) path' (N?.right tree)

(*
 * type for the proof stream which is a list of hashes and looked up data
 *)
type proof =
  | Mk_proof: data:data -> pstream:list hash -> proof

val lenp: proof -> Tot nat
let lenp p = len (Mk_proof?.pstream p)

val p_tail: p:proof{lenp p > 0} -> Tot proof
let p_tail p = Mk_proof (Mk_proof?.data p) (Cons?.tl (Mk_proof?.pstream p))

let p_data = Mk_proof?.data

let p_stream = Mk_proof?.pstream

(*
 * verifier takes as input a proof stream for certain lookup path
 * and computes the expected root node hash
 *)
val verifier: path:path -> p:proof{lenp p = len path} -> Tot hash
let rec verifier path p =
  match path with
    | [] -> gen_hash (p_data p)

    | bit::path' ->
      match p_stream p with
	| hd::_ ->
	  let h' = verifier path' (p_tail p) in
	  if bit then
	    gen_hash (Concat h' hd)
	  else
	    gen_hash (Concat hd h')

(*
 * prover function, generates a proof stream for a path
 *)
val prover: #h:hash ->
            path:path ->
            tree:mtree (len path) h ->
            Tot (p:proof{lenp p = len path})
	    (decreases path)
let rec prover #h path tree =
  match path with
    | [] -> Mk_proof (L?.data tree) []

    | bit::path' ->
      let N #dc #hl #hr left right  = tree in
      if bit then
	let p = prover path' left in
	Mk_proof (p_data p) (hr::(p_stream p))
      else
	let p = prover path' right in
	Mk_proof (p_data p) (hl::(p_stream p))

(*
 * correctness theorem: honest prover's proof stream is accepted by the verifier
 *)
val correctness: #h:hash ->
                 path:path ->
                 tree:mtree (len path) h ->
                 p:proof{p = prover path tree} ->
                 Lemma (requires True) (ensures (verifier path p = h))
                 (decreases path)
let rec correctness #h path tree p =
  match path with
    | [] -> ()
    | bit::path' ->
      if bit then
	correctness #(N?.h1 tree) path' (N?.left tree) (p_tail p)
      else
	correctness #(N?.h2 tree) path' (N?.right tree) (p_tail p)

(*
 * We prove a standard security definition that if verifier can be tricked into
 * accepting a proof of existence of an element, when the element is not actually
 * present, then we can provide a constructive proof of hash collision
 *)

type hash_collision =
    cexists (fun n -> cexists (fun (s1:mstring n) -> cexists (fun (s2:mstring n) ->
             u:unit{gen_hash s1 = gen_hash s2 /\ not (s1 = s2)})))

(*
 * security theorem: Only way a verifier can be tricked into accepting proof
 * stream for an non existent element is if there is a hash collision.
 *)
val security: #h:hash ->
              path:path ->
              tree:mtree (len path) h ->
              p:proof{lenp p = len path /\ verifier path p = h /\
                      not (get_elt path tree = p_data p)} ->
              Tot hash_collision
              (decreases path)
let rec security #h path tree p =
  match path with
    | [] -> ExIntro data_size (ExIntro (p_data p) (ExIntro (L?.data tree) ()))

    | bit::path' ->
      let N #dc #h1 #h2 left right = tree in
      let h' = verifier path' (p_tail p) in
      let hd = Cons?.hd (p_stream p) in
      if bit then
	if h' = h1 then
	  security path' left (p_tail p)
	else
	  ExIntro (hash_size + hash_size) (ExIntro (Concat h1 h2) (ExIntro (Concat h' hd) ()))
      else
	if h' = h2 then
	  security path' right (p_tail p)
	else
	  ExIntro (hash_size + hash_size) (ExIntro (Concat h1 h2) (ExIntro (Concat hd h') ()))
