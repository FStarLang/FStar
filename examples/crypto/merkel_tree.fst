module MerkelTree

(* crypto stuff, assumptions on injectivity of hash and concat functions *)
type mstring : nat -> Type

assume val hash_size:nat

assume val data_size:nat

assume val gen_hash: #n:nat -> mstring n -> Tot (mstring hash_size)

assume val concat: #n:nat -> mstring n -> mstring n -> Tot (mstring (n + n))

assume Injective_hash: (forall (n:nat) (s1:mstring n) (s2:mstring n).
                               gen_hash s1 = gen_hash s2 ==> s1 = s2)

assume Injective_concat: (forall (n:nat) (s1:mstring n) (s2:mstring n) (s3:mstring n) (s4:mstring n). concat s1 s2 = concat s3 s4 ==> (s1 = s3 /\ s2 = s4))

type data = mstring data_size

type hash = mstring hash_size

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
       mtree (n + 1) (gen_hash (concat h1 h2))

(* lookup function takes a path in the tree, true goes left, false goes right *)
type path = list bool

val get_elt: #h:hash -> path:path -> tree:mtree (len path) h -> Tot data
             (decreases path)
let rec get_elt h path tree =
  match path with
    | [] -> L.data tree
    | bit::path' ->
      if bit then
	get_elt path' (N.left tree)
      else
	get_elt path' (N.right tree)

(*
 * type for the proof stream which is a list of hashes and looked up data
 *)
type proof =
  | Mk_proof: data:data -> pstream:list hash -> proof

val lenp: proof -> Tot nat
let lenp p = len (Mk_proof.pstream p)

val p_tail: p:proof{lenp p > 0} -> Tot proof
let p_tail p = Mk_proof (Mk_proof.data p) (Cons.tl (Mk_proof.pstream p))

let p_data = Mk_proof.data

let p_stream = Mk_proof.pstream

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
	    gen_hash (concat h' hd)
	  else
	    gen_hash (concat hd h')

(*
 * security theorem: if verifier computed hash matches the root node hash,
 * then the tree indeed contains the looked up element
 *)
val security: #h:hash ->
              path:path ->
              tree:mtree (len path) h ->
              p:proof{lenp p = len path /\ verifier path p = h} ->
              Lemma (requires True) (ensures (get_elt path tree = p_data p))
              (decreases path)
let rec security h path tree p =
  match path with
    | [] -> ()
    | bit::path' ->
      match Mk_proof.pstream p with
	| hd::tl ->
	  if bit then
	    security path' (N.left tree) (p_tail p)
	  else
	    security path' (N.right tree) (p_tail p)

(*
 * prover function, generates a proof stream for a path
 *)
val prover: #h:hash ->
            path:path ->
            tree:mtree (len path) h ->
            Tot (p:proof{lenp p = len path})
	    (decreases path)
let rec prover h path tree =
  match path with
    | [] -> Mk_proof (L.data tree) []

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
let rec correctness h path tree p =
  match path with
    | [] -> ()
    | bit::path' ->
      if bit then
	correctness path' (N.left tree) (p_tail p)
      else
	correctness path' (N.right tree) (p_tail p)
