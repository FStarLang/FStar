(* Simple Encryption Scheme based on ro *)
module RandomOracle.Encryption

open FStar.Comp
open FStar.Heap
open Bijection
open Sample
open FStar.Relational
open Xor
open FStar.Bytes
open FStar.List
open RandomOracle.RO

assume val append : bytes -> bytes -> Tot bytes

(* We use a simple OTP as basis block for our encryption scheme *)
val encrypt : block -> block -> Tot block
let encrypt p k = xor p k
val decrypt : block -> block -> Tot block
let decrypt c k = xor c k

(* As our hash-key will be created by appending a random string to our
   encryption key, we need to require that encryption keys are prefixes of safe
   hash keys *)
opaque type safe_key_pre (k:double bytes) = 
  (forall (r:block). safe_key (rel_map2T append k (twice r)))

(* We prove that our sampling function is a bijection *)
opaque val encrypt_good_sample_fun : p1:block -> p2:block
  -> Lemma (good_sample_fun #block #block (fun x -> xor (xor p1 p2) x))
let encrypt_good_sample_fun p1 p2 =
  let sample_fun = (fun x -> xor (xor p1 p2) x) in
  cut (bijection #block #block sample_fun);
  bijection_good_sample_fun #block #block sample_fun

(* We prove that the identity function used for sampling  is a bijection *)
opaque val id_good_sample_fun : unit -> Lemma (good_sample_fun #block #block (fun x -> x))
let id_good_sample_fun () =
  cut (bijection #block #block (fun x -> x));
  bijection_good_sample_fun #block #block (fun x -> x)

#reset-options
(* If the random oracle is not in a bad state and if we used fresh hash-keys,
   then we can show that two the ciphertexts are equal *)
opaque val encrypt_hon : k:double key{safe_key_pre k}
                  -> p:double block ->
                  ST2 (double (option (block * block)))
                 (requires (fun h2 -> goodstate_hash (sel_rel1 h2 s)))
                 (ensures (fun h2' p h2 -> goodstate_hash (sel_rel1 h2 s)
                                           /\( not (or_irel (rel_map1T (fun s -> s.bad) (sel_rel1 h2 s)))
                                             ==> Ok (rel_map1T (fun s -> s.l)(sel_rel1 h2 s))
                                             /\ is_Some (R.l p) /\ is_Some (R.r p)
                                             /\ snd (Some.v (R.l p)) = snd (Some.v (R.r p))
                                             /\ (fresh_keys (rel_map2T append k (R (snd(Some.v #(block * block) (R.l p)))
                                                                                  (snd(Some.v #(block * block) (R.r p)))))
                                                            (rel_map1T (fun s -> s.l) (sel_rel1 h2' s))
                                                            ==> eq_irel p))))
#reset-options
let encrypt_hon k p =
                  let sample_fun = (fun x -> xor (xor (R.l p) (R.r p)) x) in
                  id_good_sample_fun ();
                  encrypt_good_sample_fun (R.l p) (R.r p);
                  let r = sample #block #block (fun x -> x) in
                  let kh = rel_map2T append k r in

                  let h = hash_hon kh sample_fun in
                  (* Writing the code in this style causes the loss of some typing information *)
(*                   let c = rel_map3 (fun h p r -> if is_Some h then Some ((encrypt p (Some.v h)), r) else None) h p r in *)
                  let c = R (if is_Some (R.l h) then Some ((encrypt (R.l p) (Some.v (R.l h))), (R.l r)) else None)
                            (if is_Some (R.r h) then Some ((encrypt (R.r p) (Some.v (R.r h))), (R.r r)) else None) in 
                  c

(* We only show that decryption does not violate our relational invariants *)
#reset-options
opaque val decrypt_hon : k:double bytes{safe_key_pre k} ->
                  c:double(block * block){snd (R.l c) = snd (R.r c)} ->
                  ST2 (double (option block))
                 (requires (fun h2 -> goodstate_hash (sel_rel1 h2 s)))
                 (ensures (fun h2' p h2 -> goodstate_hash (sel_rel1 h2 s)))
let decrypt_hon k c =
                  let r = snd_rel c in
                  let kh = rel_map2T append k r in
                  id_good_sample_fun ();
                  let h = hash_hon kh (fun x -> x) in
                  (* Writing the code in this style causes the loss of some typing information *)
(*                   rel_map2T (fun h c -> if is_Some h then Some (decrypt (fst c) (Some.v h)) else None) h c *)
                  R (if is_Some (R.l h) then Some (decrypt (fst (R.l c)) (Some.v (R.l h))) else None)
                    (if is_Some (R.r h) then Some (decrypt (fst (R.r c)) (Some.v (R.r h))) else None)
