module SPDZ.Sharing
open SPDZ.Fp
open Sample
open Bijection
open FStar.Relational
open FStar.Comp

(* The shares on both sides have to sum up to the respective secret.
   We assume that the first party is dishonest and that the second party is
   honest. Hence, the first shares are always equal in both runs, while the
   second shares are not related (high) *)
type shared (secret:double fp) = s:double (fp*fp)
                                    {fst(R.l s) = fst(R.r s)
                                  /\ add_fp (fst(R.l s)) (snd(R.l s)) = R.l secret
                                  /\ add_fp (fst(R.r s)) (snd(R.r s)) = R.r secret}

(* We show that the identity function used for sampling is a bijection *)
opaque val id_good_sample_fun : unit -> Lemma (good_sample_fun #fp #fp (fun x -> x))
let id_good_sample_fun () =
  cut (bijection #fp #fp (fun x -> x));
  bijection_good_sample_fun #fp #fp(fun x -> x)

(* Simple sharing algorithm *)
opaque val share : h:double fp -> St2 (shared h)
let share h = id_good_sample_fun ();
              let s0 = sample (fun x -> x) in
              let s1 = rel_map2T minus_fp h s0 in
              let p = pair_rel s0 s1 in
              p

(* For reconstruction all  shares have to be of eq type since they are
   published *) opaque val reconstruct : h:double fp -> s:shared h{eq_irel s}
                  -> Tot (r:(eq fp){r=h})
let reconstruct _ s  = rel_map1T (fun (a,b) -> add_fp a b) s


