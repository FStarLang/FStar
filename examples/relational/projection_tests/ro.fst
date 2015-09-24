(*--build-config
    options:--admit_fsi FStar.Set --z3timeout 15 --verify_module RoTest --project_module RoTest --project_module RoTest2 ;
    variables:LIB=../../../lib;
    other-files:$LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/all.fst $LIB/st2.fst $LIB/bytes.fst $LIB/list.fst ../sample.fst ../xor.fst ../ro.fst test.fst
  --*)

module RoTest

open FStar.Heap
open Ro
open Encryption
open TestPre

assume val sample_l : 'a -> ST Xor.block (requires (fun h -> True))
                                              (ensures  (fun h r h' -> equal h h'))

val hash_hon_l : key -> 'a -> St (option tag)
let hash_hon_l = l_PROJECT (iNLINE hash_hon)

val hash_adv_l : key -> St (option tag)
let hash_adv_l = l_PROJECT (iNLINE hash_adv)

val hash_hon2_l : key -> 'a -> St (option tag)
let hash_hon2_l = l_PROJECT (iNLINE hash_hon2)

(* This works, when the corresponding code in ../ro.fst is written in the correct 
    style, however this causes as bug..., so commenting for now *)
(*
val encrypt_hon_l : key -> Xor.block -> St (option (Xor.block * Xor.block))
let encrypt_hon_l = l_PROJECT (iNLINE encrypt_hon)
*)

module RoTest2

open FStar.Heap
open Ro
open TestPre

assume val sample_r : 'a -> ST Xor.block (requires (fun h -> True))
                                              (ensures  (fun h r h' -> equal h h'))


val hash_hon_r : key -> 'a -> St (option tag)
let hash_hon_r = r_PROJECT (iNLINE hash_hon)

val hash_adv_r : key -> St (option tag)
let hash_adv_r = r_PROJECT (iNLINE hash_adv)

val hash_hon2_r : key -> 'a -> St (option tag)
let hash_hon2_r = r_PROJECT (iNLINE hash_hon2)

(* This works, when the corresponding code in ../ro.fst is written in the correct 
    style, however this causes as bug..., so commenting for now *)
(*
val encrypt_hon_r : key -> Xor.block -> St (option (Xor.block * Xor.block))
let encrypt_hon_r = r_PROJECT (iNLINE encrypt_hon)
*)
