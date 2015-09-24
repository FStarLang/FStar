(*--build-config
    options:--admit_fsi FStar.Set --z3timeout 30 --project_module SpdzTest --verify_module SpdzTest ;
    variables:LIB=../../../lib;
    other-files:$LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/all.fst $LIB/st2.fst ../sample.fst ../spdz.fst test.fst
  --*)

module SpdzTest

open FStar.Heap
open Fp
open Sharing
open MPC
open Triples
open TestPre


assume val sample_l : 'a -> ST (fp) (requires (fun h -> True))
                                       (ensures  (fun h r h' -> equal h h'))
type shared (h:fp) = p:(fp * fp){fst p + snd p = h}

val share_l : x:fp -> St (shared x)
let share_l = l_PROJECT (iNLINE share)

val reconstruct_l : h:fp -> shared h -> Tot (r:fp{r = h})
let reconstruct_l = l_PROJECT (iNLINE reconstruct)

val triple_a_l : fp -> St (r:(h:fp & shared h))
let triple_a_l = l_PROJECT (iNLINE triple_a)

val triple_c_l : a:fp -> b:fp -> St (r:(h:fp & shared h){dfst r = mul_fp a b})
let triple_c_l = l_PROJECT (iNLINE triple_c)

val triple_l : fp -> fp -> St(r:((ha:fp & shared ha) * (hb:fp & shared hb) * (hc:fp & shared hc)){dfst(thd3 r) = mul_fp (dfst(fst3 r)) (dfst(snd3 r))})
let triple_l = l_PROJECT(iNLINE triple)

let add_loc_l = l_PROJECT (iNLINE add_loc)
val add_mpc_l : h0:fp -> h1:fp -> s0:shared h0 -> s1:shared h1 -> Tot (shared (add_fp h0 h1))
let add_mpc_l = l_PROJECT(iNLINE add_mpc)

let scalar_mul_loc_l = l_PROJECT (iNLINE scalar_mul_loc)
val scalar_mul_mpc_l : h0:fp -> a:fp -> s0:shared h0 -> Tot (shared (mul_fp a h0))
let scalar_mul_mpc_l = l_PROJECT(iNLINE scalar_mul_mpc)

let add_const_loc_l = l_PROJECT (iNLINE add_const_loc)
val add_const_mpc_l : h0:fp -> a:fp -> s0:shared h0 -> Tot (shared (add_fp a h0))
let add_const_mpc_l = l_PROJECT(iNLINE add_const_mpc)

let minus_loc_l = l_PROJECT (iNLINE minus_loc)
val minus_mpc_l : h0:fp -> h1:fp -> s0:shared h0 -> s1:shared h1 -> Tot (shared (minus_fp h0 h1))
let minus_mpc_l = l_PROJECT(iNLINE minus_mpc)

val mul_mpc_l : h0:fp -> h1:fp -> s0:shared h0 -> s1:shared h1 -> St (shared (mul_fp h0 h1))
let mul_mpc_l = l_PROJECT(iNLINE mul_mpc)
