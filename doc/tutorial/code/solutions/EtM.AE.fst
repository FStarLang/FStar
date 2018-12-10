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
module EtM.AE

open FStar.Seq
open FStar.Monotonic.Seq
open FStar.HyperStack
open FStar.HyperStack.ST

open EtM

open Platform.Bytes
open CoreCrypto

module HST = FStar.HyperStack.ST

type rid = HST.erid
type cipher = (CPA.cipher * MAC.tag)

type log_t (r:rid) = Monotonic.Seq.log_t r (CPA.msg * cipher)


abstract noeq type key =
  | Key:  #region:rid ->
               ke:CPA.key { extends (CPA.Key?.region ke) region  } ->
               km:MAC.key { extends (MAC.Key?.region km) region /\
                 (disjoint( CPA.Key?.region ke) (MAC.Key?.region km)) } ->
               log:log_t region -> key

abstract let get_log (m:mem) (k:key) =
  sel m k.log


abstract let get_mac_log (m:mem) (k:key) =
  sel m (MAC.Key?.log k.km)

abstract let get_cpa_log (m:mem) (k:key) =
  sel m (CPA.Key?.log k.ke)


// BEGIN: EtMAEInvariant
abstract let invariant (h:mem) (k:key) =
  let log = get_log h k in
  let mac_log = get_mac_log h k in
  let cpa_log = get_cpa_log h k in
  Map.contains (get_hmap h) k.region /\
  Map.contains (get_hmap h) (MAC.Key?.region k.km) /\
  Map.contains (get_hmap h) (CPA.Key?.region k.ke) /\
  Seq.length log = Seq.length mac_log /\
  Seq.length mac_log = Seq.length cpa_log /\
  (forall (i:int). indexable log i ==>
    (let m1,t = Seq.index mac_log i in
     let m2,c = Seq.index cpa_log i in
     m1 = c /\
     Seq.index log i == (m2,(c,t))
    )
  )
// END: EtMAEInvariant




abstract let genPost parent h0 (k:key) h1 =
    modifies Set.empty h0 h1
  /\ extends k.region parent
  /\ HyperStack.fresh_region k.region h0 h1
  /\ Map.contains (get_hmap h1) k.region
  /\ contains h1 k.log
  /\ sel h1 k.log == createEmpty
  /\ invariant h1 k


abstract val keygen: parent:rid -> ST key
  (requires (fun _ -> HST.witnessed (HST.region_contains_pred parent)))
  (ensures  (genPost parent))


let keygen parent =
  let region = new_region parent in
  let ke = CPA.keygen region in
  let ka = MAC.keygen region in
  let log = alloc_mref_seq region createEmpty in
  Key #region ke ka log


abstract let region_of (k:key) :rid = k.region

abstract let log_of (k:key) :(log_t (region_of k)) = k.log

abstract val encrypt: k:key -> m:Plain.plain -> ST cipher
  (requires (fun h0 -> invariant h0 k))
  (ensures  (fun h0 c h1 ->
    (let log0 = get_log h0 k in
     let log1 = get_log h1 k in
     HyperStack.modifies_transitively (Set.singleton (region_of k)) h0 h1
     /\ log1 == snoc log0 (m, c)
     /\ witnessed (at_least (Seq.length log0) (m, c) (log_of k))
     /\ invariant h1 k)))


#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1 --z3rlimit 100"
// BEGIN: EtMAEEncrypt
let encrypt k plain =
  (* let h0 = ST.get () in *)
  let c = CPA.encrypt k.ke plain in
  let t = MAC.mac k.km c in
  write_at_end k.log (plain, (c, t));
  (c, t)
// END: EtMAEEncrypt

abstract val decrypt: k:key -> c:cipher -> ST (option Plain.plain)
  (requires (fun h0 -> invariant h0 k))
  (ensures (fun h0 res h1 ->
    modifies_none h0 h1 /\
    invariant h1 k /\
      ( (b2t Ideal.uf_cma /\ Some? res) ==>
        (Some? (seq_find (fun (_,c') -> c = c') (get_log h0 k)))

   (* CH*MK: If we wanted to also prove correctness of the EtM.AE
      we would use this stronger post-condition:
      
	Seq.mem (Some.v res, c) (sel h0 k.log) *)

      )
  ))

// BEGIN: EtMAEDecrypt
let decrypt k (c,tag) =
  if MAC.verify k.km c tag
  then ( Some (CPA.decrypt k.ke c) )
  else ( None )
// END: EtMAEDecrypt
