module EtM.AE

open FStar.Seq
open FStar.SeqProperties
open FStar.Monotonic.Seq
open FStar.HyperHeap
open FStar.Monotonic.RRef

open EtM

open Platform.Bytes
open CoreCrypto

type cipher = (CPA.cipher * MAC.tag)

type log_t (r:rid) = Monotonic.Seq.log_t r (CPA.msg * cipher)


noeq type key =
  | Key:  #region:rid ->
               ke:CPA.key { extends (CPA.Key.region ke) region  } ->
               km:MAC.key { extends (MAC.Key.region km) region /\
                 (disjoint( CPA.Key.region ke) (MAC.Key.region km)) } ->
               log:log_t region -> key

let get_log (h:t) (k:key) =
  m_sel h k.log

let get_mac_log (h:t) (k:key) =
  m_sel h (MAC.Key.log k.km)

let get_cpa_log (h:t) (k:key) =
  m_sel h (CPA.Key.log k.ke)

let invariant (h:t) (k:key) =
  let log = get_log h k in
  let mac_log = get_mac_log h k in
  let cpa_log = get_cpa_log h k in
  Map.contains h k.region /\
  Map.contains h (MAC.Key.region k.km) /\
  Map.contains h (CPA.Key.region k.ke) /\
  Seq.length log = Seq.length mac_log /\
  Seq.length mac_log = Seq.length cpa_log /\
  (forall (i:int). indexable log i ==>
    (let m1,t = Seq.index mac_log i in
     let m2,c = Seq.index cpa_log i in
     m1 = c /\
     Seq.index log i = (m2,(c,t))
    )
  )




let genPost parent h0 (k:key) h1 =
    modifies Set.empty h0 h1
  /\ extends k.region parent
  /\ fresh_region k.region h0 h1
  /\ Map.contains h1 k.region
  /\ m_contains k.log h1
  /\ m_sel h1 k.log == createEmpty
  /\ invariant h1 k


val keygen: parent:rid -> ST key
  (requires (fun _ -> True))
  (ensures  (genPost parent))


let keygen parent =
  let region = new_region parent in
  let ke = CPA.keygen region in
  let ka = MAC.keygen region in
  let log = alloc_mref_seq region createEmpty in
  Key #region ke ka log


val encrypt: k:key -> m:Plain.plain -> ST cipher
  (requires (fun h0 -> invariant h0 k))
  (ensures  (fun h0 c h1 ->
    (let log0 = get_log h0 k in
     let log1 = get_log h1 k in
     modifies (Set.singleton k.region)  h0 h1
     /\ log1 == snoc log0 (m, c)
     /\ witnessed (at_least (Seq.length log0) (m, c) k.log)
     /\ invariant h1 k)))

#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1 --z3timeout 100"
let encrypt k plain =
  (* let h0 = ST.get () in *)
  let c = CPA.encrypt k.ke plain in
  let t = MAC.mac k.km c in
  write_at_end k.log (plain, (c, t));
  (* let h1 = ST.get () in *)
  //following assertions seem no longer needed
  (* cut (Seq.length (get_log h1 k) = (Seq.length (get_log h0 k)) + 1);   *)
  (* cut (Seq.length (get_mac_log h1 k) = Seq.length (get_cpa_log h1 k)); *)
  (* cut (Seq.length (get_mac_log h1 k) = Seq.length (get_log h1 k));   *)
  (* cut (Seq.index (get_mac_log h1 k) (Seq.length (get_mac_log h1 k)-1) = (c,t)); *)
  (* cut (Seq.index (get_cpa_log h1 k) (Seq.length (get_cpa_log h1 k)-1) = (plain,c)); *)
  (* cut (Seq.index (get_log h1 k) (Seq.length (get_log h1 k)-1) = (plain,c,t));  *)
  (* assert *)
  (* ( let log  = get_log h1 k in *)
  (*   let mac_log = get_mac_log h1 k in *)
  (*   let cpa_log = get_cpa_log h1 k in *)
  (*   (forall (i:int). indexable log i ==> *)
  (*     (let m1,t = Seq.index mac_log i in *)
  (*     let m2,c = Seq.index cpa_log i in *)
  (*     m1 = c /\ *)
  (*     Seq.index log i = (m2,c,t) /\ *)
  (*     True) *)
  (*   ) *)
  (*   ); *)
  (c, t)

//assume AE_needs_CMA: ((b2t Ideal.uf_cma) <==> Ideal.ind_cpa)

val decrypt: k:key -> c:cipher -> ST (option Plain.plain)
  (requires (fun h0 -> invariant h0 k))
  (ensures (fun h0 res h1 ->
    modifies_none h0 h1 /\
    invariant h1 k /\
      ( (b2t Ideal.uf_cma /\ is_Some res) ==>
        SeqProperties.mem (Some.v res, c) (m_sel h0 k.log)
        (* (let log = get_log h0 k in *)
        (*   let found = seq_find  *)
        (*     ( *)
        (*       fun (_,c',tag') ->  *)
        (*     	  c'= fst c && tag' = snd c *)
        (*     ) log in *)
        (*   is_Some found /\  *)
        (*   (\* ( let Some (p',_,_) = found  in *\) *)
   	(*   (\*   p = Some(p')  *\) *)
	(*   (\* ) /\ *\) *)
	(*   True *)
        (* ) *)
      )
  ))

let decrypt k (c,tag) =
  if MAC.verify k.km c tag
  then (
    if (Ideal.uf_cma) then
      (
      let h = ST.get () in
      assert ( SeqProperties.mem (c,tag) (get_mac_log h k) );
      (* assume ( forall c tag. SeqProperties.mem (c,tag) (get_mac_log h k) ==> *)
      (*             (exists p. SeqProperties.mem (p,c) (get_cpa_log h k) )); *)
      (* assert ( exists p. SeqProperties.mem (p,c) (get_cpa_log h k)); *)
      assume ( is_Some (seq_find (fun mc -> snd mc = c) (get_cpa_log h k) ));

      let p = CPA.decrypt k.ke c in
      assert ( SeqProperties.mem (p,c) (get_cpa_log h k) );
      (* assert ( is_Some (seq_find (fun (p',c') -> (p',c') = (p,c)) (get_cpa_log h k) ) );
         -- this one used to work *)
      //assert ( is_Some (seq_find (fun (p',c',tag') -> (p',c',tag') = (p,c,tag)) (get_log h k) ) );
      assume (SeqProperties.mem (p, (c,tag)) (get_log h k));
      Some(p)
      )
    else
      (
      Some(CPA.decrypt k.ke c)
      )
  )
  else ( None )
