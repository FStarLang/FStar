(*--build-config
    options:--admit_fsi FStar.OrdSet --admit_fsi FStar.OrdMap --admit_fsi FStar.Set --admit_fsi Ffibridge --admit_fsi FStar.Seq  --admit_fsi Runtime --admit_fsi FStar.IO --admit_fsi FStar.String --__temp_no_proj PSemantics --verify_module Crypto;
    variables:CONTRIB=../../contrib;
    other-files:classical.fst ext.fst set.fsi heap.fst st.fst all.fst seq.fsi seqproperties.fst ghost.fst listTot.fst ordset.fsi ordmap.fsi list.fst io.fsti string.fst prins.fst ast.fst ffibridge.fsi sem.fst psem.fst $CONTRIB/Platform/fst/Bytes.fst runtime.fsi print.fst $CONTRIB/CoreCrypto/fst/CoreCrypto.fst ../crypto/sha1.fst
 --*)

module Crypto

open FStar.OrdMap
open FStar.OrdSet

open Prins
open AST
open Runtime

open Semantics
open PSemantics

open Platform.Bytes

open SHA1

opaque type client_prop (p:prin) (r:redex) =
  is_R_assec r /\ is_clos (R_assec.v r) /\ mem p (R_assec.ps r) /\
  (exists c. Conf.t c = T_red r /\ Conf.l c = Target /\ Conf.m c = Mode Par (singleton p))

opaque type server_prop_witness (#a:Type) (#b:Type) (x:a) (y:b) = True

opaque type server_prop (p:prin) (r:redex) (ps:prins) (x:varname) (e:exp) (dv:dvalue) =
  (exists (pi:tpar ps) (pi_final:protocol ps).{:pattern (server_prop_witness pi pi_final)}
     contains p pi /\ contains p (fst pi_final) /\
     tpre_assec #ps (pi, OrdMap.empty #prins #tconfig_sec #ps_cmp) ps x e /\
     T_red.r (Conf.t (Some.v (select p pi))) = r /\
     pstep_star #ps (pi, OrdMap.empty #prins #tconfig_sec #ps_cmp) pi_final /\
     is_T_val (Conf.t (Some.v (select p (fst pi_final)))) /\
     D_v (T_val.meta (Conf.t (Some.v (select p (fst pi_final)))))
	 (T_val.v (Conf.t (Some.v (select p (fst pi_final))))) = dv)

(* TODO: The /\ True is to disable its extraction, file a bug in extraction *)
(* logic *) type client_prop_t (t:prin * redex) = client_prop (fst t) (snd t) /\ True

(* The /\ True is to disable its extraction *)
type server_prop_t (t:Tuple6 prin redex prins varname exp dvalue) =
  server_prop (MkTuple6._1 t) (MkTuple6._2 t) (MkTuple6._3 t) (MkTuple6._4 t) (MkTuple6._5 t) (MkTuple6._6 t) /\ True

(* TODO: plug in a concrete mac *)
val mac: key -> bytes -> Tot bytes
let mac k m = SHA1.hmac_sha1 k m

val verify: key -> bytes -> bytes -> Tot bool
let verify k m t = mac k m = t

val mac_msg:
  #a:Type -> #key_prop:(key -> a -> Type)
  -> k:key -> x:a{key_prop k x}
  -> Tot (m:bytes{key_prop k (unmarshal_s #a m)} * bytes)
let mac_msg (#a:Type) (#key_prop:key -> a -> Type) k x =
  let msg = marshal #a x in
  let mac = mac k msg in
  (msg, mac)

val verify_mac:
  #a:Type -> #key_prop:(key -> a -> Type)
  -> k:key -> m:bytes -> t:bytes
  -> Tot (option (x:a{key_prop k x}))
let verify_mac (#a:Type) (#key_prop:key -> a -> Type) k m t =
  let _ = admitP (key_prop k (unmarshal_s #a m)) in
  let b = verify k m t in
  if (not b) then None
  else Some (unmarshal #a m)

assume logic type client_key_prop: key -> (prin * redex) -> Type
assume logic type server_key_prop: key -> server_ret_type -> Type

type client_key = k:key{client_key_prop k == client_prop_t}
type server_key = k:key{server_key_prop k == server_prop_t}

val client_keygen: unit -> Tot client_key
let client_keygen _ =
  let k = random keysize in
  assume (client_key_prop k == client_prop_t);
  k

val server_keygen: unit -> Tot server_key
let server_keygen _ =
  let k = random keysize in
  assume (server_key_prop k == server_prop_t);
  k

val mac_client_msg:
  p:prin -> r:redex -> k:key{client_key_prop k (p, r)}
  -> Tot (m:bytes{client_key_prop k (unmarshal_s #(prin * redex) m)} * bytes)
let mac_client_msg p r k = mac_msg #(prin * redex) #client_key_prop k (p, r)

val verify_client_msg:
  k:client_key -> m:bytes -> t:bytes
  -> Tot (option (t:(prin * redex){client_key_prop k t}))
let verify_client_msg k m t = verify_mac #(prin * redex) #client_key_prop k m t

val client_key_prop_to_client_prop_lemma:
  k:client_key -> t:(prin * redex){client_key_prop k t}
  -> Lemma (client_prop_t t)
let client_key_prop_to_client_prop_lemma k t =
  (* TODO: Why does this not follow from client_key defn. *)
  let _ = assume (client_key_prop k == client_prop_t) in
  ()

val client_prop_to_client_key_prop_lemma:
  k:client_key -> t:(prin * redex){client_prop_t t}
  -> Lemma (client_key_prop k t)
let client_prop_to_client_key_prop_lemma k t =
  (* TODO: Why does this not follow from client_key defn. *)
  let _ = assume (client_key_prop k == client_prop_t) in
  ()

val mac_server_msg:
  p:prin -> r:redex -> ps:prins -> x:varname -> e:exp -> dv:dvalue
  -> k:key{server_key_prop k (p, r, ps, x, e, dv)}
  -> Tot (m:bytes{server_key_prop k (unmarshal_s #(server_ret_type) m)} * bytes)
let mac_server_msg p r ps x e dv k =
  mac_msg #server_ret_type #server_key_prop k (p, r, ps, x, e, dv)

val verify_server_msg:
  k:server_key -> m:bytes -> t:bytes
  -> Tot (option (t:server_ret_type{server_key_prop k t}))
let verify_server_msg k m t = verify_mac #server_ret_type #server_key_prop k m t

(* val server_key_prop_to_server_prop_lemma: *)
(*   k:server_key -> t:server_ret_type{server_key_prop k t} *)
(*   -> Lemma (server_prop_t t) *)
(* let server_key_prop_to_server_prop_lemma k t = *)
(*   (\* TODO: Why does this not follow from client_key defn. *\) *)
(*   let _ = assume (server_key_prop k == server_prop_t) in *)
(*   () *)

(* val server_prop_to_server_key_prop_lemma: *)
(*   k:server_key -> t:server_ret_type{server_prop_t t} *)
(*   -> Lemma (server_key_prop k t) *)
(* let server_prop_to_server_key_prop_lemma k t = *)
(*   (\* TODO: Why does this not follow from client_key defn. *\) *)
(*   let _ = assume (server_key_prop k == server_prop_t) in *)
(*   () *)
