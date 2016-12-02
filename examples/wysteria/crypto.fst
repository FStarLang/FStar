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
  R_assec? r /\ is_clos (R_assec.v r) /\ mem p (R_assec.ps r) /\
  (exists c. Conf.t c = T_red r /\ Conf.l c = Target /\ Conf.m c = Mode Par (singleton p))

opaque type server_prop_witness (#a:Type) (#b:Type) (x:a) (y:b) = True

opaque type server_prop (p:prin) (r:redex) (ps:prins) (x:varname) (e:exp) (dv:dvalue) =
  (exists (pi:tpar ps) (pi_final:protocol ps).{:pattern (server_prop_witness pi pi_final)}
     contains p pi /\ contains p (fst pi_final) /\
     tpre_assec #ps (pi, OrdMap.empty #prins #tconfig_sec #ps_cmp) ps x e /\
     T_red.r (Conf.t (Some.v (select p pi))) = r /\
     pstep_star #ps (pi, OrdMap.empty #prins #tconfig_sec #ps_cmp) pi_final /\
     T_val? (Conf.t (Some.v (select p (fst pi_final)))) /\
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

type client_entry =
  | CEntry: k:key -> msg:(prin * redex){client_key_prop k msg} -> mac:bytes -> client_entry

type server_entry =
  | SEntry: k:key -> msg:server_ret_type{server_key_prop k msg} -> mac:bytes -> server_entry

type client_log_t = ref (list client_entry)
type server_log_t = ref (list server_entry)

let client_log = ST.alloc #(list client_entry) []
let server_log = ST.alloc #(list server_entry) []

val mac_client_msg:
  p:prin -> r:redex -> k:key{client_key_prop k (p, r)}
  -> St (m:bytes{client_key_prop k (unmarshal_s #(prin * redex) m)} * bytes)
let mac_client_msg p r k =
  let msg = marshal #(prin * redex) (p, r) in
  let mac = mac k msg in
  client_log := (CEntry k (p, r) mac)::(!client_log);
  (msg, mac)

val verify_client_msg:
  k:client_key -> m:bytes -> t:bytes
  -> St (option (t:(prin * redex){client_key_prop k t}))
let verify_client_msg k m t =
  //let _ = admitP (client_key_prop k (unmarshal_s #(prin * redex) m)) in
  let b = verify k m t in
  if (not b) then None
  else
    let msg = unmarshal #(prin * redex) m in
    let found = Some? (List.find (fun (CEntry k' msg' mac') -> k = k' && msg' = msg && mac' = t) !client_log) in
    if found then Some msg
    else None

val mac_server_msg:
  p:prin -> r:redex -> ps:prins -> x:varname -> e:exp -> dv:dvalue
  -> k:key{server_key_prop k (p, r, ps, x, e, dv)}
  -> St (m:bytes{server_key_prop k (unmarshal_s #(server_ret_type) m)} * bytes)
let mac_server_msg p r ps x e dv k =
  let msg = marshal #server_ret_type (p, r, ps, x, e, dv) in
  let mac = mac k msg in
  server_log := (SEntry k (p, r, ps, x, e, dv) mac)::(!server_log);
  (msg, mac)

val verify_server_msg:
  k:server_key -> m:bytes -> t:bytes
  -> St (option (t:server_ret_type{server_key_prop k t}))
let verify_server_msg k m t =
  //let _ = admitP (server_key_prop k (unmarshal_s #(server_ret_type) m)) in
  let b = verify k m t in
  if (not b) then None
  else
    let msg = unmarshal #server_ret_type m in
    let found = Some? (List.find (fun (SEntry k' msg' mac') -> k = k' && msg' = msg && mac' = t) !server_log) in
    if found then Some msg
    else None

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
