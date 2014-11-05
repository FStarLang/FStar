module Format
open Prims.PURE
open String
open Array


type message = seq char
type msg (l:nat) = m:message{length m==l}

val append_inj_l: l:nat
               -> b1:message -> b2:message
               -> c1:message -> c2:message
               -> Pure unit
                       (requires (l==length b1 /\ l==length c1 /\ append b1 b2==append c1 c2))
                       (ensures \x -> (Equal b1 c1 /\ Equal b2 c2))
let rec append_inj_l l b1 b2 c1 c2 = match l with
  | 0 -> ()
  | _ -> append_inj_l (l - 1) (slice b1 1 l) b2 (slice c1 1 l) c2


(* let tag0 = create 1 0uy *)
(* let tag1 = create 1 1uy *)

(* type UInt16 (i:int) = (b2t (0 <= i) /\ b2t (i < 65536)) *)
(* type uint16 = i:int{UInt16 i} *)
(* assume logic val utf8: s:string -> Tot (m:message{length m <= strlen s}) //this spec is accurate for ASCII strings *)
(* assume logic val two:nat *)
(* assume logic val uint16_to_bytes: uint16 -> Tot (msg two) *)
(* type string16 = s:string{UInt16 (length (utf8 s))} *)

(* (\* assume UTF8_inj:   forall s0 s1.{:pattern (Equal (utf8 s0) (utf8 s1))} utf8 s0==utf8 s1 ==> s0==s1 *\) *)
(* assume UINT16_inj: forall s0 s1. Equal (uint16_to_bytes s0) (uint16_to_bytes s1) *)
(*                              ==> s0==s1 *)

(* logic val request : string -> Tot message *)
(* let request s = append tag0 (utf8 s) *)

(* logic val response: string16 -> string -> Tot message *)
(* let response s t = *)
(*   let lb = uint16_to_bytes (length (utf8 s)) in *)
(*   append tag1 (append lb  *)
(*                       (append (utf8 s)  *)
(*                               (utf8 t))) *)

(* (\* ask !v,v',s,s',t'. (Requested(v,s) /\ Responded(v',s',t')) -> (v <> v') *\) *)
(* (\* lemma *\)  *)
(* val req_resp_distinct: s:string -> s':string16 -> t':string -> Tot (u:unit{request s =!= response s' t'}) *)
(* let req_resp_distinct s s' t' = () *)

(* query ReqInj: forall s s'. request s==request s' ==> s==s' *)

(* (\* ask !v,s,s',t,t'. (Responded(v,s,t) /\ Responded(v,s',t')) -> (s = s' /\ t = t') *\) *)
(* (\* ask !v,v',s,s'. (Requested(v,s) /\ Requested(v',s') /\ v = v') -> (s = s') *\) *)
(* (\* ask !v,s,s',t,t'. (Responded(v,s,t) /\ Responded(v,s',t')) -> (s = s' /\ t = t') *\) *)
     
     


                                                               
                                                               




