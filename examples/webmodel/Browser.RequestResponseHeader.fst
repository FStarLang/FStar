(*
  Defines the functionality related to request and response headers (from fetch.spec.whatwg.org)
*)
module Browser.RequestResponseHeader

open AuxiliaryFunctions
open Web.URI
open Browser.AuxiliaryDatatypes
open Secret.SecString
open Browser.Datatypes
open Web.Origin

module List = FStar.List.Tot

(* append a name/value to header list *)
val appendName : header -> headerfield -> headervalue -> Tot header 
let appendName h hf v = (hf,v)::h

val appendLemma : #s:secLevel -> r:requestFormat s -> hf:headerfield -> hv:headervalue{Headervalue?.hvs hv = s} ->  
		  Lemma (requires (isValidRequest r)) 
		  (ensures (isValidRequest ({r with reqhead = (appendName r.reqhead hf hv)}))) [SMTPat (appendName r.reqhead hf hv)]
let appendLemma #s r hf hv = ()

val appendSecLevelLemma : h:header -> hf:headerfield -> hv:headervalue -> Lemma (requires (checkHeaderSecLevel h /\ 
			  ((not (isForbiddenHeader hf)) && (not (isForbiddenRespHeader hf)) ==> Headervalue?.hvs hv = PublicVal) )) 
			  (ensures (checkHeaderSecLevel (appendName h hf hv))) [SMTPat (appendName h hf hv)]
let appendSecLevelLemma h hf hv = ()

(* delete all headers with name/value from header list *)
val removeName : header -> headerfield -> Tot header
let rec removeName h hf = 
  match h with
  | [] -> []
  | (f,v)::tl -> if f = hf then (removeName tl hf)
	       else (f,v)::(removeName tl hf)

(* set a name/value in header list *)
val setHeader : header -> headerfield -> headervalue -> Tot header
let setHeader h hf v = 
  let nh = removeName h hf in 
  appendName h hf v

val combineHeaderValues : h:headervalue{Headervalue?.hvs h = PublicVal} -> h':headervalue{Headervalue?.hvs h' = PublicVal} -> Tot headervalue
let combineHeaderValues h h' = Headervalue PublicVal (strcat #PublicVal (strcat #PublicVal (Headervalue?.hv h) ",") (Headervalue?.hv h'))

(* combine a name/value in header list *)
val combineHeader : header -> headerfield -> headervalue -> Tot header
let rec combineHeader h hf v =
  match h with 
  | [] -> [(hf,v)]
  | (f,ov)::tl -> if f = hf && (Headervalue?.hvs ov = PublicVal) && (Headervalue?.hvs v = PublicVal) then (f, combineHeaderValues ov v)::tl
		else (f,ov)::(combineHeader tl hf v)

(* determine header names as a string *)
val getHeaderNamesList : header -> Tot (list headerfield)
let rec getHeaderNamesList h = match h with
  | [] -> []
  | (f,_)::tl -> if (isCORSSafeReqHeader f) then getHeaderNamesList tl
	       else f::(getHeaderNamesList tl)

val getHeaderNamesString : list headerfield -> Tot string
let rec getHeaderNamesString h = match h with
  | [] -> ""
  | hd::tl -> hd ^ "," ^ (getHeaderNamesString tl)

val getHeaderNames : header -> Tot string
let getHeaderNames h = getHeaderNamesString (removeDuplicates (getHeaderNamesList h))

(* Only unique header names in the header *)
(* Do we need all header names with no repeatations or the ones which are not repeated *)
(* The commented text gives the latter *)
(* val getUniqueRespHeader : header -> list headerfield -> list headerfield -> Tot (list headerfield) *)
(* let rec getUniqueRespHeader h hf rep = *)
(*   match h with *)
(*   | [] -> hf *)
(*   | (f,v)::tl -> if (List.find (fun x -> x = f) rep <> None) then (getUniqueRespHeader tl hf rep) *)
(* 	       else  *)
(* 		 match (List.find (fun x -> x = f) hf) with *)
(* 		 | None -> getUniqueRespHeader tl (f::hf) rep *)
(* 		 | Some fl -> getUniqueRespHeader tl (remove_elem_list hf fl) (fl::rep) *)

val getUniqueRespHeaderList : header -> list headerfield -> Tot (list headerfield)
let rec getUniqueRespHeaderList h hfl =
  match h with
  | [] -> hfl
  | (f,v)::tl -> match (List.find (fun x -> x = f) hfl) with
	       | None -> (getUniqueRespHeaderList tl (f::hfl))
	       | Some _ -> (getUniqueRespHeaderList tl hfl)

val getUniqueRespHeader : header -> Tot (list headerfield)
let getUniqueRespHeader h = getUniqueRespHeaderList h []

val getDirName : string -> Tot (option csp_dir_name)
let getDirName s = match s with
  | "child-src" -> Some CSP_child_src
  | "connect-src" -> Some CSP_connect_src
  | "default-src" -> Some CSP_default_src 
  | "font-src" -> Some CSP_font_src
  | "frame-src" -> Some CSP_frame_src
  | "img-src" -> Some CSP_img_src
  | "manifest-src" -> Some CSP_manifest_src
  | "media-src" -> Some CSP_media_src
  | "object-src" -> Some CSP_object_src
  | "script-src" -> Some CSP_script_src
  | "style-src" -> Some CSP_style_src
  | "worker-src" -> Some CSP_worker_src
  | "base-uri" -> Some CSP_base_uri
  | "plugin-types" -> Some CSP_plugin_types
  | "sandbox" -> Some CSP_sandbox
  | "disown-opener" -> Some CSP_disown_opener
  | "form-action" -> Some CSP_form_action
  | "frame-ancestors" -> Some CSP_frame_ancestors
  | "navigate-to" -> Some CSP_navigate_to
  | _ -> None 
  
(* CSP Level 3 - 4.1.1. Set response’s CSP list *)
val setRespCSPList : actResponse -> Tot actResponse
let setRespCSPList resp = 
  let csp = getCSPDirectives resp in
  ActResponse (ActResponse?.arl resp) ({(ActResponse?.ar resp) with respCSP=csp})

(* set the response's https state *)
val setRespHTTPS : actResponse -> Tot actResponse
let setRespHTTPS resp = 
  let httpsString = (if (not (emptyList (ActResponse?.ar resp).respurl)) && (getScheme (firstElement (ActResponse?.ar resp).respurl) = "https") then "modern" 
		    else (ActResponse?.ar resp).respHTTPS) in
  ActResponse (ActResponse?.arl resp) ({(ActResponse?.ar resp) with respHTTPS=httpsString})


