(*
  html.spec.whatwg.org
  Describes various browser functions related to navigation (postmessage, xmlhttprequest, formsubmission, navigatewindow) and 
  getting/setting location, domain, localstorage etc.
*)
module Browser.Model.Interface

open AuxiliaryFunctions
open Web.URI
open Browser.AuxiliaryDatatypes
open Secret.SecString
open Browser.Datatypes
open Browser.ContentSecurityPolicy
open Web.Origin
open Browser.HTTPFetch
open Browser.RequestResponseHeader
open FStar.IO

module List = FStar.List.Tot

#reset-options "--z3rlimit 50" 

(* Return document.domain *)
val get_document_domain : b:browser -> w:window{w.wbid = b.bid} -> Tot origin_domain
let get_document_domain b w =
  let d = w.w.wdoc in 
  (* if (noWindow (mk_adoc d)) then [] *)
  (* else *) 
  match getEffectiveDomain d with
       | None -> []
       | Some hd -> hd

(* Set document.domain : cannot set opaque origin using this function *)
val set_document_domain : b:browser -> w:window{w.wbid = b.bid} -> origin_domain -> Tot (result * cw:window{cw.wbid = b.bid} * nb:browser{nb.bid = b.bid})
let set_document_domain b w h =
  let d = w.w.wdoc in 
  if ((List.find (fun w -> w = SB_Domain) d.dsbox <> None) || h = []) then (Error "document.domain sbox", w, b) (* Security Error *)
  else
    let ed = (match getEffectiveDomain d with | Some hd -> hd | None -> []) in
    if (h <> ed && (origin_domain_match ed h = false)) then (Error "document.domain domain does not match", w, b)
    else if (not (is_opaqueDoc (mk_adoc d))) then
	let nw = setDocDomain #b w h in
	(Success "domain set", nw, Browser b.bid ({b.br with windows=(replacewin b b.br.windows (win_to_cowin w).cwin (win_to_cowin nw).cwin)}))
    else (Error "document.domain case should not arise", w, b) (* Case does not arise *)

(* 7.1.3 html.spec.whatwg.org - Security *)
private val hasBrowserScopeOrigin : #cbid:origin_opaque -> cowindow' cbid -> Tot bool
let rec hasBrowserScopeOrigin #cbid w =
  match w.cwparent with
  | None -> true
  | Some p -> (hasBrowserScopeOrigin p && (isSameOriginWin p w))

(* window.location
   Although 5.2.1 in HTML5 Spec allows access to location and window, it is not allowed in implementation
   7.7.4 of HTML5.1 Spec for Location object specifies same origin check. Further property accesses are also subject to this check
*)
val get_win_location : #s:secrecy_level -> b:browser -> c:cowindow{b.bid = c.cwbid} -> f:cowindow{b.bid = c.cwbid} -> Tot (result * option (c_uri s))
let get_win_location #s b c f =
  if c.cwbid = f.cwbid && isSameOriginWin c.cwin f.cwin && (URI?.uri_secrecy_level f.cwin.cwloc = s) then (Success "got location", (get_win_curi b c f))
  else (Error "win location error", None)

(* Get the parent window of the current window(c) *)
val get_parent : b:browser -> c:cowindow{c.cwbid = b.bid} -> Tot (cw:cowindow{cw.cwbid = b.bid})
let get_parent b c = 
  match c.cwin.cwparent with
  | None -> c
  | Some wp -> CWindow c.cwbid wp

(* Get the localStorage for the current origin from the browser. 
   Return a modified browser if the localstorage is not present with a new empty store for that origin
*)
private val get_localStorage : b:browser -> o:origin_tuple -> 
			       Tot ((dictionary #(secret_string (SecretVal [SecOrigin o])) #(secret_string (SecretVal [SecOrigin o]))) * nb:browser{nb.bid = b.bid})
let get_localStorage b o = (getLSEntry b b.br.localStorage o, b)

(* Set the localStorage for the current origin using the dictionary provided 
   The dictionary is a list of key-value pairs with functions defined in BrowserDataTypes.fst
*)
private val set_localStorage : b:browser -> o:origin_tuple -> (dictionary #(secret_string (SecretVal [SecOrigin o])) #(secret_string (SecretVal [SecOrigin o]))) -> 
			       Tot (list (e:localStorageEntry{b.bid = e.lsb}))
let set_localStorage b o d = updateLSMap b b.br.localStorage o d 

(* Get the value associated with the key in the localstorage of the current window *)
(* One can call tw.localStorage but the "tw" is normally ignored and the getting/setting happens in the current window's localstorage *)
val get_item_localStorage : #s:secrecy_level -> b:browser -> cw:window{SecretVal [SecOrigin cw.w.wloc.uri_value.uri_origin] = s} -> 
			    option cowindow -> secret_string s -> Tot (result * (option (secret_string s)))
let get_item_localStorage #s b cw tw key =
  if (OpaqueOrigin? (URI?.uri_value cw.w.wloc).uri_origin) then (Error "localstorage origin error", None)
  else if (List.find (fun w -> w = SB_Origin) cw.w.wdoc.dsbox <> None) then (Error "localstorage sbox", None)
  else (
    let o = cw.w.wloc.uri_value.uri_origin in 
    let (d, nb) = (get_localStorage b o) in 
    (Success "got local storage item", (dictionary_get_value d key))
    )
  
(* Sets the localstorage of the current window with the key value pair specified in the item *)
val set_item_localStorage : #s:secrecy_level -> b:browser -> cw:window{SecretVal [SecOrigin cw.w.wloc.uri_value.uri_origin] = s} -> 
			    option cowindow -> secret_string s -> secret_string s -> Tot (result * nb:browser{nb.bid = b.bid})
let set_item_localStorage #s b cw tw key value =
  let o = cw.w.wloc.uri_value.uri_origin in 
  if (OpaqueOrigin? o) then (Error "setlocalstorage origin error", b)
  else if (List.find (fun w -> w = SB_Origin) cw.w.wdoc.dsbox <> None) then (Error "setlocalstorage sbox", b)
  else 
    let (d,nb) = (get_localStorage b o) in 
    let nd = (dictionary_set_value d key value) in 
    let nls = (set_localStorage nb o nd) in
    (Success "set local storage item", (Browser nb.bid ({nb.br with localStorage=nls})))

(* Post message from one window to another. The target origin (to) is the one that can receive this message. 
   Omitting transfer option for now. It deletes the current copy of the object in the current window when sending the message (literally transfer)
*)
val post_message : b:browser -> cw:cowindow{cw.cwbid = b.bid} -> tw:cowindow{tw.cwbid = b.bid} -> string -> string -> Tot (result)
let post_message b cw tw msg t_ori =
  let tori = ( match t_ori with
      | "*" -> None (* This allows msg to be passed to any origin. *)
      | "/" -> Some (getWinURI b cw)
      | l -> hstring_to_uri b l
    ) in
    match tori with
    | None -> Success "sent msg"
    | Some o -> if (isSameOriginURI o (getWinURI b tw)) then Success "sent msg" else Error "msg not sent"
		  
(* url.spec.whatwg.org -- 4.4 URL equivalence *)

(* val add_flag_sandbox : list sandbox_flags -> sandbox_flags -> Tot (list sandbox_flags) *)
(* let add_flag_sandbox l s = s::l *)
(* *)
(* val get_sandbox_flags : sandbox -> Tot (list sandbox_flags) *)
(* let get_sandbox_flags sb = *)
(*   let cb = (SB_Navigation::SB_Plugins::SB_StorageURL::[SB_Domain]) in  *)
(*   let pb = (if sb.sb_popups then (add_flag_sandbox cb SB_NewWindow) else cb) in *)
(*   let tb = (if sb.sb_topnavigation then (add_flag_sandbox pb SB_TopWindow) else pb) in  *)
(*   let ub = (if sb.sb_sameorigin then (add_flag_sandbox tb SB_Origin) else tb) in *)
(*   let fb = (if sb.sb_forms then (add_flag_sandbox ub SB_Forms) else ub) in  *)
(*   let lb = (if sb.sb_pointerlock then (add_flag_sandbox fb SB_PointerLock) else fb) in *)
(*   let jb = (if sb.sb_scripts then (add_flag_sandbox (add_flag_sandbox lb SB_Script) SB_Automatic) else lb) in  *)
(*   let eb = (if sb.sb_popupsEscape then (add_flag_sandbox jb SB_Propagate) else jb) in *)
(*   let mb = (if sb.sb_modals then (add_flag_sandbox eb SB_Modals) else eb) in  *)
(*   let ob = (if sb.sb_orientation then (add_flag_sandbox mb SB_Orientation) else mb) in  *)
(*   if sb.sb_presentation then (add_flag_sandbox ob SB_Presentation) *)
(*   else ob *)

(* Fails with -- Unknown assertion failed when number of "let" are more than 10 *)
(* Separated into two functions for now... *)
private val get_partial_sb_flags : sandbox -> Tot (list sandbox_flags)
let get_partial_sb_flags sb =
  let cb = (SB_Navigation::SB_NewWindow::SB_TopWindow::SB_Origin::SB_Forms::SB_PointerLock::SB_Plugins::SB_StorageURL::[SB_Domain]) in
  let pb = (if sb.sb_popups then (list_remove_element cb SB_NewWindow) else cb) in 
  let tb = (if sb.sb_topnavigation then (list_remove_element pb SB_TopWindow) else pb) in
  let ub = (if sb.sb_sameorigin then (list_remove_element tb SB_Origin) else tb) in
  let fb = (if sb.sb_forms then (list_remove_element ub SB_Forms) else ub) in
  (if sb.sb_pointerlock then (list_remove_element fb SB_PointerLock) else fb) 

(* Return the sandbox flags based on the sandbox attributes *)
private val get_sandbox_flags : sandbox -> Tot (list sandbox_flags)
let get_sandbox_flags sb =
  let partial = (SB_Script::SB_Automatic::SB_Propagate::SB_Modals::SB_Orientation::SB_Presentation::(get_partial_sb_flags sb)) in 
  let jb = (if sb.sb_scripts then (list_remove_element (list_remove_element partial SB_Script) SB_Automatic) else partial) in
  let eb = (if sb.sb_popupsEscape then (list_remove_element jb SB_Propagate) else jb) in
  let mb = (if sb.sb_modals then (list_remove_element eb SB_Modals) else eb) in
  let ob = (if sb.sb_orientation then (list_remove_element mb SB_Orientation) else mb) in
  (if sb.sb_presentation then (list_remove_element ob SB_Presentation) else ob)

(* 7.6 Sandboxing - html.spec.whatwg.org *)
private val dirvalue_to_sandbox : list csp_directive_value -> sandbox -> Tot sandbox
let rec dirvalue_to_sandbox dv sb = 
  match dv with
  | [] -> sb
  | hd::tl -> 
    if (hd = (DV_SBox "allow-popups")) then 
      dirvalue_to_sandbox tl ({sb with sb_popups=(sb.sb_popups||true)})
    else if (hd = (DV_SBox "allow-top-navigation")) then 
      dirvalue_to_sandbox tl ({sb with sb_topnavigation=(sb.sb_topnavigation||true)}) 
    else if (hd = (DV_SBox "allow-same-origin")) then 
      dirvalue_to_sandbox tl ({sb with sb_sameorigin=(sb.sb_sameorigin||true)}) 
    else if (hd = (DV_SBox "allow-forms")) then 
      dirvalue_to_sandbox tl ({sb with sb_forms=(sb.sb_forms||true)})  
    else if (hd = (DV_SBox "allow-scripts")) then 
      dirvalue_to_sandbox tl ({sb with sb_scripts=(sb.sb_scripts||true)})  
    else if (hd = (DV_SBox "allow-pointer-lock")) then 
      dirvalue_to_sandbox tl ({sb with sb_pointerlock=(sb.sb_pointerlock||true)}) 
    else if (hd = (DV_SBox "allow-popups-to-escape-sandbox")) then 
      dirvalue_to_sandbox tl ({sb with sb_popupsEscape=(sb.sb_popupsEscape||true)})
    else if (hd = (DV_SBox "allow-modals")) then 
      dirvalue_to_sandbox tl ({sb with sb_modals=(sb.sb_modals||true)})  
    else if (hd = (DV_SBox "allow-orientation-lock")) then 
      dirvalue_to_sandbox tl ({sb with sb_orientation=(sb.sb_orientation||true)}) 
    else if (hd = (DV_SBox "allow-presentation")) then 
      dirvalue_to_sandbox tl ({sb with sb_presentation=(sb.sb_presentation||true)}) 
    else  
      dirvalue_to_sandbox tl sb

private val get_sandbox_from_CSP : csp_policy -> Tot (list sandbox_flags)
let rec get_sandbox_from_CSP p =
  match p with
  | [] -> [] 
  | ph::pt -> ( match ph.directive_name with
	      | CSP_sandbox -> get_sandbox_flags (dirvalue_to_sandbox ph.directive_value ({sb_forms=false;sb_modals=false;sb_orientation=false;sb_pointerlock=false;sb_popups=false;sb_popupsEscape=false;sb_presentation=false;sb_sameorigin=false;sb_scripts=false;sb_topnavigation=false}))
	      | _ -> get_sandbox_from_CSP pt)

private val join_flags : list sandbox_flags -> list sandbox_flags -> Tot (list sandbox_flags)
let join_flags ls1 ls2 = List.append ls1 ls2

(* check if we need to parse the remaining list *)
(* private val string_to_referrer_policy : list string -> Tot referrer_policy *)
(* let string_to_referrer_policy ls = *)
(*   match ls with *)
(*   | [] -> RP_EmptyPolicy *)
(*   | h::tl -> if h = "no-referrer" then RP_NoReferrer *)
(* 	   else if h = "no-referrer-when-downgrade" then RP_NoRefWhenDowngrade *)
(* 	   else if h = "same-origin" then RP_SameOrigin *)
(* 	   else if h = "origin" then RP_Origin *)
(* 	   else if h = "strict-origin" then RP_StrictOrigin *)
(* 	   else if h = "origin-when-cross-origin" then RP_OriginWhenCO     *)
(* 	   else if h = "strict-origin-cross-origin" then RP_StrictWhenCO    *)
(* 	   else if h = "unsafe-url" then RP_UnsafeURL  *)
(* 	   else RP_EmptyPolicy  *)
  
(*Section 6.7.1 of HTML5.1 spec defines navigating documents. (7.8.1 in the WHATWG HTML5.1 spec)
  For example, following a hyperlink, Section 4.10.22 Form submission, and the window.open() and location.assign() methods can all cause a browsing context to navigate.
  Navigation takes in a window(sw) that is the source responsible for starting the navigation of the target window(tw)
  assume val hyperlink_navigation : b:browser -> w:window -> t:window -> h:uri -> Tot (option window)
  ir indicates isRequestResource
*)
(* 7.8.1 -- process a navigate response *)
private val processNavigateResponseSub : b:browser -> req:browserRequest{b.bid = req.browser_request.reqbrowser} -> 
					 oresp:browserResponse{is_valid_browser_response_for_request req oresp} -> 
					 bool -> sw:cowindow{sw.cwbid = b.bid} -> tw:cowindow{tw.cwbid = b.bid} -> navType -> 
					 Tot (result * option (w:cowindow{w.cwbid = b.bid}) * nb:browser{nb.bid = b.bid})
let processNavigateResponseSub b req oresp ir sw tw ty =
  if (navRespBlockedCSP req ty (oresp) sw tw) then ((Error "navigation response blocked by CSP"), None, b)
  else if oresp.b_response.respcode = 204 || oresp.b_response.respcode = 205 then (Success "done navigate response", Some tw, b)
  else
      let referrer = (if ir then (match (BrowserRequest?.browser_request req).reqref with | NoReferrer -> blank_uri | Client w -> w.cwin.cwloc | URLReferrer u -> u) 
		     else blank_uri) in
      let flags = (match tw.cwin.cwparent with
		  | None -> join_flags (get_sandbox_from_CSP oresp.b_response.respCSP) tw.cwin.cwsbox
		  | Some p -> join_flags (join_flags (get_sandbox_from_CSP oresp.b_response.respCSP) tw.cwin.cwsbox) (getSBox p.cwdoc)) in
      let rurl = (List.hd (BrowserRequest?.browser_request req).requrl) in (* Original fetch url is the document's url *)
      let rP = (parse_response_referrer_policy oresp) in
      let newdoc = ({dloc=rurl; dori=getAOrigin rurl; dref=referrer; dHTTPS=oresp.b_response.respHTTPS; drefPol=rP; dCSP=oresp.b_response.respCSP; dsbox=(flags)}) in
      let nwin = add_doc_hist #b.bid b (save_cur_doc_win b tw.cwin) newdoc in
      (Success "Response processed", Some (CWindow b.bid nwin), (Browser b.bid ({b.br with windows=(replacewin b b.br.windows tw.cwin nwin)}))) (* Add to STS state here?*)
		   
private val processNavigateResponse : b:browser -> req:browserRequest{b.bid = req.browser_request.reqbrowser} -> resp:response{is_valid_response_for_request req resp} -> 
				      bool -> sw:cowindow{sw.cwbid = b.bid} -> tw:cowindow{tw.cwbid = b.bid} -> navType -> 
				      Tot (result * option (w:cowindow{w.cwbid = b.bid}) * nb:browser{nb.bid = b.bid})
let processNavigateResponse b req resp ir sw tw ty =
  match resp with
  | NetworkError e -> (Error e, None, b) (* Error - document's origin is set to an opaque origin *)
  | RespSuccess s -> (Success s, Some tw, b)
  | BResponse oresp -> processNavigateResponseSub b req oresp ir sw tw ty

private val processNavigateFetchSub : b:browser -> 
				      req:browserRequest{notForbiddenHeaderfieldInReqHeader req.browser_request.reqhead /\ req.browser_request.reqbrowser = b.bid} -> 
				      sw:cowindow{sw.cwbid = b.bid} -> tw:cowindow{tw.cwbid = b.bid} -> navType -> 
				      Tot (result * option (w:cowindow{w.cwbid = b.bid}) * nb:browser{nb.bid = b.bid})
let processNavigateFetchSub b req sw targetw ty =
    if (navReqBlockedCSP req ty sw targetw) then (Error "navigation req blocked by CSP", None, b)
    else 
      let tw = targetw.cwin in 
      let nw = (CWindow b.bid ({cwinid=tw.cwinid; cwname=tw.cwname; cwloc=(List.hd req.browser_request.requrl); cwframes=tw.cwframes; cwopener=tw.cwopener; cwparent=tw.cwparent; cwhist=tw.cwhist; cwdoc=tw.cwdoc; cwsbox=tw.cwsbox})) in
      let nb = Browser b.bid ({b.br with windows=(replacewin b b.br.windows tw nw.cwin)}) in
      let (re, _, sb) = (fetch_resource nb req false false (sw, nw, ty)) in (* should we use the request that has come back here? *)
      (re, Some nw, sb) (* Send the newwin *)

(* 7.8.1 -- Process a navigate fetch *)
private val processNavigateFetch : b:browser -> req:browserRequest{notForbiddenHeaderfieldInReqHeader req.browser_request.reqhead /\ req.browser_request.reqbrowser = b.bid} -> 
				   sw:cowindow{sw.cwbid = b.bid} -> tw:cowindow{tw.cwbid = b.bid} -> navType -> 
				   Tot (result * option (w:cowindow{w.cwbid = b.bid}) * nb:browser{nb.bid = b.bid})
let processNavigateFetch b req sw tw ty =
  let r = req.browser_request in 
  let ruri = (List.hd r.requrl) in 
  if ((is_uri_equal ruri (getWinURI b tw) true) && (not (emptyFragment ruri))) then   (* Clear all history entries *)
    (Success "fragment", Some tw, b) (* Happens if its not reload -- Navigate to the fragment *)
  else
    let ori = ((* if ((r.reqm <> "GET" || ty = "form-submission") && (not (is_opaqueWin sw))) then (false, r.reqo) *)
	      if (tw.cwin.cwparent <> None && hasBrowserScopeOrigin (Some?.v tw.cwin.cwparent)) then 
		(getAOrigin (Some?.v tw.cwin.cwparent).cwloc)
	      else r.reqo) in
    let nreq = BrowserRequest req.breq_secrecy_level ({r with reqo = ori; reqw = (Some sw); reqdest = "document"; reqtarget = (Some tw); reqredmode = "manual"; reqmode = Navigate; reqcredm = "include"; reqcredflag = true; corsflag = false; corspfflag = false; authflag = false; recflag = false}) in
    processNavigateFetchSub b nreq sw tw ty
    
(* 7.8.1 -- Navigate a browsing context *)
(* TODO - update the windows details to the request url *)
val navigateWindow: b:browser -> sw:cowindow{sw.cwbid = b.bid} -> tw:cowindow{tw.cwbid = b.bid} -> resource b -> navType -> 
		    Tot (result * option (nr:browserRequest{notForbiddenHeaderfieldInReqHeader (BrowserRequest?.browser_request nr).reqhead /\ 
				  nr.browser_request.reqbrowser = b.bid}) * option (w:cowindow{w.cwbid = b.bid}) * nb:browser{nb.bid = b.bid})
let navigateWindow b sw tw r nType =
  if (allowed_navigation sw.cwin tw.cwin = false) then ((Error "navigation not allowed"), None, None, b)
  else 
    match r with
    | RequestResource req -> (match processNavigateFetch b req sw tw nType with | (res, w, nb) -> (res, Some req, w, nb))  
    | ResponseResource req resp -> (match (processNavigateResponse b req resp false sw tw nType) with | (res, w, nb) -> (res, None, w, nb))
      
(* 7.8.1 -- Process a navigate fetch's response *)
private val processNavigateFetchRespSub : b:browser -> r:browserRequest{notForbiddenHeaderfieldInReqHeader r.browser_request.reqhead /\ b.bid = r.browser_request.reqbrowser} -> 
					  resp:browserResponse{is_valid_browser_response_for_request r resp /\ isRedirectResponse resp.b_response.respcode} -> 
					  sw:cowindow{sw.cwbid = b.bid} -> tw:cowindow{tw.cwbid = b.bid} -> navType -> 
					  Tot (result * option (nr:browserRequest{notForbiddenHeaderfieldInReqHeader (BrowserRequest?.browser_request nr).reqhead /\ 
							nr.browser_request.reqbrowser = b.bid}) * option (w:cowindow{w.cwbid = b.bid}) * nb:browser{nb.bid = b.bid})
let processNavigateFetchRespSub b req resp sw tw ty =
  match resp.b_response.resploc with
  | Some (Failure) -> let (re, _, sb) = httpRedirectFetch b req resp false (sw, tw, ty) in (* processNavigateFetchResp after getting back new response *)
		     (re, Some req, Some tw, sb)
  | Some (URL u) -> let prot = getScheme u in 
		   if prot = "http" || prot = "https" then 
		      let (re, _, sb) = httpRedirectFetch b req resp false (sw, tw, ty) in
		      (re, Some req, Some tw, sb)
		   else if prot = "blob" || prot = "file" || prot = "filesystem" || prot = "javascript" then 
		      (Error "incorrect protocol", None, None, b) (* Network Error *)
		   else if prot = "ftp" || prot = "about" || prot = "data" then 
		      let nreq = default_browser_request b sw u in 
		      (match processNavigateFetch b nreq sw tw ty with | (res, w, nb) -> (res, Some nreq, w, nb))   
		   else (Success "not navigation resource", None, Some tw, b) (*process resource appropriately*)
  | None -> (match (processNavigateResponse b req (BResponse resp) true sw tw ty) with | (res, w, nb) -> (res, None, w, nb))
	
private val processNavigateFetchResp : b:browser -> r:browserRequest{notForbiddenHeaderfieldInReqHeader r.browser_request.reqhead /\ b.bid = r.browser_request.reqbrowser} -> 
				       resp:response{is_valid_response_for_request r resp /\ (not (NetworkError? resp) /\ not (RespSuccess? resp))} ->
				       sw:cowindow{sw.cwbid = b.bid} -> tw:cowindow{tw.cwbid = b.bid} -> navType -> 
				       Tot (result * option (nr:browserRequest{notForbiddenHeaderfieldInReqHeader (BrowserRequest?.browser_request nr).reqhead /\ 
						     nr.browser_request.reqbrowser = b.bid}) * option (w:cowindow{w.cwbid = b.bid}) * nb:browser{nb.bid = b.bid})
let processNavigateFetchResp b req resp sw tw ty =
  match resp with
  | BResponse r -> 
      if (isRedirectResponse r.b_response.respcode) then processNavigateFetchRespSub b req r sw tw ty 
      else (match (processNavigateResponse b req resp true sw tw ty) with | (res, w, nb) -> (res, None, w, nb))

val processResponse : b:browser -> connection -> 
		      r:browserRequest{notForbiddenHeaderfieldInReqHeader (BrowserRequest?.browser_request r).reqhead /\ b.bid = r.browser_request.reqbrowser} -> 
		      resp:browserResponse{is_valid_browser_response_for_request r resp /\ b.bid = resp.b_response.respbrowser} -> 
		      Tot (result * option (nr:browserRequest{notForbiddenHeaderfieldInReqHeader (BrowserRequest?.browser_request nr).reqhead /\ 
						     nr.browser_request.reqbrowser = b.bid}) * option (w:cowindow{w.cwbid = b.bid}) * nb:browser{nb.bid = b.bid})
let processResponse b c r resp =
  let (rr, nb, ei) = processNetworkResponse b c r resp in
  match ei with
  | None -> (match rr with
			| RespSuccess s -> (Error ("Success but nothing returned:" ^ s), None, None, nb)
			| NetworkError e -> (Error e, None, None, nb) (* Error - document's origin is set to an opaque origin *)
			| _ -> (Error "error in processing: case should not occur", None, None, nb))
  | Some (req, sw, tw, ty) -> (match rr with
			| RespSuccess s -> (Success s, None, Some tw, nb)
			| NetworkError e -> (Error e, None, None, nb) (* Error - document's origin is set to an opaque origin *)
			| oresp -> processNavigateFetchResp nb r oresp sw tw ty)

(* val create_frame_window : rid:wid -> cw:window -> sb:list sandbox_flags -> Tot iframe *)
(* let create_frame_window rid cw sb = *)
(*   let ouri = {origin=cw.doc.dloc.origin; uname=""; pwd=None; path=[]; querystring=[]; fragment=""} in *)
(*   let d = (Document ouri cw.doc.dloc cw.doc.dHTTPS cw.doc.drefPol [] rid (List.append cw.doc.dsbox sb) "") in  *)
(*   let he = (HEntry ouri get_time d) in  *)
(*   IFrame (Window rid "" ouri [] None (Some cw) (History [he] 1) d (List.append cw.doc.dsbox sb)) "" *)

(* val create_window : rid:wid -> cw: window -> Tot window *)
(* let create_window rid cw = *)
(*   let ouri = {origin=cw.doc.dloc.origin; uname=""; pwd=None; path=[]; querystring=[]; fragment=""} in *)
(*   let d = (Document ouri cw.doc.dloc cw.doc.dHTTPS cw.doc.drefPol [] rid [] "") in  *)
(*   let he = (HEntry ouri get_time d) in  *)
(*   (Window rid "" ouri [] (Some cw) None (History [he] 1) d [])  *)

private val empty_history : bid:origin_opaque -> Tot (history bid)
let empty_history bid = ({hlhe=[];hcur=0})

(* Section 7.1.5 HTML5.1 - browsing context names*)
(* Return the window given the window name in context of a current window(w) and return a modified browser if a new window has been created *)
val get_window_from_name : b:browser -> w:cowindow{w.cwbid = b.bid} -> n:string -> Tot (result * cw:cowindow{cw.cwbid = b.bid} * nb:browser{nb.bid = b.bid})
let get_window_from_name b w n =
  if n = "" then (Success "", w, b)
  else if n = "_self" then (Success "", w, b)
  else if n = "_parent" then (match (w.cwin.cwparent) with
		  | None -> (Success "", w, b)
		  | Some wp -> (Success "", CWindow w.cwbid wp, b)
		  )
  else if n = "_top" then (Success "", CWindow w.cwbid (get_top_window b w.cwin), b)
  else if n = "_blank" then 
	  if (getDocFlag (w.cwin.cwdoc) SB_NewWindow) then (Error "new window error", w, b) 
	  else 
	    (let sbo = (if (getDocFlag w.cwin.cwdoc SB_Propagate) then [] else getSBox w.cwin.cwdoc) in
	    let (nid, nb) = set_unique_id b in 
	    let (opori, sb) = set_op_origin nb in 
	    let blank_doc = {dloc=blank_uri;dref=blank_uri;dori=opori;dHTTPS="none";drefPol=RP_EmptyPolicy;dCSP=[];(* dwin=noWin; *)dsbox=[]} in
	    let newwin = ({cwinid=nid; cwname=""; cwloc=blank_uri; cwframes=[]; cwopener=(Some w.cwin); cwparent=None; cwhist=mk_ahist (empty_history b.bid); cwdoc=mk_adoc blank_doc; cwsbox=sbo}) in
	    let newb = Browser sb.bid ({sb.br with windows=newwin::sb.br.windows}) in
 	    (Success "", CWindow sb.bid newwin, newb))      
  else let win = get_window_name b w.cwin b.br.windows n in
      match win with
	| None -> (*Create a new window with that name and opener set to current window if the current doc's sbox flags permit*)
	  if (getDocFlag w.cwin.cwdoc SB_NewWindow) then (Error "new win error", w, b) 
	  else 
	    (let sbo = (if (getDocFlag w.cwin.cwdoc SB_Propagate) then [] else getSBox w.cwin.cwdoc) in
	    let (nid, nb) = set_unique_id b in 
	    let (opori, sb) = set_op_origin nb in 
	    let blank_doc = {dloc=blank_uri;dref=blank_uri;dori=opori;dHTTPS="none";drefPol=RP_EmptyPolicy;dCSP=[];(* dwin=noWin; *)dsbox=[]} in
	    let newwin = ({cwinid=nid; cwname=n; cwloc=blank_uri; cwframes=[]; cwopener=(Some w.cwin); cwparent=None; cwhist=mk_ahist (empty_history b.bid); cwdoc=mk_adoc blank_doc; cwsbox=sbo}) in
	    let newb = Browser sb.bid ({sb.br with windows=newwin::sb.br.windows}) in
	    (Success "", CWindow sb.bid newwin, newb))
	| Some x -> (Success "", CWindow b.bid x, b) (* Change opener to current window *)
	(* if (winName<>"_blank" && familiar_with w x) then Some x *)
	(* else (\*Create a new window with that name and opener set to current window*\)  *)
	(*   (let sbo = (match List.find (fun w -> w = SB_Propagate) w.wdoc.dsbox with | None -> [] | Some x -> w.wdoc.dsbox) in *)
	(*   Some ({winid=new_id; wname=winName; wloc=blank_uri; wframes=[]; wopener=(Some w); wparent=None; whist=({hlhe=[]; hcur=0}); wdoc=blank_doc; wsbox=sbo})) *)

(* window.open method - 
   window.parent should be the window itself for new/top level windows, and is represented using None and the current window for nested windows. 
   window.opener should be the current window for windows opened using scripts
   TODO - "replace" replaces the current window with new window and places current in history - session history is not yet included
*)
val open_window: b:browser -> cw:cowindow{cw.cwbid = b.bid} -> h:string -> name:string -> 
		 Tot (result * option (nr:browserRequest{notForbiddenHeaderfieldInReqHeader (BrowserRequest?.browser_request nr).reqhead /\ 
				      nr.browser_request.reqbrowser = b.bid}) * tw:cowindow{tw.cwbid = b.bid} * nb:browser{nb.bid = b.bid})
let open_window b cw h name =
  let wname = if name = "" then "_blank" else name in
  let twres = (get_window_from_name b cw wname) in 
  match twres with 
  | (Error err, _, _) -> (Error err, None, cw, b) (*sandbox check failed*)
  | (Success s, w, nb) -> (
      let us = hstring_to_uri nb h in
      match us with 
      | None -> (Success s, None, w, nb)
      | Some u -> 
	   (match (navigateWindow nb cw w (RequestResource (default_browser_request nb cw u)) "other") with
    	   | (Error err, nr, _, n) -> (Error err, nr, cw, n)
    	   | (Success s, nr, _, n) -> (Success s, nr, w, n)))

(* (\* removes window from list and returns the modified list *\) *)
(* val closewin : list cowindow -> cowindow -> Tot (list cowindow) *)
(* let rec closewin wl w = *)
(*     match wl with *)
(*     | [] -> [] *)
(*     | hd::tl -> if w.cwinid=hd.cwinid then tl *)
(* 	      else hd::(closewin tl w) *)
	      
(* Close a window from the script*)
(* *** Need a way to update the opener for all the windows "cw" opened *** *)
val close_window: b:browser -> w:window{w.wbid = b.bid} -> cw:cowindow{cw.cwbid = b.bid} -> Tot (nb:browser{nb.bid = b.bid})
let close_window b w cw = 
  if (cw.cwin.cwopener <> None) && (familiar_with (win_to_cowin w).cwin cw.cwin) && (allowed_navigation (win_to_cowin w).cwin cw.cwin) then
    Browser b.bid ({b.br with windows=(closewin b b.br.windows cw.cwin)})
  else b
  
(* The iframe should also allow sandbox property. 
   TODO - Similar to open_window use navigateWindow to get the resource here as well 
*)
(* val open_frame : b:browser -> cw:window -> h:c_uri -> name:string -> sb:sandbox -> Tot browser *)
(* let open_frame b cw h name sb = *)
(*   let l = get_uri h in *)
(*   let fsbox = get_sandbox_flags sb in *)
(*   let fw=create_frame_window rid cw fsbox in (\* navigate frame to "h" here *\) *)
(*   let wn=(Window cw.id cw.name cw.wloc (fw::cw.frames) cw.opener cw.wparent cw.whist cw.doc cw.wsbox) in *)
(*     (Browser (wn::(closewin b.windows cw)) b.cookieStore b.localStorage b.sts b.conn) *)

(* History functions *)
val forward_window : b:browser -> cw:cowindow{cw.cwbid = b.bid} -> tw:cowindow{tw.cwbid = b.bid} -> Tot (result * nb:browser{nb.bid = b.bid})
let forward_window b cw tw =
  if (isSameOriginWin cw.cwin tw.cwin) then (Success "", forward_history b cw.cwin tw.cwin)
  else ((Error "forward history error"), b)

val back_window : b:browser -> cw:cowindow{cw.cwbid = b.bid} -> tw:cowindow{tw.cwbid = b.bid} -> Tot (result * nb:browser{nb.bid = b.bid})
let back_window b cw tw =
  if (isSameOriginWin cw.cwin tw.cwin) then (Success "", back_history b cw.cwin tw.cwin)
  else ((Error "back history error"), b)

(* Set window location *)
val set_win_location : b:browser -> c:cowindow{c.cwbid = b.bid} -> f:cowindow{f.cwbid = b.bid} -> u:uri{is_origin_in_secrecy_level b.bid u.uri_secrecy_level} -> 
		       Tot (result * option (nr:browserRequest{notForbiddenHeaderfieldInReqHeader (BrowserRequest?.browser_request nr).reqhead /\ 
					    nr.browser_request.reqbrowser = b.bid}) * option (cw:cowindow{cw.cwbid = b.bid}) * nb:browser{nb.bid = b.bid})
let set_win_location b c f u = navigateWindow b c f (RequestResource (default_browser_request b f u)) "other"

(* 4.10.22.3 Form submission algorithm - form data is serialized string fd *)
(* can also have dialog method that does separate processing *)
(* For similar schemes, the spec proposes using the suitable descriptions *)
val form_submission : b:browser -> sw:window{sw.wbid = b.bid} -> target_name:string -> m:reqMethod{m="GET" \/ m="POST"} -> 
		      u:uri{is_origin_in_secrecy_level b.bid u.uri_secrecy_level} -> fd:list (public_string * public_string) -> 
		      Tot (result * option (nr:browserRequest{notForbiddenHeaderfieldInReqHeader (BrowserRequest?.browser_request nr).reqhead /\ 
					    nr.browser_request.reqbrowser = b.bid}) * option (cw:cowindow{cw.cwbid = b.bid}) * nb:browser{nb.bid = b.bid})
let form_submission b sw tn m u fd =
  if (List.find (fun w -> w = SB_Forms) sw.w.wdoc.dsbox <> None) then ((Error ""), None, None, b)
  else 
    match (get_window_from_name b (win_to_cowin sw) tn) with
    | (Error e, _, _) -> (Error e, None, None, b)
    | (Success s, tw, nb) ->
	let sch = Origin?.protocol (URI?.uri_value u).uri_origin in 
	(* let sl = (URI?.uri_secrecy_level u) in (\* Form submission requests should be indexed by the server alone *\) *)
	if (sch = "http" || sch = "https") then (
	  if (m = "GET") then 
	    let nuri = URI (URI?.uri_secrecy_level u) ({uri_origin=(URI?.uri_value u).uri_origin;
					uri_username=(URI?.uri_value u).uri_username;
					uri_password=(URI?.uri_value u).uri_password;
					uri_path=(URI?.uri_value u).uri_path;
					uri_querystring=(classify_uri_querystring #PublicVal fd (URI?.uri_secrecy_level u));
					uri_fragment=empty_secret_string (URI?.uri_secrecy_level u)}) in
	    (navigateWindow nb (win_to_cowin sw) tw (RequestResource (default_browser_request nb (win_to_cowin sw) (nuri))) "form-submission") 
	  else 
	    let nreq = (BrowserRequest (URI?.uri_secrecy_level u) ({reqbrowser = nb.bid; reqm = "POST"; requrl = [u]; reqhead = []; reqo = (mk_aorigin (URI?.uri_value sw.w.wloc).uri_origin); reqw = (Some (win_to_cowin sw)); reqinit = ""; reqtype = ""; reqdest = ""; reqtarget = Some tw; reqredirect = 0; reqredmode = "follow"; reqref = (Client (win_to_cowin sw)); reqreferrer_policy = RP_EmptyPolicy; reqnonce = ""; reqparser = ""; requnsafe = false; reqpreflight = false; reqsync = false; reqmode = NoCORS; reqtaint = "basic"; reqcredm = "omit"; reqcredflag = false; reqbody = (classify_secret_string #PublicVal (serialize_querystring fd) (URI?.uri_secrecy_level u)); corsflag = false; corspfflag = false; authflag = false; recflag = false})) in
	    (navigateWindow nb (win_to_cowin sw) tw (RequestResource nreq) "form-submission") 
	  )
	else if ((sch = "data") && (m = "GET")) then
	  let nuri = URI (URI?.uri_secrecy_level u) ({uri_origin=(URI?.uri_value u).uri_origin;uri_username=(URI?.uri_value u).uri_username;uri_password=(URI?.uri_value u).uri_password;uri_path=(URI?.uri_value u).uri_path;uri_querystring=(classify_uri_querystring #PublicVal fd (URI?.uri_secrecy_level u));uri_fragment=empty_secret_string (URI?.uri_secrecy_level u)}) in
	  (navigateWindow nb (win_to_cowin sw) tw (RequestResource (default_browser_request nb (win_to_cowin sw) (nuri))) "form-submission") 
	else (* For ftp, javascript no data is sent *)
	  (navigateWindow nb (win_to_cowin sw) tw (RequestResource (default_browser_request nb (win_to_cowin sw) (u))) "form-submission") 

(* xhr.spec.whatwg.org - open and send only *)
(* require the request and response to have similar secrecy_levels; so return the request that contains this information *)
val xmlHttpRequest : b:browser -> w:window{w.wbid = b.bid} -> u:uri{is_origin_in_secrecy_level b.bid u.uri_secrecy_level} -> reqMethod -> string -> 
		     h:header{checkHeaderSecLevel h /\ notForbiddenHeaderfieldInReqHeader (h) /\ (isHeaderVisible h (URI?.uri_secrecy_level u))} -> 
		     Tot (result * (nr:browserRequest{notForbiddenHeaderfieldInReqHeader (BrowserRequest?.browser_request nr).reqhead /\ 
					    nr.browser_request.reqbrowser = b.bid}) * option (cw:cowindow{cw.cwbid = b.bid}) * nb:browser{nb.bid = b.bid})
let xmlHttpRequest b w u m rb h =
	let body = (if (m="GET" || m="HEAD") then "" else rb) in
	let urisl = (URI?.uri_secrecy_level u) in
	let cw = (win_to_cowin w) in
	(* include more properties as per --- xhr.spec.whatwg.org Section 4.5 *)
	(* missing sync flag, upload listener flag, withCredentials, username, password *)
	let req = BrowserRequest urisl ({reqbrowser = b.bid; reqm = m; requrl = [(u)]; reqhead = h; reqo = (mk_aorigin w.w.wloc.uri_value.uri_origin); reqw = (Some cw); reqinit = ""; reqtype = ""; reqdest = ""; reqtarget = None; reqredirect = 0; reqredmode = "follow"; reqref = (Client cw); reqreferrer_policy = RP_EmptyPolicy; reqnonce = ""; reqparser = ""; requnsafe = true; reqpreflight = false; reqsync = false; reqmode = CORS; reqtaint = "basic"; reqcredm = "same-origin"; reqcredflag = false; reqbody = (classify_secret_string #PublicVal body urisl); corsflag = false; corspfflag = false; authflag = false; recflag = false}) in
	let (re, nreq, sb) = (fetch_resource b req false false (cw, cw, "other")) in
	(re, nreq, None, sb) (*the window is not required in this case*)
	
