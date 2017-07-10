(*
  html.spec.whatwg.org
  Describes various browser functions related to navigation (postmessage, xmlhttprequest, formsubmission, navigatewindow) and 
  getting/setting location, domain, localstorage etc.
*)
(* set --z3rlimit 50 *)
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

(* Return document.domain *)
val get_document_domain : browser -> window -> Tot hdomain
let get_document_domain b w =
  let d = w.wdoc in 
  (* if (noWindow (mk_adoc d)) then [] *)
  (* else *) 
  match getEffectiveDomain d with
       | None -> []
       | Some hd -> hd

(* Set document.domain : cannot set opaque origin using this function *)
val set_document_domain : browser -> window -> hdomain -> Tot (result * window * browser)
let set_document_domain b w h =
  let d = w.wdoc in 
  if ((* (noWindow (mk_adoc d)) ||  *)(List.find (fun w -> w = SB_Domain) d.dsbox <> None) || h = []) then (Error "document.domain sbox", w, b) (* Security Error *)
  else
    let ed = (match getEffectiveDomain d with | Some hd -> hd | None -> []) in
    if (h <> ed && (domainMatch ed h = false)) then (Error "document.domain domain does not match", w, b)
    else if (not (is_opaqueDoc (mk_adoc d))) then
	let o = d.dori in 
	let nw = setDocDomain w o h in
	(Success "domain set", nw, ({b with windows=(replacewin b.windows (win_to_cowin w) (win_to_cowin nw))}))
    else (Error "document.domain case should not arise", w, b) (* Case does not arise *)

(* 7.1.3 html.spec.whatwg.org - Security *)
private val hasBrowserScopeOrigin : cowindow -> Tot bool
let rec hasBrowserScopeOrigin w =
  match (CWindow?.cwparent w) with
  | None -> true
  | Some p -> (hasBrowserScopeOrigin p) && (isSameOriginWin p w)

(* window.location
   Although 5.2.1 in HTML5 Spec allows access to location and window, it is not allowed in implementation
   7.7.4 of HTML5.1 Spec for Location object specifies same origin check. Further property accesses are also subject to this check
*)
val get_win_location : #s:secLevel -> browser -> c:cowindow -> f:cowindow -> Tot (result * option (c_uri s))
let get_win_location #s b c f =
  if isSameOriginWin c f && (URI?.usl f.cwloc = s) then (Success "got location", (get_win_curi b c f))
  else (Error "win location error", None)

(* simple location lemma *)
val lem_location : #s:secLevel -> b:browser -> c:cowindow -> f:cowindow -> 
    Lemma (requires (match get_win_location #s b c f with | Success s, u -> true | Error e, u -> false))
	  (ensures (isSameOriginWin c f))
let lem_location #s b c f = ()

(* Get the parent window of the current window(c) *)
val get_parent : b:browser -> c:cowindow -> Tot cowindow
let get_parent b c = match (CWindow?.cwparent c) with
  | None -> c
  | Some wp -> wp

(* Get the localStorage for the current origin from the browser. 
   Return a modified browser if the localstorage is not present with a new empty store for that origin
*)
private val get_localStorage : b:browser -> o:torigin -> Tot (dictionary * browser)
let get_localStorage b o = (getLSEntry b.localStorage o, b)

(* Set the localStorage for the current origin using the dictionary provided 
   The dictionary is a list of key-value pairs with functions defined in BrowserDataTypes.fst
*)
private val set_localStorage : b:browser -> o:torigin -> dictionary -> Tot (localStorageMap)
let set_localStorage b o d = updateLSMap b.localStorage o d 

(* Get the value associated with the key in the localstorage of the current window *)
(* One can call tw.localStorage but the "tw" is normally ignored and the getting/setting happens in the current window's localstorage *)
val get_item_localStorage : browser -> window -> option cowindow -> string -> Tot (result * string)
let get_item_localStorage b cw tw key =
  if (OOrigin? (URI?.u cw.wloc).c_origin) then (Error "localstorage origin error", "")
  else if (List.find (fun w -> w = SB_Origin) cw.wdoc.dsbox <> None) then (Error "localstorage sbox", "")
  else 
  let (d,nb) = (get_localStorage b (URI?.u cw.wloc).c_origin) in 
    (Success "got local storage item", (get_val_dict d key))
  
(* Sets the localstorage of the current window with the key value pair specified in the item *)
val set_item_localStorage : browser -> window -> option cowindow -> string -> string -> Tot (result * browser)
let set_item_localStorage b cw tw key value =
  if (OOrigin? (URI?.u cw.wloc).c_origin) then (Error "setlocalstorage origin error", b)
  else if (List.find (fun w -> w = SB_Origin) cw.wdoc.dsbox <> None) then (Error "setlocalstorage sbox", b)
  else 
  let (d,nb) = (get_localStorage b (URI?.u cw.wloc).c_origin) in 
  let nd = (set_val_dict d key value) in 
  let nls = (set_localStorage nb (URI?.u cw.wloc).c_origin nd) in
    (Success "set local storage item", ({nb with localStorage=nls}))

(* Post message from one window to another. The target origin (to) is the one that can receive this message. 
   Omitting transfer option for now. It deletes the current copy of the object in the current window when sending the message (literally transfer)
*)
val post_message : browser -> cowindow -> cowindow -> string -> hstring -> Tot (result)
let post_message b cw tw msg t_ori =
  let tori = ( match t_ori with
      | "*" -> None (* This allows msg to be passed to any origin. *)
      | "/" -> Some (getWinURI cw)
      | l -> hstring_to_uri l
    ) in
    match tori with
    | None -> Success "sent msg"
    | Some o -> if (isSameOriginURI o (getWinURI tw)) then Success "sent msg" else Error "msg not sent"
		  
(* url.spec.whatwg.org -- 4.4 URL equivalence *)

(* val add_flag_sandbox : list sandboxFlags -> sandboxFlags -> Tot (list sandboxFlags) *)
(* let add_flag_sandbox l s = s::l *)
(* *)
(* val get_sandbox_flags : sandbox -> Tot (list sandboxFlags) *)
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
private val get_partial_sb_flags : sandbox -> Tot (list sandboxFlags)
let get_partial_sb_flags sb =
  let cb = (SB_Navigation::SB_NewWindow::SB_TopWindow::SB_Origin::SB_Forms::SB_PointerLock::SB_Plugins::SB_StorageURL::[SB_Domain]) in
  let pb = (if sb.sb_popups then (remove_elem_list cb SB_NewWindow) else cb) in 
  let tb = (if sb.sb_topnavigation then (remove_elem_list pb SB_TopWindow) else pb) in
  let ub = (if sb.sb_sameorigin then (remove_elem_list tb SB_Origin) else tb) in
  let fb = (if sb.sb_forms then (remove_elem_list ub SB_Forms) else ub) in
  (if sb.sb_pointerlock then (remove_elem_list fb SB_PointerLock) else fb) 

(* Return the sandbox flags based on the sandbox attributes *)
private val get_sandbox_flags : sandbox -> Tot (list sandboxFlags)
let get_sandbox_flags sb =
  let partial = (SB_Script::SB_Automatic::SB_Propagate::SB_Modals::SB_Orientation::SB_Presentation::(get_partial_sb_flags sb)) in 
  let jb = (if sb.sb_scripts then (remove_elem_list (remove_elem_list partial SB_Script) SB_Automatic) else partial) in
  let eb = (if sb.sb_popupsEscape then (remove_elem_list jb SB_Propagate) else jb) in
  let mb = (if sb.sb_modals then (remove_elem_list eb SB_Modals) else eb) in
  let ob = (if sb.sb_orientation then (remove_elem_list mb SB_Orientation) else mb) in
  (if sb.sb_presentation then (remove_elem_list ob SB_Presentation) else ob)

(* 7.6 Sandboxing - html.spec.whatwg.org *)
private val dirvalue_to_sandbox : list dirValue -> sandbox -> Tot sandbox
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

private val get_sandbox_from_CSP : csp_policy -> Tot (list sandboxFlags)
let rec get_sandbox_from_CSP p =
  match p with
  | [] -> [] 
  | ph::pt -> ( match ph.dir_name with
	      | CSP_sandbox -> get_sandbox_flags (dirvalue_to_sandbox ph.dir_value ({sb_forms=false;sb_modals=false;sb_orientation=false;sb_pointerlock=false;sb_popups=false;sb_popupsEscape=false;sb_presentation=false;sb_sameorigin=false;sb_scripts=false;sb_topnavigation=false}))
	      | _ -> get_sandbox_from_CSP pt)

private val join_flags : list sandboxFlags -> list sandboxFlags -> Tot (list sandboxFlags)
let join_flags ls1 ls2 = List.append ls1 ls2

(* check if we need to parse the remaining list *)
(* private val string_to_refPolicy : list string -> Tot refPolicy *)
(* let string_to_refPolicy ls = *)
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
private val processNavigateResponseSub : browser -> req:(request) -> resp:actResponse{requestResponseValid req resp} -> ir:bool -> cowindow -> cowindow -> navType -> 
					 Tot (result * option cowindow * browser)
let processNavigateResponseSub b req oresp ir sw tw ty =
  if (navRespBlockedCSP req ty (oresp) sw tw) then ((Error "navigation response blocked by CSP"), None, b)
  else if (ActResponse?.ar oresp).respcode = 204 || (ActResponse?.ar oresp).respcode = 205 then (Success "done navigate response", Some tw, b)
  else
      let referrer = (if ir then (match (Request?.rf req).reqref with | NoReferrer -> blank_uri | Client w -> (getWinURI w) | URLReferrer u -> u) else blank_uri) in
      let flags = (match (CWindow?.cwparent tw) with
		  | None -> join_flags (get_sandbox_from_CSP (ActResponse?.ar oresp).respCSP) (CWindow?.cwsbox tw)
		  | Some p -> join_flags (join_flags (get_sandbox_from_CSP (ActResponse?.ar oresp).respCSP) (CWindow?.cwsbox tw)) (getSBox (CWindow?.cwdoc p))) in
      let rurl = (firstElement (Request?.rf req).requrl) in (* Original fetch url is the document's url *)
      let rP = (parseRefPol oresp) in
      let newdoc = mk_adoc ({dloc=rurl; dori=getAOrigin rurl; dref=referrer; dHTTPS=(ActResponse?.ar oresp).respHTTPS; drefPol=rP; dCSP=(ActResponse?.ar oresp).respCSP; dsbox=(flags)}) in
      let nw = add_doc_hist (save_cur_doc_win tw) newdoc in
      (Success "Response processed", Some nw, ({b with windows=(replacewin b.windows tw nw)})) (* Add to STS state here?*)
		   
private val processNavigateResponse : browser -> req:request -> resp:response{validReqResp req resp} -> bool -> cowindow -> cowindow -> navType -> 
				      Tot (result * option cowindow * browser)
let processNavigateResponse b req resp ir sw tw ty =
  match resp with
  | NetworkError e -> (Error e, None, b) (* Error - document's origin is set to an opaque origin *)
  | RespSuccess s -> (Success s, Some tw, b)
  | r -> let oresp = (match r with
		 | TotResponse tr -> tr
		 | FilteredResponse fr -> match fr with
					 | BasicFiltered bf -> bf.ir
					 | CORSFiltered cf -> cf.ir
					 | OpaqFiltered opf -> opf.ir
					 | OpaqRedFiltered orf -> orf.ir ) in
	processNavigateResponseSub b req oresp ir sw tw ty

(* 7.8.1 -- Process a navigate fetch *)
private val processNavigateFetch : browser -> req:request{notForbiddenHeaderfieldInReqHeader (Request?.rf req).reqhead} -> cowindow -> cowindow -> navType -> 
				   Tot (result * option (nr:request{notForbiddenHeaderfieldInReqHeader (Request?.rf nr).reqhead}) * option cowindow * browser)
let processNavigateFetch b req sw tw ty =
  let r = (Request?.rf req) in 
  let ruri = (firstElement r.requrl) in 
  if ((equalURL ruri (getWinURI tw) true) && (not (emptyFragment ruri))) then   (* Clear all history entries *)
    (Success "fragment", None, Some tw, b) (* Happens if its not reload -- Navigate to the fragment *)
  else
    let ori = ((* if ((r.reqm <> "GET" || ty = "form-submission") && (not (is_opaqueWin sw))) then (false, r.reqo) *)
	    if ((CWindow?.cwparent tw) <> None && hasBrowserScopeOrigin (Some?.v (CWindow?.cwparent tw))) then 
	       (getAOrigin (getWinURI (Some?.v (CWindow?.cwparent tw))))
	    else r.reqo) in
    let nreq = Request (Request?.rsl req) ({r with reqo = ori; reqw = (Some sw); reqdest = "document"; reqtarget = (Some tw); reqredmode = "manual"; reqmode = Navigate; reqcredm = "include"; reqcredflag = true; corsflag = false; corspfflag = false; authflag = false; recflag = false}) in
    if (navReqBlockedCSP nreq ty sw tw) then (Error "navigation req blocked by CSP", None, None, b)
    else 
      let nw = (CWindow tw.cwinid tw.cwname ruri tw.cwframes tw.cwopener tw.cwparent tw.cwhist tw.cwdoc tw.cwsbox) in
      let nb = ({b with windows=(replacewin b.windows tw nw)}) in
      let (re, nr, sb) = (fetch_resource nb nreq false false (sw, nw, ty)) in
      (re, Some nr, Some nw, sb) (* Send the newwin *)

(* 7.8.1 -- Navigate a browsing context *)
(* TODO - update the windows details to the request url *)
val navigateWindow: browser -> cowindow -> cowindow -> resource -> navType -> 
		    Tot (result * option (nr:request{notForbiddenHeaderfieldInReqHeader (Request?.rf nr).reqhead}) * option cowindow * browser)
let navigateWindow b sw tw r nType =
  if (allowed_navigation sw tw = false) then ((Error "navigation not allowed"), None, None, b)
  else 
    match r with
    | RequestResource req -> processNavigateFetch b req sw tw nType 
    | ResponseResource req resp -> (match (processNavigateResponse b req resp false sw tw nType) with | (res, w, nb) -> (res, None, w, nb))
      
(* 7.8.1 -- Process a navigate fetch's response *)
private val processNavigateFetchRespSub : browser -> req:request{notForbiddenHeaderfieldInReqHeader (Request?.rf req).reqhead} -> 
					  resp:actResponse{requestResponseValid req resp /\ isRedirectResponse (ActResponse?.ar resp)} -> cowindow -> cowindow -> navType -> 
					  Tot (result * option (nr:request{notForbiddenHeaderfieldInReqHeader (Request?.rf nr).reqhead}) * option cowindow * browser)
let processNavigateFetchRespSub b req resp sw tw ty =
  match (ActResponse?.ar resp).resploc with
  | Some (Failure) -> let (re, nr, sb) = httpRedirectFetch b req resp false (sw, tw, ty) in (* processNavigateFetchResp after getting back new response *)
		     (re, Some nr, Some tw, sb)
  | Some (URL u) -> let prot = getScheme u in 
		   if prot = "http" || prot = "https" then 
		      let (re, nr, sb) = httpRedirectFetch b req resp false (sw, tw, ty) in
		      (re, Some nr, Some tw, sb)
		   else if prot = "blob" || prot = "file" || prot = "filesystem" || prot = "javascript" then 
		      (Error "incorrect protocol", None, None, b) (* Network Error *)
		   else if prot = "ftp" || prot = "about" || prot = "data" then 
		      let nreq = default_req_uri sw u in 
		      processNavigateFetch b nreq sw tw ty
		   else (Success "not navigation resource", None, Some tw, b) (*process resource appropriately*)
  | None -> (match (processNavigateResponse b req (TotResponse resp) true sw tw ty) with | (res, w, nb) -> (res, None, w, nb))
	
private val processNavigateFetchResp : browser -> req:request{notForbiddenHeaderfieldInReqHeader (Request?.rf req).reqhead} -> 
				       r:response{validReqResp req r /\ (not (NetworkError? r) /\ not (RespSuccess? r))} ->cowindow -> cowindow -> navType -> 
				       Tot (result * option (nr:request{notForbiddenHeaderfieldInReqHeader (Request?.rf nr).reqhead}) * option cowindow * browser)
let processNavigateFetchResp b req resp sw tw ty =
  match resp with
  | TotResponse tr -> 
      if (isRedirectResponse (ActResponse?.ar tr)) then processNavigateFetchRespSub b req tr sw tw ty 
      else (match (processNavigateResponse b req resp true sw tw ty) with | (res, w, nb) -> (res, None, w, nb))
  | FilteredResponse (BasicFiltered f) -> 
      if (isRedirectResponse (ActResponse?.ar f.ir)) then processNavigateFetchRespSub b req f.ir sw tw ty 
      else (match (processNavigateResponse b req resp true sw tw ty) with | (res, w, nb) -> (res, None, w, nb))
  | FilteredResponse (CORSFiltered f) -> 
      if (isRedirectResponse (ActResponse?.ar f.ir)) then processNavigateFetchRespSub b req f.ir sw tw ty 
      else (match (processNavigateResponse b req resp true sw tw ty) with | (res, w, nb) -> (res, None, w, nb))
  | FilteredResponse (OpaqFiltered f) -> 
      if (isRedirectResponse (ActResponse?.ar f.ir)) then processNavigateFetchRespSub b req f.ir sw tw ty 
      else (match (processNavigateResponse b req resp true sw tw ty) with | (res, w, nb) -> (res, None, w, nb))
  | FilteredResponse (OpaqRedFiltered f) -> 
      if (isRedirectResponse (ActResponse?.ar f.ir)) then processNavigateFetchRespSub b req f.ir sw tw ty 
      else (match (processNavigateResponse b req resp true sw tw ty) with | (res, w, nb) -> (res, None, w, nb))

(* private val processNavigateFetchResp : browser -> req:request -> r:actResponse{requestResponseValid req r} ->  *)
(* 				       cowindow -> cowindow -> navType -> Tot (result * option cowindow * browser) *)
(* let processNavigateFetchResp b req resp sw tw ty = *)
(*   if (isRedirectResponse (ActResponse?.ar resp)) then  *)
(*     processNavigateFetchRespSub b req resp sw tw ty *)
(*   else (processNavigateResponse b req (TotResponse resp) true sw tw ty)  *)

val processResponse : browser -> connection -> r:request{notForbiddenHeaderfieldInReqHeader (Request?.rf r).reqhead} -> resp:actResponse{requestResponseValid r resp} -> 
		      Tot (result * option (nr:request{notForbiddenHeaderfieldInReqHeader (Request?.rf nr).reqhead}) * option cowindow * browser)
let processResponse b c r resp =
  let (rr, nb, ei) = processNetworkResponse b c r resp in
  match ei with
  | None -> (match rr with
			| RespSuccess s -> (Error ("Success but nothing returned:" ^ s), None, None, nb)
			| NetworkError e -> (Error e, None, None, nb) (* Error - document's origin is set to an opaque origin *)
			| _ -> (Error "error in processing: case should not occur", None, None, nb))
  | Some (req, sw, tw, ty) -> match rr with
			| RespSuccess s -> (Success s, None, Some tw, nb)
			| NetworkError e -> (Error e, None, None, nb) (* Error - document's origin is set to an opaque origin *)
			| oresp -> (* if (r = req) then *) (* The request is not the same as req is changed quite a bit before being queued up *)
				     processNavigateFetchResp nb r oresp sw tw ty 
				  (* else (Error "Incorrect request accessed", None, None, nb) *)

(* val create_frame_window : rid:wid -> cw:window -> sb:list sandboxFlags -> Tot iframe *)
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

(* Section 7.1.5 HTML5.1 - browsing context names*)
(* Return the window given the window name in context of a current window(w) and return a modified browser if a new window has been created *)
val get_window_from_name : b:browser -> w:cowindow -> n:string -> Tot (result * cowindow * browser)
let get_window_from_name b w n =
  if n = "" then (Success "", w, b)
  else if n = "_self" then (Success "", w, b)
  else if n = "_parent" then (match (CWindow?.cwparent w) with
		  | None -> (Success "", w, b)
		  | Some wp -> (Success "", wp, b)
		  )
  else if n = "_top" then (Success "", (get_top_window w), b)
  else if n = "_blank" then 
	  if (getDocFlag (CWindow?.cwdoc w) SB_NewWindow) then (Error "new window error", w, b) 
	  else 
	    (let sbo = (if (getDocFlag (CWindow?.cwdoc w) SB_Propagate) then [] else getSBox (CWindow?.cwdoc w)) in
	    let (nid, nb) = set_unique_id b in 
	    let (opori, sb) = set_op_origin nb in 
	    let blank_doc = {dloc=blank_uri;dref=blank_uri;dori=opori;dHTTPS="none";drefPol=RP_EmptyPolicy;dCSP=[];(* dwin=noWin; *)dsbox=[]} in
	    let newwin = win_to_cowin ({winid=nid; wname=""; wloc=blank_uri; wframes=[]; wopener=(Some w); wparent=None; whist=({hlhe=[]; hcur=0}); wdoc=blank_doc; wsbox=sbo}) in
	    let newb = ({(sb) with windows=newwin::(sb).windows}) in
 	    (Success "", newwin, newb))      
  else let win = get_window_name w b.windows n in
      match win with
	| None -> (*Create a new window with that name and opener set to current window if the current doc's sbox flags permit*)
	  if (getDocFlag (CWindow?.cwdoc w) SB_NewWindow) then (Error "new win error", w, b) 
	  else 
	    (let sbo = (if (getDocFlag (CWindow?.cwdoc w) SB_Propagate) then [] else getSBox (CWindow?.cwdoc w)) in
	    let (nid, nb) = set_unique_id b in 
	    let (opori, sb) = set_op_origin nb in 
	    let blank_doc = {dloc=blank_uri;dref=blank_uri;dori=opori;dHTTPS="none";drefPol=RP_EmptyPolicy;dCSP=[];(* dwin=noWin; *)dsbox=[]} in
	    let newwin = win_to_cowin ({winid=nid; wname=n; wloc=blank_uri; wframes=[]; wopener=(Some w); wparent=None; whist=({hlhe=[]; hcur=0}); wdoc=blank_doc; wsbox=sbo}) in
	    let newb = ({(sb) with windows=newwin::(sb).windows}) in
	    (Success "", newwin, newb))
	| Some x -> (Success "", x, b) (* Change opener to current window *)
	(* if (winName<>"_blank" && familiar_with w x) then Some x *)
	(* else (\*Create a new window with that name and opener set to current window*\)  *)
	(*   (let sbo = (match List.find (fun w -> w = SB_Propagate) w.wdoc.dsbox with | None -> [] | Some x -> w.wdoc.dsbox) in *)
	(*   Some ({winid=new_id; wname=winName; wloc=blank_uri; wframes=[]; wopener=(Some w); wparent=None; whist=({hlhe=[]; hcur=0}); wdoc=blank_doc; wsbox=sbo})) *)

(* window.open method - 
   window.parent should be the window itself for new/top level windows, and is represented using None and the current window for nested windows. 
   window.opener should be the current window for windows opened using scripts
   TODO - "replace" replaces the current window with new window and places current in history - session history is not yet included
*)
val open_window: b:browser -> cw:cowindow -> h:string -> name:string -> 
		 Tot (result * option (nr:request{notForbiddenHeaderfieldInReqHeader (Request?.rf nr).reqhead}) * cowindow * browser)
let open_window b cw h name =
  let wname = if name = "" then "_blank" else name in
  let twres = (get_window_from_name b cw wname) in 
  match twres with 
  | (Error err, _, _) -> (Error err, None, cw, b) (*sandbox check failed*)
  | (Success s, w, nb) -> (
      let us = hstring_to_uri h in
      match us with 
      | None -> (Success s, None, w, nb)
      | Some u -> 
	   (match (navigateWindow nb cw w (RequestResource (default_req_uri cw u)) "other") with
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
(* *** Need a way to update the opener for all the windows "w" opened *** *)
val close_window: b:browser -> cw:window -> w:cowindow -> Tot browser
let close_window b cw w = 
  if ((CWindow?.cwopener w) <> None) && (familiar_with (win_to_cowin cw) w) && (allowed_navigation (win_to_cowin cw) w) then
    ({b with windows=(closewin b.windows w)})
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
val forward_window : b:browser -> cw:cowindow -> tw:cowindow{equalSubLevels (URI?.usl (CWindow?.cwloc cw)) (URI?.usl (CWindow?.cwloc tw))} -> Tot (result * browser)
let forward_window b cw tw =
  if (isSameOriginWin cw tw) then (Success "", forward_history b cw tw)
  else ((Error "forward history error"), b)

val back_window : b:browser -> cw:cowindow -> tw:cowindow{equalSubLevels (URI?.usl (CWindow?.cwloc cw)) (URI?.usl (CWindow?.cwloc tw))} -> Tot (result * browser)
let back_window b cw tw =
  if (isSameOriginWin cw tw) then (Success "", back_history b cw tw)
  else ((Error "back history error"), b)

(* Set window location *)
val set_win_location : browser -> c:cowindow -> f:cowindow -> u:uri{match (URI?.usl u) with | SecretVal [o] -> true | _ -> false} -> 
		       Tot (result * option (nr:request{notForbiddenHeaderfieldInReqHeader (Request?.rf nr).reqhead}) * option cowindow * browser)
let set_win_location b c f u = navigateWindow b c f (RequestResource (default_req_uri f u)) "other"

(* 4.10.22.3 Form submission algorithm - form data is serialized string fd *)
(* can also have dialog method that does separate processing *)
(* For similar schemes, the spec proposes using the suitable descriptions *)
val form_submission : #l:secLevel{match l with | SecretVal [o] -> true | _ -> false} -> browser -> window -> string -> m:reqMethod{m="GET" \/ m="POST"} -> 
		      u:uri{(URI?.usl u) = l /\ (match (URI?.usl u) with | SecretVal [o] -> true | _ -> false)} -> fd:list (secString l * secString l) -> 
		      Tot (result * option (nr:request{notForbiddenHeaderfieldInReqHeader (Request?.rf nr).reqhead}) * option cowindow * browser)
let form_submission #l b sw tn m u fd =
  if (List.find (fun w -> w = SB_Forms) sw.wdoc.dsbox <> None) then ((Error ""), None, None, b)
  else 
    match (get_window_from_name b (win_to_cowin sw) tn) with
    | (Error e, _, _) -> (Error e, None, None, b)
    | (Success s, tw, nb) ->
	let sch = TOrigin?.protocol (URI?.u u).c_origin in 
	(* let sl = (URI?.usl u) in (\* Form submission requests should be indexed by the server alone *\) *)
	if (sch = "http" || sch = "https") then (
	  if (m = "GET") then 
	    let nuri = URI l ({c_origin=(URI?.u u).c_origin;c_uname=(URI?.u u).c_uname;c_pwd=(URI?.u u).c_pwd;c_path=(URI?.u u).c_path;c_querystring=fd;c_fragment=emptyString l}) in
	    (navigateWindow nb (win_to_cowin sw) tw (RequestResource (default_req_uri (win_to_cowin sw) (nuri))) "form-submission") 
	  else 
	    let nreq = (match (URI?.usl u) with
		       | SecretVal [o] -> Request (URI?.usl u) ({reqm = "POST"; requrl = [u]; reqhead = []; reqo = (mk_aorigin (URI?.u sw.wloc).c_origin); reqw = (Some (win_to_cowin sw)); reqinit = ""; reqtype = ""; reqdest = ""; reqtarget = Some tw; reqredirect = 0; reqredmode = "follow"; reqref = (Client (win_to_cowin sw)); reqrefPolicy = RP_EmptyPolicy; reqnonce = ""; reqparser = ""; requnsafe = false; reqpreflight = false; reqsync = false; reqmode = NoCORS; reqtaint = "basic"; reqcredm = "omit"; reqcredflag = false; reqbody = (serializeQueryString fd); corsflag = false; corspfflag = false; authflag = false; recflag = false}))
		       in
	    (navigateWindow nb (win_to_cowin sw) tw (RequestResource nreq) "form-submission") 
	  )
	else if ((sch = "data") && (m = "GET")) then
	  let nuri = URI l ({c_origin=(URI?.u u).c_origin;c_uname=(URI?.u u).c_uname;c_pwd=(URI?.u u).c_pwd;c_path=(URI?.u u).c_path;c_querystring=fd;c_fragment=emptyString l}) in
	  (navigateWindow nb (win_to_cowin sw) tw (RequestResource (default_req_uri (win_to_cowin sw) (nuri))) "form-submission") 
	else (* For ftp, javascript no data is sent *)
	  (navigateWindow nb (win_to_cowin sw) tw (RequestResource (default_req_uri (win_to_cowin sw) (u))) "form-submission") 

(* xhr.spec.whatwg.org - open and send only *)
(* require the request and response to have similar secLevels; so return the request that contains this information *)
val xmlHttpRequest : browser -> window -> u:uri -> reqMethod -> string -> 
		     h:header{checkHeaderSecLevel h /\ notForbiddenHeaderfieldInReqHeader (h) /\ 
						     (match (URI?.usl u) with | SecretVal [o] -> isHeaderVisible h [o] | _ -> false)} -> 
		     Tot (result * (nr:request{notForbiddenHeaderfieldInReqHeader (Request?.rf nr).reqhead}) * option window * browser)
let xmlHttpRequest b w u m rb h =
	let body = (if (m="GET" || m="HEAD") then "" else rb) in
	let urisl = (URI?.usl u) in
	let cw = (win_to_cowin w) in
	(* include more properties as per --- xhr.spec.whatwg.org Section 4.5 *)
	(* missing sync flag, upload listener flag, withCredentials, username, password *)
	let req = (match (URI?.usl u) with
		  | SecretVal [o] -> Request urisl ({reqm = m; requrl = [(u)]; reqhead = h; reqo = (mk_aorigin (URI?.u w.wloc).c_origin); reqw = (Some cw); reqinit = ""; reqtype = ""; reqdest = ""; reqtarget = None; reqredirect = 0; reqredmode = "follow"; reqref = (Client cw); reqrefPolicy = RP_EmptyPolicy; reqnonce = ""; reqparser = ""; requnsafe = true; reqpreflight = false; reqsync = false; reqmode = CORS; reqtaint = "basic"; reqcredm = "same-origin"; reqcredflag = false; reqbody = (classify #PublicVal body urisl); corsflag = false; corspfflag = false; authflag = false; recflag = false})) in
	let (re, nreq, sb) = (fetch_resource b req false false (cw, cw, "other")) in
	(re, nreq, None, sb) (*the window is not required in this case*)
	
