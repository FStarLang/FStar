(*
  fetch.spec.whatwg.org
  Describes the functionality of fetching a resource on the network and handling the response
*)
(* set --z3rlimit 50 *)
module Browser.HTTPFetch

open AuxiliaryFunctions
open Web.URI
open Browser.AuxiliaryDatatypes
open Secret.SecString
open Browser.Datatypes
open Browser.ContentSecurityPolicy
open Browser.RequestResponseHeader
open Browser.HTTPFetch.Auxiliary

module List = FStar.List.Tot

(* Section 4.6 - HTTP Network fetch *) 
(* can return network error at some points *)
val httpNetworkFetch : browser -> request -> bool -> (cowindow * cowindow * navType) -> Tot (result * browser)
let httpNetworkFetch b r cflag einfo = sendRequest b r cflag einfo

private val getFetchHeader : browser -> req:request -> bool -> Tot (bool * h:header{checkHeaderSecLevel h})
let getFetchHeader b req cors =
    let r = Request?.rf req in 
    let cf = (r.reqcredm = "include" || (r.reqcredm = "same-origin" && r.reqtaint = "basic")) in
	(* HTTP/1.1 Spec (RFC 7231) 5.5.2 - 
	   A user agent MUST NOT send a referrer header field in an unsecured HTTP request if the referring page was received with a secure protocol *)
    let nh1 = if (URLReferrer? r.reqref) then (appendName r.reqhead "Referer" (match r.reqref with | URLReferrer u -> getHeaderValueURI req u))
	      else r.reqhead in 
    let nh2 = if (cors || (r.reqm <> "GET" && r.reqm <> "HEAD")) then appendName nh1 "Origin" (getHeaderValueOrigin req) else nh1 in
    if (cf) then (
       let th = (let cookie = (get_cookie_list b req false) in if (emptyHeaderVal cookie) then (nh2) else (appendName nh2 "Cookie" cookie)) in
       if (hasAuthzHeader th) then (cf,th)
       else (*check authentication entry -- RFC 7235? contains the header information but nothing about where the entry is*) 
	   (cf,th)) (*use authentication-fetch flag here*)
    else (cf,nh2)

(* Section 4.5 - HTTP Network or Cache fetch - omitting the cache part *) 
(* For cache access, process response in the same function *)
val httpNetworkOrCacheFetch : browser -> req:request{notForbiddenHeaderfieldInReqHeader (Request?.rf req).reqhead} -> bool -> bool -> (cowindow * cowindow * navType) -> 
			      Tot (result * nr:request{notForbiddenHeaderfieldInReqHeader (Request?.rf nr).reqhead} * browser)
let httpNetworkOrCacheFetch b req cors af einfo =
    let r = Request?.rf req in 
    let (cflag, nh) = getFetchHeader b req cors in 
    let nr = Request (Request?.rsl req) ({r with reqhead=nh;corsflag=cors;corspfflag=false;authflag=af}) in
    let (re, nb) = (httpNetworkFetch b nr cflag einfo) in
    (re, req, nb)

(* A version of httpNetworkOrCacheFetch to handle preflight fetches as they already contain headers with forbidden name - 
   these are never redirected as it ultimately uses httpNetworkOrCacheFetch 
*)
val httpNetworkOrCachePreflightFetch : browser -> request -> bool -> bool -> (cowindow * cowindow * navType) -> Tot (result * browser)
let httpNetworkOrCachePreflightFetch b req cors af einfo =
    let r = Request?.rf req in 
    let (cflag, nh) = getFetchHeader b req cors in 
    let nr = Request (Request?.rsl req) ({r with reqhead=nh;corsflag=cors;corspfflag=false;authflag=af}) in
    (httpNetworkFetch b nr cflag einfo) 

val preflight_request : request -> h:header{checkHeaderSecLevel h /\ List.for_all (fun (hf,hv) -> Headervalue?.hvs hv = PublicVal) h} -> Tot request
let preflight_request req h =
  let r = (Request?.rf req) in
  let rs = (Request?.rsl req) in
  Request rs ({reqm="OPTIONS";requrl=r.requrl;reqhead=h;reqo=r.reqo;reqw=None;reqinit=r.reqinit;reqtype=r.reqtype;reqdest=r.reqdest;reqtarget=None;reqredirect=0;reqredmode="follow";reqref=r.reqref;reqrefPolicy=r.reqrefPolicy;reqnonce="";reqparser="";requnsafe=false;reqpreflight=false;reqsync=false;reqmode=NoCORS;reqtaint="basic";reqcredm="omit";reqcredflag=false;reqbody=(emptyString rs);corsflag=r.corsflag;corspfflag=true;authflag=r.authflag;recflag=r.recflag})

(* Section 4.7 - CORS-Preflight Fetch *)
val corsPreflightFetch : browser -> req:request -> (cowindow * cowindow * navType) -> Tot (result * browser)
let corsPreflightFetch b req einfo =
  let r = (Request?.rf req) in
  let u = (firstElement r.requrl) in
  let nh = [("Access-Control-Request-Method", (Headervalue PublicVal r.reqm));("Access-Control-Request-Headers",(Headervalue PublicVal (getHeaderNames r.reqhead)))] in
  let pr = (let r = (Request?.rf req) in
	   let rs = (Request?.rsl req) in
	   Request rs ({reqm="OPTIONS";requrl=r.requrl;reqhead=nh;reqo=r.reqo;reqw=None;reqinit=r.reqinit;reqtype=r.reqtype;reqdest=r.reqdest;reqtarget=None;reqredirect=0;reqredmode="follow";reqref=r.reqref;reqrefPolicy=r.reqrefPolicy;reqnonce="";reqparser="";requnsafe=false;reqpreflight=false;reqsync=false;reqmode=NoCORS;reqtaint="basic";reqcredm="omit";reqcredflag=false;reqbody=(emptyString rs);corsflag=r.corsflag;corspfflag=true;authflag=r.authflag;recflag=r.recflag})) in
  httpNetworkOrCachePreflightFetch b pr false false einfo

(* Section 4.3 - HTTP Fetch *)
val httpFetch : browser -> r:request{notForbiddenHeaderfieldInReqHeader (Request?.rf r).reqhead} -> bool -> bool -> (cowindow * cowindow * navType) -> 
		Tot (result * nr:request{notForbiddenHeaderfieldInReqHeader (Request?.rf nr).reqhead} * browser)
let httpFetch b r cors pf einfo = (* check for skip-service-worker. define service workers. for now assuming that the page doesnt use service workers *)
  if (pf) then
      let nreq = Request (Request?.rsl r) ({(Request?.rf r) with corsflag=cors;corspfflag=true}) in
      let (re, nb) = corsPreflightFetch b nreq einfo in
      (re, r, nb)  (*Send the original request here - not the one created as part preflightFetch *)
  else
      httpNetworkOrCacheFetch b r cors false einfo

(* Section 4.2 - Scheme Fetch *)
(* case analyse the protocol to determine what to do. Considering only http(s) cases, calls into httpFetch *)
val schemeFetch : browser -> r:request{notForbiddenHeaderfieldInReqHeader (Request?.rf r).reqhead} -> (cowindow * cowindow * navType) -> 
		  Tot (result * nr:request{notForbiddenHeaderfieldInReqHeader (Request?.rf nr).reqhead} * browser)
let schemeFetch b r einfo =
  let rurl = (firstElement (Request?.rf r).requrl) in
  if getScheme (rurl) = "http" || getScheme (rurl) = "https" then
     httpFetch b r false false einfo
  else (Error "basic fetch error", r, b) (* return an error ? *)
    
(* 4.1 case analysis (11) *)
val response_for_fetch : browser -> nreq:request{notForbiddenHeaderfieldInReqHeader (Request?.rf nreq).reqhead} -> bool -> 
			 (cowindow * cowindow * navType) -> Tot (result * nr:request{notForbiddenHeaderfieldInReqHeader (Request?.rf nr).reqhead} * browser)
let response_for_fetch b nreq cors einfo =
    let r = (Request?.rf nreq) in
    let nurl = (firstElement r.requrl) in
    let no = getAOrigin nurl in
    if (isSameOriginRR no r.reqo && cors = false) || (r.reqmode = Navigate) || (r.reqmode = WebSocket) then
    	let req = Request (Request?.rsl nreq) ({r with reqtaint="basic"}) in
    	schemeFetch b req einfo (* perform basic fetch *)
    else if r.reqmode = SameOrigin then (Error "same origin error", nreq, b) (* Network error *)
    else if r.reqmode = NoCORS then
    	let req = Request (Request?.rsl nreq) ({r with reqtaint="opaque"}) in
    	schemeFetch b req einfo (* perform basic fetch *)
    else if (getScheme nurl) <> "http" && (getScheme nurl) <> "https" then (Error "scheme not HTTP", nreq, b) (* Network error *)
    else if r.reqpreflight || (r.requnsafe && (not (isCORSSafelistedMethod r.reqm) || not (isCORSSafelistedHeaders r.reqhead))) then
	(* Other checks, and HTTP fetch *)
	let req = Request (Request?.rsl nreq) ({r with reqtaint="cors";corsflag=true;corspfflag=true}) in
	httpFetch b req true true einfo
    else
	let req = Request (Request?.rsl nreq) ({r with reqtaint="cors";corsflag=true;}) in
	httpFetch b req true false einfo

private val upReferRequest : r:request{notForbiddenHeaderfieldInReqHeader (Request?.rf r).reqhead} -> referer -> refPolicy -> bool -> bool -> 
			     Tot (nr:request{notForbiddenHeaderfieldInReqHeader (Request?.rf nr).reqhead})
let upReferRequest r refer rP cors rf = Request (Request?.rsl r) ({(Request?.rf r) with reqref=refer;reqrefPolicy=rP;corsflag=cors;recflag=rf})

(* Fetch a resource from the network; over CORS*)
(* Main fetch -Section 4.1 fetch.spec.whatwg.org *)
(* This should return a modified browser, with either the pending request or the response parsed *)
(* Or if we consider this to be async always, then this would always queue the request and handle the response later *)
(* Algorithm main fetch using request, optionally with a CORS flag and recursive flag *)
(* Fetch calls response_for_fetch which calls basic fetch which calls http fetch which calls http redirect fetch which calls Fetch! *)
val fetch_resource : browser -> r:request{notForbiddenHeaderfieldInReqHeader (Request?.rf r).reqhead} -> bool -> bool -> (cowindow * cowindow * navType) -> 
		     Tot (result * nr:request{notForbiddenHeaderfieldInReqHeader (Request?.rf nr).reqhead} * browser)
let fetch_resource b r cors rf einfo =
  let req = (Request?.rf r) in
  if (block_port r || reqBlockedCSP r) then (Error "request blocked by CSP", r, b)
  else
    let rP = (if (req.reqrefPolicy = RP_EmptyPolicy && req.reqw <> None) then
    		(match req.reqw with | Some w -> if ((getRefPolicy (CWindow?.cwdoc w)) = RP_EmptyPolicy) then RP_NoRefWhenDowngrade else (getRefPolicy (CWindow?.cwdoc w)))
    	      else if (req.reqrefPolicy = RP_EmptyPolicy) then RP_NoRefWhenDowngrade
    	      else req.reqrefPolicy) in
    let refer = (if (req.reqref <> NoReferrer && not (is_opaqueReq r)) then get_referrer r rP else req.reqref) in
    let ruri = (firstElement req.requrl) in 
    let nreq = upReferRequest r refer rP cors rf in
    let nr = (if (getScheme ruri = "http") && (isSecureHost b ruri) then makeRequestHTTPS nreq else nreq) in
    response_for_fetch b nr cors einfo    (* Queue it as a pending request and process the above steps separately as if waiting for a response in the queue *)

(* Section 4.4 - HTTP-redirect Fetch *)
(* The specification requires a response and not an actResponse and then uses the actResponse accordingly *)
val httpRedirectFetch : browser -> req:request{notForbiddenHeaderfieldInReqHeader (Request?.rf req).reqhead /\ checkHeaderSecLevel (Request?.rf req).reqhead} -> 
			resp:actResponse{requestResponseValid req resp /\ isRedirectResponse (ActResponse?.ar resp)} ->
			bool -> (cowindow * cowindow * navType) -> Tot (result * nr:request{notForbiddenHeaderfieldInReqHeader (Request?.rf nr).reqhead} * browser)
let httpRedirectFetch b req resp cors einfo =
  let r = Request?.rf req in
  if (ActResponse?.ar resp).resploc = None then (Success "no url", req, b) (* NO URL to redirect to *)
  else if (ActResponse?.ar resp).resploc = Some (Failure) then (Error "redirect fetch error : Failure", req, b)
  else
    let u = match ((ActResponse?.ar resp).resploc) with | Some (URL l) -> l in (* _ case should not arise *)
    if r.reqmode = CORS && (not (isSameOriginRR r.reqo (getAOrigin u))) && (includesCredentials u) then (Error "CORS error", req, b) (* Network Error *)
    else if cors && (includesCredentials u) then (Error "CORS with credentials ", req, b) (* Network error *)
    else
      let (ro, nb) = (if (cors && (not (isSameOriginRR (getAOrigin u) (getAOrigin (firstElement r.requrl))))) then (set_op_origin b)
  		     else (r.reqo, b)) in
      let nreq = setRefPolRedirect req resp in
      let nr = Request?.rf nreq in
      let rf = (nr.reqredmode <> "manual") in
      let nh = reclassifyHeader (nr.reqhead) (URI?.usl u) in
      if ((((ActResponse?.ar resp).respcode = 301 || (ActResponse?.ar resp).respcode = 302) && r.reqm = "POST") || ((ActResponse?.ar resp).respcode = 303)) then
      	  let newr = Request (URI?.usl u) ({nr with requrl=u::nr.requrl;reqm="GET";reqo=ro;reqhead=nh;reqredirect=(nr.reqredirect + 1);reqbody=(emptyString (URI?.usl u));corsflag=cors;recflag=rf}) in
          fetch_resource nb newr cors true einfo
      else if ((isRedResponse (ActResponse?.ar resp)) && r.reqm = "POST") then (* redirect for 307/308 with POST *)
      	  let newr = Request (URI?.usl u) ({nr with requrl=u::nr.requrl;reqm=r.reqm;reqo=ro;reqhead=nh;reqredirect=(nr.reqredirect + 1);reqbody=(reclassify nr.reqbody (URI?.usl u));corsflag=cors;recflag=rf}) in
          fetch_resource nb newr cors true einfo
      else  (* other cases - mostly GET for 301/2/7/8 *)
	  let newr = Request (URI?.usl u) ({nr with requrl=u::nr.requrl;reqm=r.reqm;reqo=ro;reqhead=nh;reqredirect=(nr.reqredirect + 1);reqbody=(emptyString (URI?.usl u));corsflag=cors;recflag=rf}) in
          fetch_resource nb newr cors true einfo

(* ******************************************************* *)
(* the browser receives the response on a given connection *)
(* return the request, response, credentials flag and the browser with modified connection pool *)
(* Taking the request as input to allow static checking *)
val getResponse : browser -> connection -> actResponse ->
		  Tot (option ((request * cowindow * cowindow * navType) * actResponse * bool) * browser)
let getResponse b c resp =
  let rcl = (getResponseConn b.conn c) in
    match rcl with
    | None -> (None, b)
    | Some (r, f, ncl) -> (Some (r, resp, f), ({b with conn=ncl}))

(* TODO - process the response body and appropriate changes *)
(* Return error if processing fails *)
(* val processResponseBody : browser -> request -> response -> Tot (result * browser) *)
(* let processResponseBody b r resp = (Response resp, b) *)

(* Process Fetch Response - Step 13, 14, 16 of main fetch algorithm *)
val processFetchResponse : browser -> req:request -> resp:response{validReqResp req resp} -> bool -> Tot (ores:response{validReqResp req ores})
let processFetchResponse b req resp cf =
  match resp with
  | NetworkError e -> NetworkError e
  | RespSuccess s -> RespSuccess s
  | _ ->
  let nreq = (Request?.rf req) in
  let nresp = (match resp with
      | TotResponse r -> (
	     let nl = (
	       if (nreq.reqtaint = "cors") then
		   let hfn = getExposeHeaders r in
		   match hfn with
		   | ["*"] -> if (nreq.reqcredm <> "include") then (getUniqueRespHeader (ActResponse?.ar r).resphead) else (ActResponse?.ar r).respCORS
			     (*13.2 - ??*)
		   | hfl -> hfl
	       else
	           (ActResponse?.ar r).respCORS
		   ) in
	     let aresp = ActResponse (ActResponse?.arl r) ({(ActResponse?.ar r) with respCORS=nl}) in
		       match nreq.reqtaint with
		       | "basic" -> BasicFiltered ({ir=aresp;fr=(basicResponse aresp)})
		       | "cors" -> CORSFiltered ({ir=aresp;fr=(corsResponse aresp)})
		       | "opaque" -> OpaqFiltered ({ir=aresp;fr=opResponse aresp})
		       )
      | FilteredResponse fr -> fr) in
  let iresp = (match nresp with
	    | BasicFiltered b -> b.ir
	    | CORSFiltered c -> c.ir
	    | OpaqFiltered o -> o.ir
	    | OpaqRedFiltered orf -> orf.ir ) in
  let res = if (emptyList (ActResponse?.ar iresp).respurl) then ActResponse (ActResponse?.arl iresp) ({(ActResponse?.ar iresp) with respurl=nreq.requrl})
	    else iresp in
  if (respReqBlockedCSP res req) then (NetworkError "response to req blocked by CSP") (* Network error *)
  else (* (processResponseBody b req (FilteredResponse nresp)) *)
    (FilteredResponse nresp)
	  
(* Process cors preflight response *)
val processCORSPreFlightResponse : browser -> r:request -> resp:actResponse{requestResponseValid r resp} -> bool -> Tot (option actResponse)
let processCORSPreFlightResponse b r resp cf =
    if (corsCheck r resp) && ((ActResponse?.ar resp).respcode >= 200) && ((ActResponse?.ar resp).respcode <= 299) then
       (corsOKResponse r resp)
    else (None) (* Network error *)

(* Process http redirect response required to redirect response-request? *)
val processHttpRedirectResponse : browser -> request -> resp:response{notNetError resp} -> bool -> Tot (bool * result)
let processHttpRedirectResponse b req resp cf =
  let aresp = (match resp with | TotResponse r -> r | FilteredResponse f -> (getInternalResponse f)) in
  if ((ActResponse?.ar aresp).resploc = None) then (false, Success "")
  else if ((Some?.v (ActResponse?.ar aresp).resploc = Failure) || (* for failure return Network Error -- location url of response can be null, failure or url *)
     (match (Some?.v (ActResponse?.ar aresp).resploc) with | URL u -> (getScheme u <> "http" && getScheme u <> "https"))) then (false, (Error "location URL error"))
  else if (Request?.rf req).reqredirect = 20 then (false, (Error "exceeded redirect count"))
  else (true, Success "allow redirect")
  
(* Process http response *)
(* The fetch functions return the request but do not pass over to the callee *)
val processHttpResponse : browser -> req:request{notForbiddenHeaderfieldInReqHeader (Request?.rf req).reqhead} -> resp:actResponse{requestResponseValid req resp} -> bool ->
			  (cowindow * cowindow * navType) -> Tot (ores:response{validReqResp req ores} * browser)
let processHttpResponse b req resp cf einfo =
  let reqf = (Request?.rf req) in
  if (reqf.corspfflag) then
     match processCORSPreFlightResponse b req resp cf with
     | None -> (NetworkError "CORS preflight response error", b) (*Network error *)
     | Some _ -> let (r, nreq, nb) = httpNetworkOrCacheFetch b req reqf.corsflag false einfo in (* CORS preflight response *)
		match r with
		| Error e -> (NetworkError e, nb)
		| Success s -> (RespSuccess s, nb)
  else
    if (reqf.corsflag) && (not (corsCheck req resp)) then (NetworkError "CORS check failure", b)
    else if isRedirectResponse (ActResponse?.ar resp) then (
	    (* (ActResponse?.ar resp).respcode = 301 || (ActResponse?.ar resp).respcode = 302 || (ActResponse?.ar resp).respcode = 303 || *)
	    (* (ActResponse?.ar resp).respcode = 307 || (ActResponse?.ar resp).respcode = 308 then ( *)
	 if reqf.reqredmode = "error" then
	   (NetworkError "redirect mode error", b) (* network error *)
	 else if reqf.reqredmode = "manual" then
	   let loc = getLocationURI resp in
	   let ares = ActResponse (ActResponse?.arl resp) ({(ActResponse?.ar resp) with resploc=loc}) in
	   ((processFetchResponse b req (FilteredResponse (OpaqRedFiltered ({ir=ares;fr=(opRedResponse ares)}))) cf), b)
	 else if reqf.reqredmode = "follow" then
	   let (redirect, res) = processHttpRedirectResponse b req (TotResponse resp) cf in
	   match res with
	   | Error e -> (NetworkError e, b) (* Network Error *)
	   | Success s -> (
	      if redirect = false then
		((processFetchResponse b req (TotResponse resp) cf), b)
	      else
		let (r, nreq, b) = httpRedirectFetch b req resp reqf.corsflag einfo in
		match r with
		| Error e -> (NetworkError e, b)
		| Success s -> (RespSuccess s, b)
	      )
	 else (NetworkError "redirect mode error - case should not arise", b))
    else
	((processFetchResponse b req (TotResponse resp) cf), b)

(* Process network-or-cache response *)
val processNOCResponse : browser -> req:request{notForbiddenHeaderfieldInReqHeader (Request?.rf req).reqhead} -> resp:actResponse{requestResponseValid req resp} -> bool ->
			 (cowindow * cowindow * navType) -> Tot (ores:response{validReqResp req ores} * browser)
let processNOCResponse b req resp cf einfo =
  if ((ActResponse?.ar resp).respcode = 401 && cf = true && (Request?.rf req).corsflag = false && Some? (Request?.rf req).reqw) then (
     if ((Request?.rf req).reqcredflag = false || (Request?.rf req).authflag = true) then
	let (u,p) = getUserPassword b in
	let ourl = (firstElement (Request?.rf req).requrl) in
	let nurl = setUserPwd #(URI?.usl ourl) ourl (classify #PublicVal u (URI?.usl ourl)) (classify #PublicVal p (URI?.usl ourl)) in
	let nreq = Request (Request?.rsl req) ({(Request?.rf req) with requrl=(replace_elem_list (Request?.rf req).requrl 1 nurl)}) in
    	let (r, nr, nb) = httpNetworkOrCacheFetch b nreq false true einfo in (* should we reset cors flag or not? or should it be an option bool *)
	match r with | Error e -> (NetworkError e, nb) | Success s -> (RespSuccess s, nb)
     else
    	let (r, nr, nb) = httpNetworkOrCacheFetch b req false true einfo in
	match r with | Error e -> (NetworkError e, nb) | Success s -> (RespSuccess s, nb)
     )
  else if ((ActResponse?.ar resp).respcode = 407 && Some? (Request?.rf req).reqw) then
      (* Prompt the end user as appropriate in request's window and store the result as a proxy-authentication entry *)
      let (r, nr, nb) = httpNetworkOrCacheFetch b req (Request?.rf req).corsflag (Request?.rf req).authflag einfo in
      match r with | Error e -> (NetworkError e, nb) | Success s -> (RespSuccess s, nb)
  else
      processHttpResponse b req resp cf einfo

(* Processing response for network fetch *)
val processNetworkResponse : browser -> connection -> r:request{notForbiddenHeaderfieldInReqHeader (Request?.rf r).reqhead} -> resp:actResponse{requestResponseValid r resp} ->
			     Tot (ores:response{validReqResp r ores} * browser * option (request * cowindow * cowindow * navType))
let processNetworkResponse b c r resp =
  let (rr,nb) = (getResponse b c resp) in (* remove the first request from the connection list in the browser *)
  match rr with
  | None -> (NetworkError "process network response error", nb, None)
  | Some ((req, sw, tw, ty), resp, cf) ->
	 (* if (req = r) then (\* the request changes quite a bit while processing -- this might not be the same. *\) *)
 	   let nresp = setRespHTTPS (setRespCSPList resp) in
	   let nbr = if cf then (setCookie nb r nresp) else nb in
	   let einfo = (sw, tw, ty) in
	   (* based on the response code here, recall this function with authentication details. cannot prove termination and some precondition failure above *)
	   let (res, br) = processNOCResponse nbr r nresp cf einfo in
	   (res, br, Some (r, sw, tw, ty))
	 (* else *)
	   (* (NetworkError "incorrect request access error", nb, None) (\* some other request accessed from the connection pool *\) *)

