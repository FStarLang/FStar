(*
  fetch.spec.whatwg.org and referrer-policy spec (https://www.w3.org/TR/referrer-policy/)
  Describes the functionality of fetching a resource on the network and handling the response
*)
module Browser.HTTPFetch

open AuxiliaryFunctions
open Web.Origin
open Web.URI
open Browser.AuxiliaryDatatypes
open Secret.SecString
open Browser.Datatypes
open Browser.ContentSecurityPolicy
open Browser.RequestResponseHeader

module List = FStar.List.Tot

#reset-options "--z3rlimit 100"

(* prompt user to get username and password *)
val getUserPassword : browser -> Tot (string * string)
let getUserPassword b = ("user", "pwd")

(* 4.1 Main Fetch - Should browserRequest be blocked due to bad origin_port *)
val block_origin_port : browserRequest -> Tot bool
let block_origin_port r =
  let r_protocol = getScheme (List.hd (BrowserRequest?.browser_request r).requrl) in 
  let r_port = getPort (List.hd (BrowserRequest?.browser_request r).requrl) in
  if r_protocol = "ftp" && (r_port = Some 20 || r_port = Some 21) then false
  else if (r_protocol = "http" || r_protocol = "https") && (Some? r_port) && port_is_bad (Some?.v r_port) then true
  else false (*request should be allowed*)

(* 8.3 - Referrer Policy - Determine browserRequest's referrer *)
val get_referrer : r:browserRequest{(BrowserRequest?.browser_request r).reqref <> NoReferrer} -> rp:referrer_policy{rp <> RP_EmptyPolicy} -> Tot referer
let get_referrer r rp =
  let refSource = (match (BrowserRequest?.browser_request r).reqref with | Client w -> (getWinURI w) | URLReferrer u -> u) in
  let refOrigin = URLReferrer (getOriginURL (refSource)) in
  let refURL = URLReferrer (getRefURL (refSource)) in
  match rp with
  | RP_NoReferrer -> NoReferrer
  | RP_NoRefWhenDowngrade -> refURL
  | RP_SameOrigin -> (match (isSameAOrigin (BrowserRequest?.browser_request r).reqo (getAOrigin refSource)) with
		    | false -> NoReferrer
		    | true -> refURL)
  | RP_Origin     -> refOrigin
  | RP_StrictOrigin -> refOrigin (* Check for TLS-protected windows*)
  | RP_OriginWhenCO -> (match (isSameAOrigin (BrowserRequest?.browser_request r).reqo (getAOrigin refSource)) with
		      | false -> refOrigin 
		      | true -> refURL)
  | RP_StrictWhenCO -> (match (isSameAOrigin (BrowserRequest?.browser_request r).reqo (getAOrigin refSource)) with
		      | false -> refOrigin
		      | true -> refURL)
  | RP_UnsafeURL -> refURL

(* Referrer Policy --- 8.2. Set request’s referrer policy on redirect *)
val setRefPolRedirect : req:browserRequest{notForbiddenHeaderfieldInReqHeader req.browser_request.reqhead /\ checkHeaderSecLevel req.browser_request.reqhead} -> 
			resp:browserResponse{req.browser_request.reqbrowser = resp.b_response.respbrowser /\ is_valid_browser_response_for_request req resp} -> 
			Tot (nreq:browserRequest{nreq.browser_request.reqbrowser = resp.b_response.respbrowser /\ 
						nreq.browser_request.reqbrowser = req.browser_request.reqbrowser /\
						is_valid_browser_response_for_request nreq resp /\ 
						notForbiddenHeaderfieldInReqHeader nreq.browser_request.reqhead /\ 
						checkHeaderSecLevel nreq.browser_request.reqhead})
let setRefPolRedirect req resp =
  let refPol = parse_response_referrer_policy resp in
  if refPol = RP_EmptyPolicy then req 
  else BrowserRequest (BrowserRequest?.breq_secrecy_level req) ({(BrowserRequest?.browser_request req) with reqreferrer_policy=refPol})

val refPolRedForbiddenHeaderLemma : req:browserRequest{notForbiddenHeaderfieldInReqHeader (BrowserRequest?.browser_request req).reqhead} -> 
				    resp:browserResponse{req.browser_request.reqbrowser = resp.b_response.respbrowser /\ is_valid_browser_response_for_request req resp} -> 
				    Lemma (requires (notForbiddenHeaderfieldInReqHeader (BrowserRequest?.browser_request req).reqhead)) 
				    (ensures (notForbiddenHeaderfieldInReqHeader (BrowserRequest?.browser_request (setRefPolRedirect req resp)).reqhead)) 
let refPolRedForbiddenHeaderLemma req resp = ()

(* Is request's method cors-safelisted method *)
val isCORSSafelistedMethod : reqMethod -> Tot bool
let isCORSSafelistedMethod m = (m="GET" || m="HEAD" || m="POST")

(* Are the request and response from same origin *)
val isSameOriginRR : a_origin -> a_origin -> Tot bool
let isSameOriginRR reqo respo = (isSameAOrigin reqo respo) 

val hasAuthzHeader : header -> Tot bool
let rec hasAuthzHeader h =
  match h with
  | [] -> false
  | (hf,hv)::tl -> (hf="Authorization") || (hasAuthzHeader tl)




(* Section 4.6 - HTTP Network fetch *) 
(* can return network error at some points *)
val httpNetworkFetch : b:browser -> r:browserRequest{r.browser_request.reqbrowser = b.bid} -> bool -> 
		       (sw:cowindow{sw.cwbid = b.bid} * tw:cowindow{tw.cwbid = b.bid} * navType) -> 
		       Tot (result * nb:browser{nb.bid = b.bid /\ r.browser_request.reqbrowser = nb.bid})
let httpNetworkFetch b r cflag einfo = sendRequest b r cflag einfo

private val getFetchHeader : b:browser -> r:browserRequest{r.browser_request.reqbrowser = b.bid} -> bool -> Tot (bool * h:header{checkHeaderSecLevel h})
let getFetchHeader b req cors =
    let r = BrowserRequest?.browser_request req in 
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
val httpNetworkOrCacheFetch : b:browser -> r:browserRequest{notForbiddenHeaderfieldInReqHeader r.browser_request.reqhead /\ r.browser_request.reqbrowser = b.bid} -> 
			      bool -> bool -> (sw:cowindow{sw.cwbid = b.bid} * tw:cowindow{tw.cwbid = b.bid} * navType) -> 
			      Tot (result * nb:browser{nb.bid = b.bid /\ r.browser_request.reqbrowser = nb.bid})
let httpNetworkOrCacheFetch b req cors af einfo =
    let r = req.browser_request in 
    let (cflag, nh) = getFetchHeader b req cors in 
    let nr = BrowserRequest (req.breq_secrecy_level) ({r with reqhead=nh;corsflag=cors;corspfflag=false;authflag=af}) in
    let (re, nb) = (httpNetworkFetch b nr cflag einfo) in
    (re, nb)

(* A version of httpNetworkOrCacheFetch to handle preflight fetches as they already contain headers with forbidden name - 
   these.are never redirected as it ultimately uses httpNetworkOrCacheFetch 
*)
val httpNetworkOrCachePreflightFetch : b:browser -> r:browserRequest{r.browser_request.reqbrowser = b.bid} -> bool -> bool -> (sw:cowindow{sw.cwbid = b.bid} * tw:cowindow{tw.cwbid = b.bid} * navType) -> 
				       Tot (result * nb:browser{nb.bid = b.bid /\ r.browser_request.reqbrowser = nb.bid})
let httpNetworkOrCachePreflightFetch b req cors af einfo =
    let r = req.browser_request in 
    let (cflag, nh) = getFetchHeader b req cors in 
    let nr = BrowserRequest (req.breq_secrecy_level) ({r with reqhead=nh;corsflag=cors;corspfflag=false;authflag=af}) in
    (httpNetworkFetch b nr cflag einfo) 

val preflight_request : b:browser -> r:browserRequest{r.browser_request.reqbrowser = b.bid} -> 
			h:header{checkHeaderSecLevel h /\ List.for_all (fun (hf,hv) -> Headervalue?.hvs hv = PublicVal) h} -> 
			Tot (nr:browserRequest{nr.browser_request.reqbrowser = b.bid})
let preflight_request b req h =
    let r = req.browser_request in
    let rs = req.breq_secrecy_level in
    BrowserRequest rs ({reqbrowser=r.reqbrowser;reqm="OPTIONS";requrl=r.requrl;reqhead=h;reqo=r.reqo;reqw=None;reqinit=r.reqinit;reqtype=r.reqtype;reqdest=r.reqdest;reqtarget=None;reqredirect=0;reqredmode="follow";reqref=r.reqref;reqreferrer_policy=r.reqreferrer_policy;reqnonce="";reqparser="";requnsafe=false;reqpreflight=false;reqsync=false;reqmode=NoCORS;reqtaint="basic";reqcredm="omit";reqcredflag=false;reqbody=(empty_secret_string rs);corsflag=r.corsflag;corspfflag=true;authflag=r.authflag;recflag=r.recflag})

(* Section 4.7 - CORS-Preflight Fetch *)
val corsPreflightFetch : b:browser -> r:browserRequest{r.browser_request.reqbrowser = b.bid} -> (sw:cowindow{sw.cwbid = b.bid} * tw:cowindow{tw.cwbid = b.bid} * navType) -> 
			 Tot (result * nb:browser{nb.bid = b.bid /\ r.browser_request.reqbrowser = nb.bid})
let corsPreflightFetch b req einfo =
    let r = req.browser_request in
    let u = (List.hd r.requrl) in
    let nh = [("Access-Control-Request-Method", (Headervalue PublicVal r.reqm));("Access-Control-Request-Headers",(Headervalue PublicVal (getHeaderNames r.reqhead)))] in
    let pr = (let rs = req.breq_secrecy_level in
		  BrowserRequest rs ({reqbrowser=r.reqbrowser;reqm="OPTIONS";requrl=r.requrl;reqhead=nh;reqo=r.reqo;reqw=None;reqinit=r.reqinit;reqtype=r.reqtype;reqdest=r.reqdest;reqtarget=None;reqredirect=0;reqredmode="follow";reqref=r.reqref;reqreferrer_policy=r.reqreferrer_policy;reqnonce="";reqparser="";requnsafe=false;reqpreflight=false;reqsync=false;reqmode=NoCORS;reqtaint="basic";reqcredm="omit";reqcredflag=false;reqbody=(empty_secret_string rs);corsflag=r.corsflag;corspfflag=true;authflag=r.authflag;recflag=r.recflag})) in
    httpNetworkOrCachePreflightFetch b pr false false einfo

(* Section 4.3 - HTTP Fetch *)
val httpFetch : b:browser -> r:browserRequest{notForbiddenHeaderfieldInReqHeader r.browser_request.reqhead /\ r.browser_request.reqbrowser = b.bid} -> 
		bool -> bool -> (sw:cowindow{sw.cwbid = b.bid} * tw:cowindow{tw.cwbid = b.bid} * navType) -> 
		Tot (result * nb:browser{nb.bid = b.bid /\ r.browser_request.reqbrowser = nb.bid})
let httpFetch b r cors pf einfo = (* check for skip-service-worker. define service workers. for now assuming that the page doesnt use service workers *)
  if (pf) then
      let nreq = BrowserRequest (r.breq_secrecy_level) ({r.browser_request with corsflag=cors;corspfflag=true}) in
      corsPreflightFetch b nreq einfo
  else
      httpNetworkOrCacheFetch b r cors false einfo

(* Section 4.2 - Scheme Fetch *)
(* case analyse the protocol to determine what to do. Considering only http(s) cases, calls into httpFetch *)
val schemeFetch : b:browser -> r:browserRequest{notForbiddenHeaderfieldInReqHeader r.browser_request.reqhead /\ r.browser_request.reqbrowser = b.bid} -> 
		  (sw:cowindow{sw.cwbid = b.bid} * tw:cowindow{tw.cwbid = b.bid} * navType) -> 
		  Tot (result * nb:browser{nb.bid = b.bid /\  r.browser_request.reqbrowser = nb.bid})
let schemeFetch b r einfo =
  let rurl = (List.hd r.browser_request.requrl) in
  if getScheme (rurl) = "http" || getScheme (rurl) = "https" then
     httpFetch b r false false einfo
  else (Error "basic fetch error", b) (* return an error ? *)
    
(* 4.1 case analysis (11) *)
val response_for_fetch : b:browser -> r:browserRequest{notForbiddenHeaderfieldInReqHeader r.browser_request.reqhead /\ r.browser_request.reqbrowser = b.bid} -> 
			 bool -> (sw:cowindow{sw.cwbid = b.bid} * tw:cowindow{tw.cwbid = b.bid} * navType) -> 
			 Tot (result * nr:browserRequest{notForbiddenHeaderfieldInReqHeader nr.browser_request.reqhead /\ nr.browser_request.reqbrowser = b.bid} * 
				       nb:browser{nb.bid = b.bid /\ r.browser_request.reqbrowser = nb.bid})
let response_for_fetch b r cors einfo =
    let req = r.browser_request in
    let req_url = (List.hd req.requrl) in
    let no = getAOrigin req_url in
    if (isSameOriginRR no req.reqo && cors = false) || (req.reqmode = Navigate) || (req.reqmode = WebSocket) then
    	let nreq = BrowserRequest r.breq_secrecy_level ({req with reqtaint="basic"}) in
    	(match schemeFetch b nreq einfo with | (res, nb) -> (res, nreq, nb)) (* perform basic fetch *)
    else if req.reqmode = SameOrigin then (Error "same origin error", r, b) (* Network error *)
    else if req.reqmode = NoCORS then
    	let nreq = BrowserRequest r.breq_secrecy_level ({req with reqtaint="opaque"}) in
    	(match schemeFetch b nreq einfo with | (res, nb) -> (res, nreq, nb)) (* perform basic fetch *)
    else if (getScheme req_url) <> "http" && (getScheme req_url) <> "https" then (Error "origin_protocol not HTTP", r, b) (* Network error *)
    else if req.reqpreflight || (req.requnsafe && (not (isCORSSafelistedMethod req.reqm) || not (isCORSSafelistedHeaders req.reqhead))) then
	(* Other checks, and HTTP fetch *)
	let nreq = BrowserRequest r.breq_secrecy_level ({req with reqtaint="cors";corsflag=true;corspfflag=true}) in
	(match httpFetch b nreq true true einfo with | (res, nb) -> (res, nreq, nb))
    else
	let nreq = BrowserRequest r.breq_secrecy_level ({req with reqtaint="cors";corsflag=true;}) in
	(match httpFetch b nreq true false einfo with | (res, nb) -> (res, nreq, nb)) 

private val upReferRequest : r:browserRequest{notForbiddenHeaderfieldInReqHeader (BrowserRequest?.browser_request r).reqhead} -> referer -> referrer_policy -> bool -> bool -> 
			     Tot (nr:browserRequest{notForbiddenHeaderfieldInReqHeader (BrowserRequest?.browser_request nr).reqhead})
let upReferRequest r refer rP cors rf = BrowserRequest r.breq_secrecy_level ({r.browser_request with reqref=refer;reqreferrer_policy=rP;corsflag=cors;recflag=rf})

(* Fetch a resource from the network; over CORS*)
(* Main fetch -Section 4.1 fetch.spec.whatwg.org *)
(* This should return a modified browser, with either the pending request or the response .arsed *)
(* Or if we consider this to be async always, then this would always queue the request and handle the response later *)
(* Algorithm main fetch using request, optionally with a CORS flag and recursive flag *)
(* Fetch calls response_for_fetch which calls basic fetch which calls http fetch which calls http redirect fetch which calls Fetch! *)
val fetch_resource : b:browser -> r:browserRequest{notForbiddenHeaderfieldInReqHeader r.browser_request.reqhead /\ r.browser_request.reqbrowser = b.bid} -> 
		     bool -> bool -> (sw:cowindow{sw.cwbid = b.bid} * tw:cowindow{tw.cwbid = b.bid} * navType) -> 
		     Tot (result * nr:browserRequest{notForbiddenHeaderfieldInReqHeader nr.browser_request.reqhead /\ nr.browser_request.reqbrowser = b.bid} * 
				       nb:browser{nb.bid = b.bid /\ r.browser_request.reqbrowser = nb.bid})
let fetch_resource b r cors rf einfo =
  let req = r.browser_request in
  if (block_origin_port r || reqBlockedCSP r) then (Error "request blocked by CSP", r, b)
  else
    let rP = (if (req.reqreferrer_policy = RP_EmptyPolicy && req.reqw <> None) then
    		(match req.reqw with | Some w -> if ((getRefPolicy w.cwin.cwdoc) = RP_EmptyPolicy) then RP_NoRefWhenDowngrade else (getRefPolicy w.cwin.cwdoc))
    	      else if (req.reqreferrer_policy = RP_EmptyPolicy) then RP_NoRefWhenDowngrade
    	      else req.reqreferrer_policy) in
    let refer = (if (req.reqref <> NoReferrer && not (is_opaqueReq r)) then get_referrer r rP else req.reqref) in
    let ruri = (List.hd req.requrl) in 
    let nreq = upReferRequest r refer rP cors rf in
    let nr = (if (getScheme ruri = "http") && (isSecureHost b ruri) then makeRequestHTTPS nreq else nreq) in
    response_for_fetch b nr cors einfo    (* Queue it as a pending request and process the above steps se.arately as if waiting for a response in the queue *)

(* Section 4.4 - HTTP-redirect Fetch *)
(* The specification requires a response and not an browserResponse and then uses the browserResponse accordingly *)
val httpRedirectFetch : b:browser -> req:browserRequest{notForbiddenHeaderfieldInReqHeader req.browser_request.reqhead /\ checkHeaderSecLevel req.browser_request.reqhead /\ 
											  req.browser_request.reqbrowser = b.bid} -> 
			resp:browserResponse{req.browser_request.reqbrowser = resp.b_response.respbrowser /\ is_valid_browser_response_for_request req resp /\ 
									    isRedirectResponse resp.b_response.respcode} -> bool -> 
			(sw:cowindow{sw.cwbid = b.bid} * tw:cowindow{tw.cwbid = b.bid} * navType) -> 
			Tot (result * nr:browserRequest{notForbiddenHeaderfieldInReqHeader nr.browser_request.reqhead /\ nr.browser_request.reqbrowser = b.bid} * 
				      nb:browser{nb.bid = b.bid /\ req.browser_request.reqbrowser = nb.bid})
let httpRedirectFetch b req resp cors einfo =
  let r = BrowserRequest?.browser_request req in
  if resp.b_response.resploc = None then (Success "no url", req, b) (* NO URL to redirect to *)
  else if resp.b_response.resploc = Some (Failure) then (Error "redirect fetch error : Failure", req, b)
  else
    let u = match (resp.b_response.resploc) with | Some (URL l) -> l in (* _ case should not.arise *)
    if r.reqmode = CORS && (not (isSameOriginRR r.reqo (getAOrigin u))) && (includesCredentials u) then (Error "CORS error", req, b) (* Network Error *)
    else if cors && (includesCredentials u) then (Error "CORS with credentials ", req, b) (* Network error *)
    else
      let (ro, nb) = (if (cors && (not (isSameOriginRR (getAOrigin u) (getAOrigin (List.hd r.requrl))))) then (set_op_origin b)
    		     else (r.reqo, b)) in
      let nreq = setRefPolRedirect req resp in
      let nr = BrowserRequest?.browser_request nreq in
      let rf = (nr.reqredmode <> "manual") in
      let nh = reclassifyHeader (nr.reqhead) (URI?.uri_secrecy_level u) in
      if (((resp.b_response.respcode = 301 || resp.b_response.respcode = 302) && r.reqm = "POST") || (resp.b_response.respcode = 303)) then
      	  let newr = BrowserRequest (URI?.uri_secrecy_level u) ({nr with requrl=u::nr.requrl;reqm="GET";reqo=ro;reqhead=nh;reqredirect=(nr.reqredirect + 1);reqbody=(empty_secret_string (URI?.uri_secrecy_level u));corsflag=cors;recflag=rf}) in
          fetch_resource nb newr cors true einfo
      else if ((isRedirectBodyResponse resp.b_response.respcode) && r.reqm = "POST") then (* redirect for 307/308 with POST *)
      	  let newr = BrowserRequest (URI?.uri_secrecy_level u) ({nr with requrl=u::nr.requrl;reqm=r.reqm;reqo=ro;reqhead=nh;reqredirect=(nr.reqredirect + 1);reqbody=(reclassify_secret_string nr.reqbody (URI?.uri_secrecy_level u));corsflag=cors;recflag=rf}) in
          fetch_resource nb newr cors true einfo
      else  (* other cases - mostly GET for 301/2/7/8 *)
      	  let newr = BrowserRequest (URI?.uri_secrecy_level u) ({nr with requrl=u::nr.requrl;reqm=r.reqm;reqo=ro;reqhead=nh;reqredirect=(nr.reqredirect + 1);reqbody=(empty_secret_string (URI?.uri_secrecy_level u));corsflag=cors;recflag=rf}) in
          fetch_resource nb newr cors true einfo

(* ******************************************************* *)
(* the browser receives the response on a given connection *)
(* return the request, credentials flag and the browser with modified connection pool along with the source, .arget windows and navigation type *)
(* Taking the request as input to allow static checking *)
(* val getRequestForResponse : browser -> connection -> resp:browserResponse -> *)
(* 		  Tot (option (r:browserRequest{notForbiddenHeaderfieldInReqHeader (BrowserRequest?.browser_request r).reqhead /\ is_valid_browser_response_for_request r resp}) *  *)
(* 		      option (sw:cowindow{sw.cwbid = b.bid} * tw:cowindow{tw.cwbid = b.bid} * navType) *  *)
(* 		      option bool *  *)
(* 		      browser) *)
(* let getRequestForResponse b c resp = *)
(*   let rcl = (getResponseConn b.conn c) in *)
(*     match rcl with *)
(*     | None, f, ncl -> (None, None, f, ({b with conn=ncl})) *)
(*     | Some (req, sw, tw, ty), f, ncl ->  *)
(* 		     (\* check if valid request -- .arry the request in response *\)  *)
(* 		     (Some req, Some (sw, tw, ty), f, ({b with conn=ncl})) *)
				       
val getResponse : b:browser -> connection -> resp:browserResponse{resp.b_response.respbrowser = b.bid} ->
		  Tot (option ((nr:browserRequest{b.bid = nr.browser_request.reqbrowser} * 
			      sw:cowindow{sw.cwbid = b.bid} * tw:cowindow{tw.cwbid = b.bid} * navType) * browserResponse * bool) * nb:browser{nb.bid = b.bid})
let getResponse b c resp =
  let rcl = (getResponseConn b.br.conn c) in
    match rcl with
    | None -> (None, b)
    | Some (r, f, ncl) -> (Some (r, resp, f), (Browser b.bid ({b.br with conn=ncl})))

(* TODO - process the response body and appropriate changes *)
(* Return error if processing fails *)
(* val processResponseBody : browser -> request -> response -> Tot (result * browser) *)
(* let processResponseBody b r resp = (Response resp, b) *)

(* Process Fetch Response - Step 13, 14, 16 of main fetch algorithm *)
val processFetchResponse : b:browser -> req:browserRequest{req.browser_request.reqbrowser = b.bid} -> 
			   resp:response{is_valid_response_for_request req resp} -> bool -> Tot (ores:response{is_valid_response_for_request req ores})
let processFetchResponse b req resp cf =
  match resp with
  | NetworkError e -> NetworkError e
  | RespSuccess s -> RespSuccess s
  | BResponse r ->
      let nreq = req.browser_request in
      let nresp = (let nl = (if (nreq.reqtaint = "cors") then
				let hfn = getExposeHeaders r in
				match hfn with
				| ["*"] -> if (nreq.reqcredm <> "include") then (getUniqueRespHeader r.b_response.resphead) else r.b_response.respCORS
				(*13.2 - ??*)
				| hfl -> hfl
			     else
				 r.b_response.respCORS) in
		  BrowserResponse r.bresp_secrecy_level ({r.b_response with respCORS=nl})) in
      let res = if (list_is_empty nresp.b_response.respurl) then 
		   BrowserResponse nresp.bresp_secrecy_level ({nresp.b_response with respurl=nreq.requrl})
		else nresp in
      if (respReqBlockedCSP res req) then (NetworkError "response to req blocked by CSP") (* Network error *)
      else (BResponse nresp)
	  
(* Process cors preflight response *)
val processCORSPreFlightResponse : b:browser -> r:browserRequest{b.bid = r.browser_request.reqbrowser} -> 
				   resp:browserResponse{r.browser_request.reqbrowser = resp.b_response.respbrowser /\ is_valid_browser_response_for_request r resp} -> bool -> 
				   Tot (option (fresp:browserResponse{r.browser_request.reqbrowser = fresp.b_response.respbrowser /\ is_valid_browser_response_for_request r fresp}))
let processCORSPreFlightResponse b r resp cf =
    if (corsCheck r resp) && (resp.b_response.respcode >= 200) && (resp.b_response.respcode <= 299) then
       (corsOKResponse r resp)
    else (None) (* Network error *)

(* Process http redirect response required to redirect response-request? *)
val processHttpRedirectResponse : b:browser -> r:browserRequest{b.bid = r.browser_request.reqbrowser} -> resp:response{BResponse? resp} -> bool -> Tot (bool * result)
let processHttpRedirectResponse b req resp cf =
  let aresp = (match resp with | BResponse r -> r) in
  if (aresp.b_response.resploc = None) then (false, Success "")
  else if ((Some?.v aresp.b_response.resploc = Failure) || (* for failure return Network Error -- location url of response can be null, failure or url *)
     (match (Some?.v aresp.b_response.resploc) with | URL u -> (getScheme u <> "http" && getScheme u <> "https"))) then (false, (Error "location URL error"))
  else if req.browser_request.reqredirect = 20 then (false, (Error "exceeded redirect count"))
  else (true, Success "allow redirect")
  
(* Process http response *)
(* The fetch functions return the request but do not pass over to the callee *)
val processHttpResponse : b:browser -> req:browserRequest{b.bid = req.browser_request.reqbrowser /\ 
							       notForbiddenHeaderfieldInReqHeader (BrowserRequest?.browser_request req).reqhead} -> 
			  resp:browserResponse{req.browser_request.reqbrowser = resp.b_response.respbrowser /\ is_valid_browser_response_for_request req resp} -> bool ->
			  (sw:cowindow{sw.cwbid = b.bid} * tw:cowindow{tw.cwbid = b.bid} * navType) -> Tot (ores:response{is_valid_response_for_request req ores} * nb:browser{nb.bid = b.bid})
let processHttpResponse b req resp cf einfo =
  let reqf = req.browser_request in
  if (reqf.corspfflag) then
     match processCORSPreFlightResponse b req resp cf with
     | None -> (NetworkError "CORS preflight response error", b) (*Network error *)
     | Some _ -> let (r, nb) = httpNetworkOrCacheFetch b req reqf.corsflag false einfo in (* CORS preflight response *)
		match r with
		| Error e -> (NetworkError e, nb)
		| Success s -> (RespSuccess s, nb)
  else
    if (reqf.corsflag) && (not (corsCheck req resp)) then (NetworkError "CORS check failure", b)
    else if isRedirectResponse resp.b_response.respcode then (
	    (* resp.b_response.respcode = 301 || resp.b_response.respcode = 302 || resp.b_response.respcode = 303 || *)
	    (* resp.b_response.respcode = 307 || resp.b_response.respcode = 308 then ( *)
	 if reqf.reqredmode = "error" then
	   (NetworkError "redirect mode error", b) (* network error *)
	 else if reqf.reqredmode = "manual" then
	   let loc = getLocationURI resp.b_response in
	   let ares = BrowserResponse resp.bresp_secrecy_level ({resp.b_response with resploc=loc}) in
	   assert(is_valid_browser_response_for_request req ares);
	   ((processFetchResponse b req (BResponse ares) cf), b)
	 else if reqf.reqredmode = "follow" then
	   let (redirect, res) = processHttpRedirectResponse b req (BResponse resp) cf in
	   match res with
	   | Error e -> (NetworkError e, b) (* Network Error *)
	   | Success s -> (
	      if redirect = false then
		((processFetchResponse b req (BResponse resp) cf), b)
	      else
		let (r, b) = httpRedirectFetch b req resp reqf.corsflag einfo in
		match r with
		| Error e -> (NetworkError e, b)
		| Success s -> (RespSuccess s, b)
	      )
	 else (NetworkError "redirect mode error - case should not.arise", b))
    else
	((processFetchResponse b req (BResponse resp) cf), b)

(* Process network-or-cache response *)
val processNOCResponse : b:browser -> 
			 req:browserRequest{notForbiddenHeaderfieldInReqHeader (BrowserRequest?.browser_request req).reqhead /\ b.bid = req.browser_request.reqbrowser} -> 
			 resp:browserResponse{is_valid_browser_response_for_request req resp /\ req.browser_request.reqbrowser = resp.b_response.respbrowser} -> bool ->
			 (sw:cowindow{sw.cwbid = b.bid} * tw:cowindow{tw.cwbid = b.bid} * navType) -> 
			 Tot (ores:response{is_valid_response_for_request req ores} * nb:browser{nb.bid = b.bid})
let processNOCResponse b req resp cf einfo =
  if (resp.b_response.respcode = 401 && cf = true && (BrowserRequest?.browser_request req).corsflag = false && Some? (BrowserRequest?.browser_request req).reqw) then (
     if ((BrowserRequest?.browser_request req).reqcredflag = false || (BrowserRequest?.browser_request req).authflag = true) then
	let (u,p) = getUserPassword b in
	let ourl = (List.hd (BrowserRequest?.browser_request req).requrl) in
	let nurl = setUserPwd #(URI?.uri_secrecy_level ourl) ourl (classify_secret_string #PublicVal u (URI?.uri_secrecy_level ourl)) (classify_secret_string #PublicVal p (URI?.uri_secrecy_level ourl)) in
	let nreq = BrowserRequest (BrowserRequest?.breq_secrecy_level req) ({(BrowserRequest?.browser_request req) with requrl=(list_replace_element_at (BrowserRequest?.browser_request req).requrl 1 nurl)}) in
    	let (r, nb) = httpNetworkOrCacheFetch b nreq false true einfo in (* should we reset cors flag or not? or should it be an option bool *)
	match r with | Error e -> (NetworkError e, nb) | Success s -> (RespSuccess s, nb)
     else
    	let (r, nb) = httpNetworkOrCacheFetch b req false true einfo in
	match r with | Error e -> (NetworkError e, nb) | Success s -> (RespSuccess s, nb)
     )
  else if (resp.b_response.respcode = 407 && Some? (BrowserRequest?.browser_request req).reqw) then
      (* Prompt the end user as appropriate in request's window and store the result as a proxy-authentication entry *)
      let (r, nb) = httpNetworkOrCacheFetch b req (BrowserRequest?.browser_request req).corsflag (BrowserRequest?.browser_request req).authflag einfo in
      match r with | Error e -> (NetworkError e, nb) | Success s -> (RespSuccess s, nb)
  else
      processHttpResponse b req resp cf einfo

val processNetworkResponse : b:browser -> connection -> 
			     r:browserRequest{notForbiddenHeaderfieldInReqHeader (BrowserRequest?.browser_request r).reqhead /\ b.bid = r.browser_request.reqbrowser} -> 
			     resp:browserResponse{is_valid_browser_response_for_request r resp /\ b.bid = resp.b_response.respbrowser} -> 
			     Tot (ores:response{is_valid_response_for_request r ores} * nb:browser{nb.bid = b.bid} * 
				 option (nr:browserRequest{notForbiddenHeaderfieldInReqHeader nr.browser_request.reqhead /\ b.bid = nr.browser_request.reqbrowser} * 
				 sw:cowindow{sw.cwbid = b.bid} * tw:cowindow{tw.cwbid = b.bid} * navType))
let processNetworkResponse b c r resp =
  let (rr,nb) = (getResponse b c resp) in (* remove the first request from the connection list in the browser *)
  match rr with
  | None -> (NetworkError "process network response error", nb, None)
  | Some ((req, sw, tw, ty), resp, cf) ->
	   (* if (req = r) then (\* the request changes quite a bit while processing -- this might not be the same. *\) *)
 	   let nresp = setRespHTTPS (setRespCSPList resp) in
	   let nbr = if cf then (set_cookie_browser nb r nresp) else nb in
	   let einfo = (sw, tw, ty) in
	   (* based on the response code here, recall this function with authentication details. cannot prove termination and some precondition failure above *)
	   let (res, br) = processNOCResponse nbr r nresp cf einfo in
	   (res, br, Some (r, sw, tw, ty))
