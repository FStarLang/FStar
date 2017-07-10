module OAuth.RP

open FStar.All
open FStar.Heap
open FStar.IO
open Web.Origin
open Web.URI
open Secret.SecString
open Browser.AuxiliaryDatatypes
open Browser.Datatypes
open AuxiliaryFunctions
open Browser.StringFunctions
open Browser.Model.Interface
open NetworkRequestInterface
open OAuth.Datatypes

(* ***** RP.COM ***** *)
let rpurl = ({c_origin=rpori;c_uname=emptyString (SecretVal [rpori]);c_pwd=emptyString (SecretVal [rpori]);c_path=[];c_querystring=[];c_fragment=emptyString (SecretVal [rpori])})
let rpuri = mk_uri rpurl

val checkRPReq : req:request -> Tot (b:bool)
let checkRPReq req =
  match (Request?.rsl req) with
  | PublicVal -> true
  | SecretVal ol -> List.mem rpori ol

val rpReqLemma : req:request -> Lemma (requires (checkRPReq req)) (ensures (restricts (Request?.rsl req) (SecretVal [rpori]))) [SMTPat (checkRPReq req)]
let rpReqLemma req = ()

(* use a browser for sending request containing authcode from RP to IP at the end of the protocol *)
let rpb = ST.alloc (init_browser)
let irp = match (set_unique_id !rpb) with | (f, s) -> rpb := s; f (* Get a unique_id (f) and browser (s) *)
let rpdoc = {dloc=rpuri;dref=blank_uri;dori=(mk_aorigin rpurl.c_origin);dHTTPS="none";drefPol=RP_OriginWhenCO;dCSP=[];dsbox=[];}
(* create a window in the browser to send the request with "rpdoc" as the document *)
let rpsw = 
      let hist = HistEntry (URI?.usl rpuri) (URI?.u rpuri) get_time rpdoc irp in 
      let newwin = (win_to_cowin ({winid=irp;wname="";wloc=rpuri;wframes=[];wopener=None;wparent=None;whist={hlhe=[hist];hcur=1};wdoc=(rpdoc);wsbox=[];})) in
      (rpb := ({(!rpb) with windows=newwin::(!rpb).windows})); newwin

val rpLoginIPAuth : r:request -> ML (resp:actResponse{requestResponseValid r resp}) 
let rpLoginIPAuth r =
  let urisl = s_getReqURISecLevel r in
  let ruri = mk_uri (s_getRequestURI #urisl r) in (* get the request url *)
  let qs = getQS ruri in
  let ip = getQSVal #urisl qs "IP" in
  if s_equal #urisl #PublicVal ip "ip.com" then 
  (
    let sl = (SecretVal [rpori;ipori]) in 
    let sid = (genSecret sl) in
    let state = (genSecret sl) in 
    let cid = (getRPClientID ipori) in
    (
      (let logsession:loginSession = [(ipori, sid, state)] in
      rpLS := List.append logsession (!rpLS));
      let respuri = ({c_origin=ipori;c_uname=emptyString sl;c_pwd=emptyString sl;c_path=[classify #PublicVal "authEP" sl];c_querystring=[(classify #PublicVal "client_id" sl,classify #PublicVal cid sl);(classify #PublicVal "redirect_uri" sl, classify #PublicVal "https://rp.com:443/codeEP/" sl);(classify #PublicVal "origin" sl, classify #PublicVal "https://rp.com/" sl);(classify #PublicVal "csrftoken" sl,getSecret state)];c_fragment=emptyString sl}) in
      let rpREP = curi_to_hstring respuri in 
      let rpResp = ActResponse sl ({resptype="default";respcode=301;respurl=[]; resphead=[("Set-Cookie", (mk_svheaderval sid));("Location", (mk_headerval rpREP))]; respbody=(emptyString sl);resptrail=[];respHTTPS="modern";respCSP=cspPol;respCORS=[];resploc=None;respRedSec=sl}) in
      (rpResp)
      ))
  else if s_equal #urisl #PublicVal ip "badip.com" then
  (
    let sl = (SecretVal [rpori;badipori]) in
    let sid = (genSecret sl) in
    let state = (genSecret sl) in
    (
      (let logsession:loginSession = [(badipori, sid, state)] in
      rpLS := List.append logsession (!rpLS));
      (* Badip replaces the response headers as per its convenience - the badip can modify the origin-index also  *)
      let usl = (SecretVal [rpori;ipori]) in
      let respuri = ({c_origin=ipori;c_uname="";c_pwd="";c_path=["authEP"];c_querystring=[("client_id",(getRPClientID ipori));("redirect_uri","https://rp.com:443/codeEP/");("origin","https://rp.com/");("csrftoken",declassify #sl (getSecret state))];c_fragment=""}) in
      let rpREP = classify #PublicVal (curi_to_hstring respuri) usl in
      let rpResp = ActResponse usl ({resptype="default";respcode=301;respurl=[]; resphead=[("Set-Cookie", (mk_headerval (classify #PublicVal (declassify #sl (getSecret sid)) usl)));("Location", (mk_headerval rpREP))]; respbody=(emptyString usl);resptrail=[];respHTTPS="modern";respCSP=cspPol;respCORS=[];resploc=None;respRedSec=usl}) in
      (* print_string ("IP is not ip.com:" ^ (curi_to_hstring respuri) ^ "\n" );  *)
      (rpResp)
      ))
  else (print_string ("IP is not ip.com:" ^ (declassify ip) ^ "\n" ); (defErrResponse))

val getRPLoginIPAuth : r:request -> ML (ret:retReqResp{isValidRetResp r ret})
let getRPLoginIPAuth r = (let resp = rpLoginIPAuth r in RetResponse resp)

(* Compact authcode resend method for the RP *)
(* the indexed origins defeat the idp mix-up attack here - as for the request with code to be sent, the index must include badipori *)
val rpReqCodeEP : request -> ML (option (r:request{notForbiddenHeaderfieldInReqHeader (Request?.rf r).reqhead}))
let rpReqCodeEP r =
  let urisl = s_getReqURISecLevel r in
  let ruri = mk_uri (s_getRequestURI #urisl r) in (* get the request url *)
  let qs = getQS #urisl (ruri) in
  let token = mk_secretval (getQSVal #urisl qs "csrftoken") in
  let ip = getIPLogin !rpLS token in (* determine the IP based on the state-token *)
  let urisl = SecretVal [ip] in
  let code = declassify (getQSVal #(URI?.usl ruri) qs "authcode") in
  let cid = (getRPClientID ip) in
  (match (getCDSecret (!rpCD) ip) with
  | None -> (* get client data secret is none for the ip -- may be the client_secret was not established *)
	   (
	   (* The port is required to pass isOriginSec in StringFunctions *)
	   let rturi = ({c_origin=ip;c_uname=emptyString urisl;c_pwd=emptyString urisl;c_path=[(classify #PublicVal "tokenEP" urisl)];c_querystring=[((classify #PublicVal "client_id" urisl), classify #PublicVal cid urisl);((classify #PublicVal "redirect_uri" urisl),(classify #PublicVal "https://rp.com:443/codeEP/" urisl));((classify #PublicVal "authcode" urisl),(classify #PublicVal code urisl))];c_fragment=emptyString urisl}) in
	   let nreq = Request urisl ({reqm = "POST"; requrl = [(mk_uri rturi)]; reqhead = []; reqo = mk_aorigin ((URI?.u (CWindow?.cwloc rpsw)).c_origin); reqw = (Some rpsw); reqinit = ""; reqtype = ""; reqdest = ""; reqtarget = None; reqredirect = 0; reqredmode = "follow"; reqref = (Client rpsw); reqrefPolicy = RP_OriginWhenCO; reqnonce = ""; reqparser = ""; requnsafe = false; reqpreflight = false; reqsync = false; reqmode = NoCORS; reqtaint = "basic"; reqcredm = "omit"; reqcredflag = false; reqbody = (emptyString urisl); corsflag = false; corspfflag = false; authflag = false; recflag = false}) in
	   let (r, req, tw, nb) = navigateWindow !rpb rpsw rpsw (RequestResource nreq) "other" in
	   rpb := nb; (req)
	   )
  | Some sec ->
	   (
	   secretOriginLemma ip (Secret?.s sec);
	   let cs = classify #(Secret?.s sec) (getSecret #(Secret?.s sec) (sec)) urisl in
	   let rturi = ({c_origin=ip;c_uname=emptyString urisl;c_pwd=emptyString urisl;c_path=[(classify #PublicVal "tokenEP" urisl)];c_querystring=[((classify #PublicVal "client_id" urisl), classify #PublicVal cid urisl);((classify #PublicVal "redirect_uri" urisl),(classify #PublicVal "https://rp.com:443/codeEP/" urisl));((classify #PublicVal "authcode" urisl),(classify #PublicVal code urisl));((classify #PublicVal "client_secret" urisl),cs)];c_fragment=emptyString urisl}) in
	   let nreq = Request urisl ({reqm = "POST"; requrl = [(mk_uri rturi)]; reqhead = []; reqo = mk_aorigin ((URI?.u (CWindow?.cwloc rpsw)).c_origin); reqw = (Some rpsw); reqinit = ""; reqtype = ""; reqdest = ""; reqtarget = None; reqredirect = 0; reqredmode = "follow"; reqref = (Client rpsw); reqrefPolicy = RP_OriginWhenCO; reqnonce = ""; reqparser = ""; requnsafe = false; reqpreflight = false; reqsync = false; reqmode = NoCORS; reqtaint = "basic"; reqcredm = "omit"; reqcredflag = false; reqbody = (emptyString urisl); corsflag = false; corspfflag = false; authflag = false; recflag = false}) in
	   let (r, req, tw, nb) = navigateWindow !rpb rpsw rpsw (RequestResource nreq) "other" in
	   rpb := nb; (req)
	   ))

val getRPReqCodeEP : r:request -> ML (ret:retReqResp{isValidRetResp r ret})
let getRPReqCodeEP r = (match rpReqCodeEP r with | None -> RetResponse defErrResponse | Some req -> RetRequest req)

(* val rpReqCodeEP : uri -> ML actResponse  *)
(* let rpReqCodeEP ruri = *)
(*   let urisl = URI?.usl ruri in  *)
(*   let qs = getQS (ruri) in *)
(*   let token = mk_secretval (getQSVal #urisl qs "csrftoken") in *)
(*   let ip = getIPLogin !rpLS token in *)
(*   if (ip = ipori) && (urisl = SecretVal [rpori;ipori]) then ( (\* the request must have come from IP to RP and indexed by RPORI and IPORI to allow further communication *\) *)
(*      ( *)
(* 	let code = getQSVal #urisl qs "authcode" in  *)
(* 	let cid = (getRPClientID ipori) in  *)
(*      match (getCDSecret !rpCD ipori) with *)
(*        | None -> (\* get client data secret is none for the ip -- may be the client_secret was not established *\) *)
(* 	    ( *)
(* 	    (\* The port is required to pass isOriginSec in ExtFunctionsImpl *\) *)
(* 	    let rturi = ({c_origin=ipori;c_uname=emptyString urisl;c_pwd=emptyString urisl;c_path=[(classify #PublicVal "tokenEP" urisl)];c_querystring=[((classify #PublicVal "client_id" urisl), classify #PublicVal cid urisl);((classify #PublicVal "redirect_uri" urisl),(classify #PublicVal "https://rp.com:443/codeEP/" urisl));((classify #PublicVal "authcode" urisl),code)];c_fragment=emptyString urisl}) in *)
(* 	    let nreq = Request urisl ({reqm = "POST"; requrl = [(mk_uri rturi)]; reqhead = []; reqo = mk_aorigin ((URI?.u (CWindow?.cwloc rpsw)).c_origin); reqw = (Some rpsw); reqinit = ""; reqtype = ""; reqdest = ""; reqtarget = None; reqredirect = 0; reqredmode = "follow"; reqref = (Client rpsw); reqrefPolicy = RP_OriginWhenCO; reqnonce = ""; reqparser = ""; requnsafe = false; reqpreflight = false; reqsync = false; reqmode = NoCORS; reqtaint = "basic"; reqcredm = "omit"; reqcredflag = false; reqbody = (emptyString urisl); corsflag = false; corspfflag = false; authflag = false; recflag = false}) in *)
(* 	    let (r, tw, nb) = navigateWindow !rpb rpsw rpsw (RequestResource nreq) "other" in 	     *)
(* 	    rpb := nb *)
(* 	    ) *)
(*        | Some sec -> *)
(* 	    ( *)
(* 	    let cs = classify #(Secret?.s sec) (getSecret #(Secret?.s sec) (sec)) urisl in  *)
(* 	    (\* The port is required to pass isOriginSec in ExtFunctionsImpl *\) *)
(* 	    let rturi = ({c_origin=ipori;c_uname=emptyString urisl;c_pwd=emptyString urisl;c_path=[(classify #PublicVal "tokenEP" urisl)];c_querystring=[((classify #PublicVal "client_id" urisl), classify #PublicVal cid urisl);((classify #PublicVal "redirect_uri" urisl),(classify #PublicVal "https://rp.com:443/codeEP/" urisl));((classify #PublicVal "authcode" urisl),code);((classify #PublicVal "client_secret" urisl),cs)];c_fragment=emptyString urisl}) in *)
(* 	    let nreq = Request urisl ({reqm = "POST"; requrl = [(mk_uri rturi)]; reqhead = []; reqo = mk_aorigin ((URI?.u (CWindow?.cwloc rpsw)).c_origin); reqw = (Some rpsw); reqinit = ""; reqtype = ""; reqdest = ""; reqtarget = None; reqredirect = 0; reqredmode = "follow"; reqref = (Client rpsw); reqrefPolicy = RP_OriginWhenCO; reqnonce = ""; reqparser = ""; requnsafe = false; reqpreflight = false; reqsync = false; reqmode = NoCORS; reqtaint = "basic"; reqcredm = "omit"; reqcredflag = false; reqbody = (emptyString urisl); corsflag = false; corspfflag = false; authflag = false; recflag = false}) in *)
(* 	    let (r, tw, nb) = navigateWindow !rpb rpsw rpsw (RequestResource nreq) "other" in 	     *)
(* 	    rpb := nb *)
(* 	    )); *)
(* 	    defResponse) *)
(*   (\* the indexed origins  defeat the idp mix-up attack here - as for the request with code to be sent, the index must include badipori *\)	     *)
(*   else if (ip = badipori) && (urisl = SecretVal [rpori;badipori]) then (\* the request must have come from BadIP to RP - no client data secret is none for the RP *\) *)
(* 	  (( *)
(* 	    let code = (getQSVal #urisl qs "authcode") in  *)
(* 	    let cid = (getRPClientID badipori) in  *)
(* 	    let rturi = ({c_origin=badipori;c_uname=emptyString urisl;c_pwd=emptyString urisl;c_path=[(classify #PublicVal "tokenEP" urisl)];c_querystring=[((classify #PublicVal "client_id" urisl), classify #PublicVal cid urisl);((classify #PublicVal "redirect_uri" urisl),(classify #PublicVal "https://rp.com:443/codeEP/" urisl));((classify #PublicVal "authcode" urisl),code)];c_fragment=emptyString urisl}) in *)
(* 	    let nreq = Request urisl ({reqm = "POST"; requrl = [(mk_uri rturi)]; reqhead = []; reqo = mk_aorigin ((URI?.u (CWindow?.cwloc rpsw)).c_origin); reqw = (Some rpsw); reqinit = ""; reqtype = ""; reqdest = ""; reqtarget = None; reqredirect = 0; reqredmode = "follow"; reqref = (Client rpsw); reqrefPolicy = RP_OriginWhenCO; reqnonce = ""; reqparser = ""; requnsafe = false; reqpreflight = false; reqsync = false; reqmode = NoCORS; reqtaint = "basic"; reqcredm = "omit"; reqcredflag = false; reqbody = (emptyString urisl); corsflag = false; corspfflag = false; authflag = false; recflag = false}) in *)
(* 	    let (r, tw, nb) = navigateWindow !rpb rpsw rpsw (RequestResource nreq) "other" in 	     *)
(* 	    rpb := nb *)
(* 	    ); *)
(* 	    defResponse) *)
(*   else defResponse *)

(* For different requests, return different responses *)
val rpReqResp : r:request -> ML (ret:retReqResp{isValidRetResp r ret})
let rpReqResp r =
    let urisl = s_getReqURISecLevel r in
    let ruri = mk_uri (s_getRequestURI #urisl r) in (* get the request url *)
    if checkRPReq r && (getPort ruri) = (Some 443) then (* Only accept secure connections (HTTPS) *)
    (
    if (checkEP r "login-ipauth") then (* if the end-point is login with IP *)
      getRPLoginIPAuth r
    else if (checkEP r "codeEP") then (* auth-code end-point *)
      getRPReqCodeEP r
    else (RetResponse defErrResponse)
    )
    else (print_string ("IP is not ip.com:" ^ (declassify (curi_to_hstring (s_getRequestURI #urisl r))) ^ "\n" ); (RetResponse defErrResponse))

