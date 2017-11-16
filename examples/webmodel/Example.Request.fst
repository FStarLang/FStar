module Example.Request

open FStar.IO
open Web.Origin
open Web.URI
open Secret.SecString
open Browser.AuxiliaryDatatypes
open Browser.Datatypes
open Browser.Model.Interface
open Network.Interface

let example_origin:torigin = TOrigin "https" ["example";"com"] (Some 443) None

(* Create a default function for the browser with window *)
let initial_browser = (init_browser)
let (current_id, old_browser) = (set_unique_id initial_browser)

let document_url = {c_origin=example_origin;
		   c_uname=emptyString (SecretVal [example_origin]);
		   c_pwd=emptyString (SecretVal [example_origin]);
		   c_path=[];
		   c_querystring=[];
		   c_fragment=emptyString (SecretVal [example_origin])}
		   
let document_uri = mk_uri document_url
let current_document = {dloc=document_uri;
		       dref=blank_uri;
		       dori=(mk_aorigin document_url.c_origin);
		       dHTTPS="modern";
		       drefPol=RP_NoReferrer;
		       dCSP=[];
		       dsbox=[];}      

let current_window:window = 
	let current_window_history = HistEntry (URI?.usl document_uri) (URI?.u document_uri) get_time current_document current_id in 
	({winid=current_id;
	  wname="";
	  wloc=document_uri;
	  wframes=[];
	  wopener=None;
	  wparent=None;
	  whist={hlhe=[current_window_history];hcur=1};
	  wdoc=(current_document);
	  wsbox=[];})
	
let current_browser = ({old_browser with windows=(win_to_cowin current_window)::(old_browser.windows)})

// Browser initialized with a window "running a script" from https://example.com

let request_origin = TOrigin "https" ["another_example";"com"] (Some 443) None
let request_uri = mk_uri ({c_origin=request_origin;
			 c_uname=emptyString (PublicVal);
			 c_pwd=emptyString (PublicVal);
			 c_path=["login"];
			 c_querystring=[];
			 c_fragment=emptyString (PublicVal)})

let cross_origin_current_window = (win_to_cowin current_window)

let server_function (r:browserRequest) = 
  let ruri = (AuxiliaryFunctions.firstElement (BRequest?.rf r).requrl) in 
  if (getPort ruri) = (Some 443) then 
  (
	if (checkEP r "login") then 
	     (ActResponse (PublicVal) ({respori=request_origin; (* Bookkeeping information - origin of the server - response originates here *)
				      respdest=initial_browser.bid; (* Bookkeeping information - origin (id) of the client that requested *)
				      respRedSec=PublicVal; (* Bookkeeping information - secrecy level of the redirect, if any *)
				      resptype="default";
				      respcode=302;
				      respurl=[];
				      resphead=[("Location", (mk_headerval #PublicVal ("https://redirect.example.com:443")))];
				      respbody=(emptyString (PublicVal));
				      resptrail=[];
				      respHTTPS="modern";
				      respCSP=[];
				      respCORS=[];
				      resploc=None;}))
	else if (checkEP r "/") then 
	     (ActResponse (PublicVal) ({respori=request_origin;
				      respdest=initial_browser.bid;
				      resptype="default";
				      respcode=200;
				      respurl=[];
				      resphead=[];
				      respbody=(emptyString (PublicVal));
				      resptrail=[];
				      respHTTPS="modern";
				      respCSP=[];
				      respCORS=[];
				      resploc=None;
				      respRedSec=PublicVal}))
	else (defErrResponse request_origin (BRequest?.rf r).reqb)
  )
  else (defErrResponse request_origin (BRequest?.rf r).reqb)



let main =
  let (request_result, sent_request, new_window, new_browser) = 
		       (* navigateWindow current_browser cross_origin_current_window cross_origin_current_window  *)
		       (* 	 (RequestResource (default_browser_request current_browser cross_origin_current_window (request_uri))) "other" in *)
		       form_submission current_browser current_window "" "GET" request_uri [] in 
  match new_browser.conn with (*the response arrives on the connection - assume connection available here*)
  | [] -> print_string ("Empty F*!\n")
  | hd::_ -> 
	match sent_request with 
	| None -> print_string ("Error! No request found \n")
	| Some s_request ->
	          let response_from_server = server_function s_request in 
	          let (response_result, _, new_window1, new_browser1) = 
					processResponse new_browser (getConn hd).connect s_request response_from_server in
					( match response_result with
					| (Error e) -> print_string ("Error! " ^ e ^ "\n")
					| (Success s) -> print_string ("Success! " ^ s ^ "\n"))


