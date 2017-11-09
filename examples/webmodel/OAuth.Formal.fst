module OAuth.Formal

type http_request
type http_response
type param
type header
type body
type uri
type origin = string
type uid = string


// We will check by typing that a nonce of type "nonce idx"
// can never be sent to principals other than idx.uid, idx.rp, idx.ip
type index 
assume val public_index: index
assume val can_send: i:index -> i':index -> GTot Type
assume val includes: i:index -> o:origin -> GTot Type

assume val index2 : o1:origin -> o2:origin -> i:index{includes i o1 /\ includes i o2}

type nonce (idx:index)
assume val eq_nonce: #(idx:index) -> nonce idx -> nonce idx -> bool

assume val param_index: param -> GTot index
type pub_param = p:param{param_index p == public_index}

assume val header_index: header -> GTot index
type pub_header = h:header{header_index h == public_index}

assume val body_index: body -> GTot index
type pub_body = b:body{body_index b == public_index}

assume val can_send_public: i:index -> Lemma 
	   (requires True)
	   (ensures (fun _ -> can_send public_index i))
	   [SMTPat (can_send public_index i)]
	   
assume val mk_uri: origin -> path:string -> list param  -> uri
assume val uri_origin: uri -> origin
assume val add_parameters: u:uri -> list param -> u':uri{uri_origin u == uri_origin u'}

assume val request_path: http_request -> string
assume val request_method: http_request -> string
assume val request_parameters: http_request -> (list param)
assume val request_origin_header: http_request -> string
assume val request_cookie_header: #idx:index -> http_request -> nonce idx
assume val request_body: http_request -> body


assume val mk_referrer_policy_header: string -> header
assume val mk_set_cookie_header: #idx:index -> nonce idx -> header
assume val mk_authorization_header: #idx:index -> string -> nonce idx -> header

assume val mk_request: #req_idx:index -> 
		       method:string -> 
		       request_uri:uri{includes req_idx (uri_origin request_uri)}  -> 
		       list (h:header{can_send (header_index h) req_idx}) -> 
		       b:body{body_index b == req_idx} -> 
		       http_request
assume val mk_response: list header -> body -> http_response
assume val mk_redirect_response: uri -> list header -> http_response

assume val response_body: http_response -> body


assume val mk_body: #req_idx:index -> list (p:param{can_send (param_index p) req_idx}) -> b:body{body_index b == req_idx}
assume val get_body: body -> list param

assume val mk_origin: string -> origin
assume val get_origin: origin -> string

 
type server_state 
unfold type server 'a = server_state -> ('a * server_state)
unfold let bind (f:server 'a) (g: 'a -> server 'b) = 
  (fun s0 -> let (r,s1) = (f s0) in g r s1)
unfold let return (x:'a) : server 'a =
  fun s0 -> x,s0

type session
assume val create_session: #idx:index -> server (nonce idx)
assume val mk_nonce: #idx:index -> server (nonce idx)

// OAuth Specific
type idp_record
assume val read_idps: origin -> server (list idp_record) 
assume val get_idp_origin: idp_record -> origin
assume val get_idp_record: o:origin -> list idp_record -> option (ir:idp_record{get_idp_origin ir == o})
assume val get_idp_auth_endpoint_uri: ir:idp_record -> u:uri{uri_origin u == get_idp_origin ir}
assume val get_idp_token_endpoint_uri: ir:idp_record -> u:uri{uri_origin u == get_idp_origin ir}
assume val get_idp_introspection_endpoint_uri: ir:idp_record -> u:uri{uri_origin u == get_idp_origin ir}
assume val get_client_id: idp_record -> string
assume val get_client_secret: #idx:index -> idp_record -> option (nonce idx)

assume val response_type_param: string -> pub_param
assume val client_id_param: string -> pub_param
assume val idp_param: origin -> pub_param
assume val redirect_uri_param: uri -> pub_param
assume val script_param: string -> pub_param
assume val grant_type_param: string -> pub_param

assume val state_param: #idx:index -> nonce idx -> p:param{param_index p == idx}
assume val authorization_code_param: #idx:index -> nonce idx -> p:param{param_index p == idx}
assume val access_token_param: #idx:index -> nonce idx -> p:param{param_index p == idx}

assume val get_idp_param: (list param) -> option origin
assume val get_client_id_param: (list param) -> option string
assume val get_state_param: #idx:index -> (list param) -> option (nonce idx)
assume val get_mode_param: (list param) -> option string // echoes back response_type
assume val get_code_param: #idx:index -> (list param) -> option (nonce idx)
assume val get_access_token_param: #idx:index -> (list param) -> option (nonce idx)

(*
assume val get_idp_code_params: #idx:index -> (list param) -> Pure (option (origin * nonce idx))
					   (requires True)
					   (ensures (fun x -> match x with 
							   | None -> True
							   | Some (idp,code) -> 
*)
assume val set_rp_session: #idx:index -> #idx':index -> loginSessionId:nonce idx -> idp:origin -> s:nonce idx' -> m:string -> redir:uri -> server unit
assume val get_rp_session: #idx:index -> #idx':index -> loginSessionId:nonce idx -> server (option (idp:origin * s:nonce idx' * m:string * redir:uri))

assume val set_rp_request_state: #idx:index -> #idx':index -> request_id:nonce idx -> mode:string -> idp:origin -> req:nonce idx' -> server unit
assume val get_rp_request_state: #idx:index -> #idx':index -> request_id:nonce idx -> server (option (mode:string * idp:origin * req:nonce idx'))

noeq type http_message = | Req : #idx:index -> id:nonce idx -> http_request -> http_message | Resp: #idx:index -> id:nonce idx -> http_response -> http_message

#reset-options "--z3rlimit 100"
//val rp_http_server: rp_origin:origin -> msg:http_message -> server (option (msg':http_message{
//						match (msg,msg') with 
//						| Req i _, Resp i' _ -> i == i'
//						| _, _ -> True}))


let rp_http_server (rp_origin:origin) (msg:http_message) : server (option http_message) = 
 match msg with
 | Req #idx id req -> 
  let path = request_path req in
  if path = "/" then
    let headers = [mk_referrer_policy_header "origin"] in 
    let script_ = script_param "script_rp_index" in
    can_send_public idx;
    assert (can_send (param_index script_) idx);
    let resp = Resp #idx id (mk_response headers (mk_body #idx [script_])) in
    return (Some resp)
  else if path = "/startInteractiveLogin" then
    if (request_method req = "POST" &&
        request_origin_header req = get_origin rp_origin)
	 //may need extra checks for HTTPS 
    then (
       match get_idp_param (get_body (request_body req)) with
       | None -> return None 
       | Some idp -> 
	 idps <-- read_idps rp_origin ;
	 match get_idp_record idp idps with
	 | None -> return None
	 | Some ir -> 
	   (state <-- mk_nonce #idx ;
	     let auth_uri = get_idp_auth_endpoint_uri ir in
	     let client_id = get_client_id ir in
	     let redirect_uri = mk_uri rp_origin "/redirectionEndpoint" [idp_param idp] in
   	     let auth_uri = add_parameters auth_uri [response_type_param "code"; 
						    client_id_param client_id; 
						    state_param state; 
						    redirect_uri_param redirect_uri] in
	     session_id <-- create_session #idx ;
	     set_rp_session session_id idp state "code" redirect_uri ;;
	     let resp = mk_redirect_response auth_uri [mk_set_cookie_header session_id; mk_referrer_policy_header "origin"] in
	     let resp = Resp #idx id resp in 
	     return (Some resp)))
	     else return None
    else if path = "/redirectionEndpoint" then
      let session_id = request_cookie_header req in
      session_or_none <-- get_rp_session #idx #idx session_id ;
      match session_or_none with
      | None -> return None
      | Some (idp, state, mode, redir) -> 
	idps <-- read_idps rp_origin ;
	match get_idp_record idp idps with
	| None -> return None
	| Some ir -> 
	       let client_id = get_client_id ir in
	       let req_params = request_parameters req in
	       match (get_client_id_param req_params, 
		     get_idp_param req_params, 
		     get_state_param #idx req_params,
		     get_mode_param req_params) with
               | Some cid, Some idp', Some state', Some mode ->
		      if (cid = client_id && idp' = idp && eq_nonce state state' && mode = "code") then  
			      // be careful of side-channel leaks in state = state'
	              match (get_code_param #idx req_params) with
		      | None -> return None
		      | Some code -> 
                             match (get_client_secret #idx ir) with
			     | None -> return None
			     | Some sec -> 
				    let token_index = index2 idp rp_origin in
				    let token_request = mk_request #token_index "POST" 
							(get_idp_token_endpoint_uri ir)
							[mk_authorization_header client_id sec] 
							(mk_body #token_index 
								 [grant_type_param "authorization_code";
							          authorization_code_param code;
								  redirect_uri_param redir]) in
				    request_id <-- mk_nonce ;
				    set_rp_request_state request_id "code" idp id ;;
			            return (Some (Req #idx request_id token_request))
    
		      else return None   
	       | _,_,_,_ -> return None
    else return None
 | Resp #idx id resp -> // process IP's response and process API response
     session_or_none <-- get_rp_request_state id ;
     match session_or_none with
     | None -> return None
     | Some (mode,idp,prev) -> 
        if mode = "code" then 
        let resp_params = get_body (response_body resp) in
	match get_access_token_param #idx resp_params with
	| None -> return None
	| Some token -> 
	  idps <-- read_idps rp_origin ;
	  match get_idp_record idp idps with
	  | None -> return None
	  | Some ir -> 
		 let intros_uri = get_idp_introspection_endpoint_uri ir in
		 let intros_uri = add_parameters intros_uri [access_token_param token] in
		 request_id <-- mk_nonce ;
   		 set_rp_request_state request_id "introspect" idp prev ;;
		 let request_idx = index2 idp rp_origin in
		 assert (includes request_idx idp);
		 assert (includes request_idx (uri_origin intros_uri));
		 let request = mk_request #request_idx "GET" intros_uri [] (mk_body #request_idx []) in
		 return (Some (Req #idx request_id request))
        else if mode = "introspect" then
	     /// We may get back the userid and/or a protected resource and/or client_id here
	     /// For authentication, we need to check these values, but not for authorization
	     let headers = [mk_referrer_policy_header "origin"] in 
	     let script_ = script_param "script_rp_index" in
	     can_send_public idx;
	     assert (can_send (param_index script_) idx);
	     return (Some (Resp #idx prev (mk_response headers (mk_body #idx [script_]))))
	else return None 


 
