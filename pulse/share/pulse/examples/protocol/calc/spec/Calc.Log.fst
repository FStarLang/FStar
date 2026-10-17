module Calc.Log

(**
  Ghost log with monotonic references for calc sample.
  Demonstrates wire-to-semantic correspondence pattern with full byte parsing.
**)

module L = FStar.List.Tot
open FStar.List.Tot
open Calc.Spec
module Seq = FStar.Seq
module R = FStar.ReflexiveTransitiveClosure
open Calc.Wire
open FStar.Preorder

type bytes = Seq.seq FStar.UInt8.t

(** Parse sequence of request bytes (each request is 5 bytes) **)
let rec parse_requests (b: bytes) 
  : Tot (list request) (decreases (Seq.length b))
  =
  if Seq.length b < 5 then []
  else
    let msg_bytes = Seq.slice b 0 5 in
    let rest = Seq.slice b 5 (Seq.length b) in
    match parse_request msg_bytes with
    | None -> []  // Stop at first unparseable message
    | Some req -> req :: parse_requests rest

(** Serialize sequence of responses (each response is 5 bytes) **)
let rec serialize_responses (resps: list response) 
  : Tot bytes (decreases resps)
  =
  match resps with
  | [] -> Seq.empty
  | r :: rs -> Seq.append (serialize_response r) (serialize_responses rs)

(** All messages in bytes parse successfully **)
let rec all_parse (b: bytes{Seq.length b % 5 == 0}) 
  : Tot prop (decreases (Seq.length b))
  =
  if Seq.length b < 5 then True
  else
    let msg_bytes = Seq.slice b 0 5 in
    let rest = Seq.slice b 5 (Seq.length b) in
    Some? (parse_request msg_bytes) /\ all_parse rest

(** Ghost log tracks wire-to-semantic state **)
noeq
type calc_log = {
  input_bytes: bytes;           // All request bytes received
  output_bytes: bytes;          // All response bytes sent  
  requests: list request;       // Parsed requests
  responses: list response;     // Responses sent
  current_state: calc_stack;    // Current stack state
}

(** Initial log **)
let initial_log : calc_log = {
  input_bytes = Seq.empty;
  output_bytes = Seq.empty;
  requests = [];
  responses = [];
  current_state = [];
}

(** 
  Log consistency: Full wire-to-semantic correspondence
  
  1. input_bytes parses to requests
  2. output_bytes serializes responses  
  3. current_state matches running requests through state machine
  4. responses match state machine outputs
**)
let log_consistent (log:calc_log) : prop =
  let (state, resps) = run [] log.requests in
  // Byte length invariants (checked first so they refine the types)
  Seq.length log.input_bytes % 5 == 0 /\
  Seq.length log.output_bytes % 5 == 0 /\
  // All input bytes parse successfully
  all_parse log.input_bytes /\
  // Semantic consistency
  log.current_state == state /\
  log.responses == resps /\
  // Wire-to-semantic correspondence
  parse_requests log.input_bytes == log.requests /\
  serialize_responses log.responses `Seq.equal` log.output_bytes

(** Update log for Push operation **)
let step_log_push (value: int) (req_bytes: bytes{Seq.length req_bytes == 5})
                  (resp_bytes: bytes{Seq.length resp_bytes == 5})
                  (log: calc_log)
  : calc_log =
  let req = Push value in
  let (new_state, response) = step log.current_state req in
  {
    input_bytes = Seq.append log.input_bytes req_bytes;
    output_bytes = Seq.append log.output_bytes resp_bytes;
    requests = log.requests @ [req];
    responses = log.responses @ [response];
    current_state = new_state;
  }

(** Update log for Peek operation **)
let step_log_peek (req_bytes: bytes{Seq.length req_bytes == 5})
                  (resp_bytes: bytes{Seq.length resp_bytes == 5})
                  (log: calc_log)
  : calc_log =
  let req = Peek in
  let (new_state, response) = step log.current_state req in
  {
    input_bytes = Seq.append log.input_bytes req_bytes;
    output_bytes = Seq.append log.output_bytes resp_bytes;
    requests = log.requests @ [req];
    responses = log.responses @ [response];
    current_state = new_state;
  }

(** Update log for Add operation **)
let step_log_add (req_bytes: bytes{Seq.length req_bytes == 5})
                 (resp_bytes: bytes{Seq.length resp_bytes == 5})
                 (log: calc_log)
  : calc_log =
  let req = Add in
  let (new_state, response) = step log.current_state req in
  {
    input_bytes = Seq.append log.input_bytes req_bytes;
    output_bytes = Seq.append log.output_bytes resp_bytes;
    requests = log.requests @ [req];
    responses = log.responses @ [response];
    current_state = new_state;
  }

(** Update log for Sub operation **)
let step_log_sub (req_bytes: bytes{Seq.length req_bytes == 5})
                 (resp_bytes: bytes{Seq.length resp_bytes == 5})
                 (log: calc_log)
  : calc_log =
  let req = Sub in
  let (new_state, response) = step log.current_state req in
  {
    input_bytes = Seq.append log.input_bytes req_bytes;
    output_bytes = Seq.append log.output_bytes resp_bytes;
    requests = log.requests @ [req];
    responses = log.responses @ [response];
    current_state = new_state;
  }

(** Update log for Mul operation **)
let step_log_mul (req_bytes: bytes{Seq.length req_bytes == 5})
                 (resp_bytes: bytes{Seq.length resp_bytes == 5})
                 (log: calc_log)
  : calc_log =
  let req = Mul in
  let (new_state, response) = step log.current_state req in
  {
    input_bytes = Seq.append log.input_bytes req_bytes;
    output_bytes = Seq.append log.output_bytes resp_bytes;
    requests = log.requests @ [req];
    responses = log.responses @ [response];
    current_state = new_state;
  }

(** Update log for Div operation **)
let step_log_div (req_bytes: bytes{Seq.length req_bytes == 5})
                 (resp_bytes: bytes{Seq.length resp_bytes == 5})
                 (log: calc_log)
  : calc_log =
  let req = Div in
  let (new_state, response) = step log.current_state req in
  {
    input_bytes = Seq.append log.input_bytes req_bytes;
    output_bytes = Seq.append log.output_bytes resp_bytes;
    requests = log.requests @ [req];
    responses = log.responses @ [response];
    current_state = new_state;
  }

(** Define single-step evolution relation **)
let log_single_step : R.binrel calc_log =
  fun log0 log1 ->
    // Push
    (exists (value:int) (req_bytes:bytes{Seq.length req_bytes == 5})
                        (resp_bytes:bytes{Seq.length resp_bytes == 5}).
       log1 == step_log_push value req_bytes resp_bytes log0) \/
    // Peek
    (exists (req_bytes:bytes{Seq.length req_bytes == 5})
            (resp_bytes:bytes{Seq.length resp_bytes == 5}).
       log1 == step_log_peek req_bytes resp_bytes log0) \/
    // Add
    (exists (req_bytes:bytes{Seq.length req_bytes == 5})
            (resp_bytes:bytes{Seq.length resp_bytes == 5}).
       log1 == step_log_add req_bytes resp_bytes log0) \/
    // Sub
    (exists (req_bytes:bytes{Seq.length req_bytes == 5})
            (resp_bytes:bytes{Seq.length resp_bytes == 5}).
       log1 == step_log_sub req_bytes resp_bytes log0) \/
    // Mul
    (exists (req_bytes:bytes{Seq.length req_bytes == 5})
            (resp_bytes:bytes{Seq.length resp_bytes == 5}).
       log1 == step_log_mul req_bytes resp_bytes log0) \/
    // Div
    (exists (req_bytes:bytes{Seq.length req_bytes == 5})
            (resp_bytes:bytes{Seq.length resp_bytes == 5}).
       log1 == step_log_div req_bytes resp_bytes log0)

(** Preorder for monotonic ghost reference **)
let log_evolves : preorder calc_log = R.closure log_single_step

(** log_evolves is reflexive **)
val lemma_log_evolves_refl (log: calc_log) : Lemma (log_evolves log log)
let lemma_log_evolves_refl log = ()

(** Helper lemma: extending run preserves consistency **)
val lemma_run_extend
  (s:calc_stack)
  (reqs:list request)
  (req:request)
  (s':calc_stack)
  (resps:list response)
  (s'':calc_stack)
  (resp:response)
  : Lemma
      (requires 
        run s reqs == (s', resps) /\
        step s' req == (s'', resp))
      (ensures
        run s (reqs @ [req]) == (s'', resps @ [resp]))
      (decreases reqs)

let rec lemma_run_extend s reqs req s' resps s'' resp =
  match reqs with
  | [] -> ()
  | r :: rest ->
      let (s1, resp1) = step s r in
      let (s2, resps2) = run s1 rest in
      lemma_run_extend s1 rest req s2 resps2 s'' resp

(** Helper lemma: serialize_responses produces bytes of length 5*n **)
val lemma_serialize_responses_length
  (resps: list response)
  : Lemma (Seq.length (serialize_responses resps) == 5 * L.length resps)

let rec lemma_serialize_responses_length resps =
  match resps with
  | [] -> ()
  | r :: rest ->
      lemma_serialize_responses_length rest

(** Helper lemma: parse_requests on a single 5-byte message **)
val lemma_parse_requests_single
  (bytes: bytes{Seq.length bytes == 5})
  (req: request)
  : Lemma 
      (requires parse_request bytes == Some req)
      (ensures parse_requests bytes == [req])

let lemma_parse_requests_single bytes req = ()

(** Helper lemma: serializing a list appends the serializations **)
val lemma_serialize_responses_append
  (resps1: list response)
  (resps2: list response)
  : Lemma (serialize_responses (resps1 @ resps2) `Seq.equal`
           Seq.append (serialize_responses resps1) (serialize_responses resps2))

let rec lemma_serialize_responses_append resps1 resps2 =
  match resps1 with
  | [] -> ()
  | r :: rest ->
      lemma_serialize_responses_append rest resps2
      // serialize_responses ((r :: rest) @ resps2)
      // = serialize_response r ++ serialize_responses (rest @ resps2)
      // = serialize_response r ++ (serialize_responses rest ++ serialize_responses resps2)
      // = (serialize_response r ++ serialize_responses rest) ++ serialize_responses resps2
      // = serialize_responses (r :: rest) ++ serialize_responses resps2
      // Append is associative by definition on sequences

(** Helper lemma: serialize_responses of a singleton list **)
val lemma_serialize_responses_single
  (resp: response)
  : Lemma (serialize_responses [resp] `Seq.equal` serialize_response resp)

let lemma_serialize_responses_single resp = ()

(** Helper: slicing the beginning of an append **)
val lemma_slice_append_prefix
  (s1: bytes{Seq.length s1 >= 5})
  (s2: bytes)
  : Lemma (Seq.slice (Seq.append s1 s2) 0 5 `Seq.equal` Seq.slice s1 0 5)

let lemma_slice_append_prefix s1 s2 =
  Seq.lemma_index_app1 s1 s2 0;
  Seq.lemma_index_app1 s1 s2 1;
  Seq.lemma_index_app1 s1 s2 2;
  Seq.lemma_index_app1 s1 s2 3;
  Seq.lemma_index_app1 s1 s2 4

(** Helper: appending a parseable 5-byte message extends the parse list **)
val lemma_parse_requests_append_one
  (bytes1: bytes{Seq.length bytes1 % 5 == 0})
  (msg_bytes: bytes{Seq.length msg_bytes == 5})
  (req: request)
  : Lemma 
      (requires parse_request msg_bytes == Some req /\ all_parse bytes1)
      (ensures parse_requests (Seq.append bytes1 msg_bytes) == parse_requests bytes1 @ [req])
      (decreases (Seq.length bytes1))

#push-options "--z3rlimit 30 --fuel 2 --ifuel 1"
let rec lemma_parse_requests_append_one bytes1 msg_bytes req =
  if Seq.length bytes1 < 5 then ()
  else begin
    lemma_slice_append_prefix bytes1 msg_bytes;
    FStar.Seq.Properties.lemma_slice_first_in_append bytes1 msg_bytes 5;
    let first_msg = Seq.slice bytes1 0 5 in
    let rest = Seq.slice bytes1 5 (Seq.length bytes1) in
    // all_parse bytes1 means: Some? (parse_request first_msg) /\ all_parse rest
    match parse_request first_msg with
    | Some r -> lemma_parse_requests_append_one rest msg_bytes req
  end
#pop-options

(** Helper: appending a parseable message preserves all_parse **)
val lemma_all_parse_append
  (b1: bytes{Seq.length b1 % 5 == 0})
  (b2: bytes{Seq.length b2 == 5})
  : Lemma (requires all_parse b1 /\ Some? (parse_request b2))
          (ensures all_parse (Seq.append b1 b2))
          (decreases (Seq.length b1))

#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"
let rec lemma_all_parse_append b1 b2 =
  if Seq.length b1 < 5 then ()
  else begin
    let msg1 = Seq.slice b1 0 5 in
    let rest1 = Seq.slice b1 5 (Seq.length b1) in
    lemma_slice_append_prefix b1 b2;
    FStar.Seq.Properties.lemma_slice_first_in_append b1 b2 5;
    lemma_all_parse_append rest1 b2
  end
#pop-options

(* The six `step_log_*_consistent` lemmas below are structurally identical and
   had all been left at F*'s default rlimit of 5, which they only just fit under
   Z3 4.13.3.  Give the whole family the same budget as the neighbouring lemmas
   in this file (20) rather than leaving them on a knife edge. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"

(** Lemma: step_log_push preserves consistency **)
val lemma_step_log_push_consistent
  (value: int)
  (req_bytes: bytes{Seq.length req_bytes == 5})
  (resp_bytes: bytes{Seq.length resp_bytes == 5})
  (log: calc_log{log_consistent log})
  : Lemma 
      (requires 
        parse_request req_bytes == Some (Push value) /\
        serialize_response (snd (step log.current_state (Push value))) `Seq.equal` resp_bytes)
      (ensures log_consistent (step_log_push value req_bytes resp_bytes log))

let lemma_step_log_push_consistent value req_bytes resp_bytes log =
  let new_log = step_log_push value req_bytes resp_bytes log in
  let req = Push value in
  let (new_state, spec_resp) = step log.current_state req in
  
  // Get existing state and responses
  let (old_state, old_resps) = run [] log.requests in
  assert (old_state == log.current_state);
  assert (old_resps == log.responses);
  
  // Prove extended run (semantic consistency)
  lemma_run_extend [] log.requests req old_state old_resps new_state spec_resp;
  assert (run [] (log.requests @ [req]) == (new_state, old_resps @ [spec_resp]));
  
  // Prove wire-to-semantic correspondence for requests
  lemma_parse_requests_single req_bytes req;
  lemma_parse_requests_append_one log.input_bytes req_bytes req;
  assert (parse_requests new_log.input_bytes == new_log.requests);
  
  // Length invariants (needed for all_parse refinement).  State the append
  // lengths explicitly rather than leaving them to the `% 5` obligations.
  Seq.lemma_len_append log.input_bytes req_bytes;
  Seq.lemma_len_append log.output_bytes resp_bytes;
  assert (Seq.length new_log.input_bytes % 5 == 0);
  assert (Seq.length new_log.output_bytes % 5 == 0);
  
  // Prove all_parse for new log
  lemma_all_parse_append log.input_bytes req_bytes;
  assert (all_parse new_log.input_bytes);
  
  // Prove wire-to-semantic correspondence for responses
  lemma_serialize_responses_single spec_resp;
  lemma_serialize_responses_append log.responses [spec_resp];
  assert (serialize_responses new_log.responses `Seq.equal` new_log.output_bytes)

(** Initial log is consistent **)
val lemma_initial_log_consistent : unit -> Lemma (log_consistent initial_log)
let lemma_initial_log_consistent () = ()

(** Lemma: step_log_push produces evolution **)
val lemma_step_log_push_evolves
  (value: int)
  (req_bytes: bytes{Seq.length req_bytes == 5})
  (resp_bytes: bytes{Seq.length resp_bytes == 5})
  (log: calc_log)
  : Lemma (log_single_step log (step_log_push value req_bytes resp_bytes log))

let lemma_step_log_push_evolves value req_bytes resp_bytes log = ()

(** Lemma: step_log_push preserves wire-to-semantic correspondence **)
val lemma_step_log_push_properties
  (value: int)
  (req_bytes: bytes{Seq.length req_bytes == 5})
  (resp_bytes: bytes{Seq.length resp_bytes == 5})
  (log: calc_log{log_consistent log})
  : Lemma 
      (requires
        parse_request req_bytes == Some (Push value) /\
        serialize_response (snd (step log.current_state (Push value))) `Seq.equal` resp_bytes)
      (ensures (
        let log1 = step_log_push value req_bytes resp_bytes log in
        log1.input_bytes `Seq.equal` Seq.append log.input_bytes req_bytes /\
        log1.output_bytes `Seq.equal` Seq.append log.output_bytes resp_bytes /\
        log_consistent log1
      ))

let lemma_step_log_push_properties value req_bytes resp_bytes log =
  lemma_step_log_push_consistent value req_bytes resp_bytes log

(** Lemma: step_log_peek preserves consistency **)
val lemma_step_log_peek_consistent
  (req_bytes: bytes{Seq.length req_bytes == 5})
  (resp_bytes: bytes{Seq.length resp_bytes == 5})
  (log: calc_log{log_consistent log})
  : Lemma
      (requires
        parse_request req_bytes == Some Peek /\
        serialize_response (snd (step log.current_state Peek)) `Seq.equal` resp_bytes)
      (ensures log_consistent (step_log_peek req_bytes resp_bytes log))

let lemma_step_log_peek_consistent req_bytes resp_bytes log =
  let new_log = step_log_peek req_bytes resp_bytes log in
  let req = Peek in
  let (new_state, spec_resp) = step log.current_state req in
  
  // Get existing state and responses
  let (old_state, old_resps) = run [] log.requests in
  assert (old_state == log.current_state);
  assert (old_resps == log.responses);
  
  // Prove extended run (semantic consistency)
  lemma_run_extend [] log.requests req old_state old_resps new_state spec_resp;
  
  // Prove wire-to-semantic correspondence for requests
  lemma_parse_requests_single req_bytes req;
  lemma_parse_requests_append_one log.input_bytes req_bytes req;
  
  // Length invariants (needed for all_parse refinement).  State the append
  // lengths explicitly rather than leaving them to the `% 5` obligations.
  Seq.lemma_len_append log.input_bytes req_bytes;
  Seq.lemma_len_append log.output_bytes resp_bytes;
  assert (Seq.length new_log.input_bytes % 5 == 0);
  assert (Seq.length new_log.output_bytes % 5 == 0);
  
  // Prove all_parse for new log
  lemma_all_parse_append log.input_bytes req_bytes;
  assert (all_parse new_log.input_bytes);
  
  // Prove wire-to-semantic correspondence for responses
  lemma_serialize_responses_single spec_resp;
  lemma_serialize_responses_append log.responses [spec_resp]

(** Lemma: step_log_peek produces evolution **)
val lemma_step_log_peek_evolves
  (req_bytes: bytes{Seq.length req_bytes == 5})
  (resp_bytes: bytes{Seq.length resp_bytes == 5})
  (log: calc_log)
  : Lemma (log_single_step log (step_log_peek req_bytes resp_bytes log))

let lemma_step_log_peek_evolves req_bytes resp_bytes log = ()

(** Lemma: step_log_add preserves consistency **)
val lemma_step_log_add_consistent
  (req_bytes: bytes{Seq.length req_bytes == 5})
  (resp_bytes: bytes{Seq.length resp_bytes == 5})
  (log: calc_log{log_consistent log})
  : Lemma
      (requires
        parse_request req_bytes == Some Add /\
        serialize_response (snd (step log.current_state Add)) `Seq.equal` resp_bytes)
      (ensures log_consistent (step_log_add req_bytes resp_bytes log))

let lemma_step_log_add_consistent req_bytes resp_bytes log =
  let new_log = step_log_add req_bytes resp_bytes log in
  let req = Add in
  let (new_state, spec_resp) = step log.current_state req in
  
  let (old_state, old_resps) = run [] log.requests in
  lemma_run_extend [] log.requests req old_state old_resps new_state spec_resp;
  
  lemma_parse_requests_single req_bytes req;
  lemma_parse_requests_append_one log.input_bytes req_bytes req;
  
  // Length invariants (needed for all_parse refinement).  State the append
  // lengths explicitly rather than leaving them to the `% 5` obligations.
  Seq.lemma_len_append log.input_bytes req_bytes;
  Seq.lemma_len_append log.output_bytes resp_bytes;
  assert (Seq.length new_log.input_bytes % 5 == 0);
  assert (Seq.length new_log.output_bytes % 5 == 0);
  
  // Prove all_parse for new log
  lemma_all_parse_append log.input_bytes req_bytes;
  assert (all_parse new_log.input_bytes);
  
  lemma_serialize_responses_single spec_resp;
  lemma_serialize_responses_append log.responses [spec_resp]

val lemma_step_log_add_evolves
  (req_bytes: bytes{Seq.length req_bytes == 5})
  (resp_bytes: bytes{Seq.length resp_bytes == 5})
  (log: calc_log)
  : Lemma (log_single_step log (step_log_add req_bytes resp_bytes log))

let lemma_step_log_add_evolves req_bytes resp_bytes log = ()

(** Lemmas for Sub/Mul/Div - same pattern as Add **)
val lemma_step_log_sub_consistent
  (req_bytes: bytes{Seq.length req_bytes == 5})
  (resp_bytes: bytes{Seq.length resp_bytes == 5})
  (log: calc_log{log_consistent log})
  : Lemma
      (requires
        parse_request req_bytes == Some Sub /\
        serialize_response (snd (step log.current_state Sub)) `Seq.equal` resp_bytes)
      (ensures log_consistent (step_log_sub req_bytes resp_bytes log))

let lemma_step_log_sub_consistent req_bytes resp_bytes log =
  let new_log = step_log_sub req_bytes resp_bytes log in
  let (new_state, spec_resp) = step log.current_state Sub in
  let (old_state, old_resps) = run [] log.requests in
  lemma_run_extend [] log.requests Sub old_state old_resps new_state spec_resp;
  
  lemma_parse_requests_single req_bytes Sub;
  lemma_parse_requests_append_one log.input_bytes req_bytes Sub;
  
  // Length invariants (needed for all_parse refinement).  State the append
  // lengths explicitly rather than leaving them to the `% 5` obligations.
  Seq.lemma_len_append log.input_bytes req_bytes;
  Seq.lemma_len_append log.output_bytes resp_bytes;
  assert (Seq.length new_log.input_bytes % 5 == 0);
  assert (Seq.length new_log.output_bytes % 5 == 0);
  
  // Prove all_parse for new log
  lemma_all_parse_append log.input_bytes req_bytes;
  assert (all_parse new_log.input_bytes);
  
  lemma_serialize_responses_single spec_resp;
  lemma_serialize_responses_append log.responses [spec_resp]

val lemma_step_log_sub_evolves
  (req_bytes: bytes{Seq.length req_bytes == 5})
  (resp_bytes: bytes{Seq.length resp_bytes == 5})
  (log: calc_log)
  : Lemma (log_single_step log (step_log_sub req_bytes resp_bytes log))

let lemma_step_log_sub_evolves req_bytes resp_bytes log = ()

val lemma_step_log_mul_consistent
  (req_bytes: bytes{Seq.length req_bytes == 5})
  (resp_bytes: bytes{Seq.length resp_bytes == 5})
  (log: calc_log{log_consistent log})
  : Lemma
      (requires
        parse_request req_bytes == Some Mul /\
        serialize_response (snd (step log.current_state Mul)) `Seq.equal` resp_bytes)
      (ensures log_consistent (step_log_mul req_bytes resp_bytes log))

let lemma_step_log_mul_consistent req_bytes resp_bytes log =
  let new_log = step_log_mul req_bytes resp_bytes log in
  let (new_state, spec_resp) = step log.current_state Mul in
  let (old_state, old_resps) = run [] log.requests in
  lemma_run_extend [] log.requests Mul old_state old_resps new_state spec_resp;
  
  lemma_parse_requests_single req_bytes Mul;
  lemma_parse_requests_append_one log.input_bytes req_bytes Mul;
  
  // Length invariants (needed for all_parse refinement).  State the append
  // lengths explicitly rather than leaving them to the `% 5` obligations.
  Seq.lemma_len_append log.input_bytes req_bytes;
  Seq.lemma_len_append log.output_bytes resp_bytes;
  assert (Seq.length new_log.input_bytes % 5 == 0);
  assert (Seq.length new_log.output_bytes % 5 == 0);
  
  // Prove all_parse for new log
  lemma_all_parse_append log.input_bytes req_bytes;
  assert (all_parse new_log.input_bytes);
  
  lemma_serialize_responses_single spec_resp;
  lemma_serialize_responses_append log.responses [spec_resp]

val lemma_step_log_mul_evolves
  (req_bytes: bytes{Seq.length req_bytes == 5})
  (resp_bytes: bytes{Seq.length resp_bytes == 5})
  (log: calc_log)
  : Lemma (log_single_step log (step_log_mul req_bytes resp_bytes log))

let lemma_step_log_mul_evolves req_bytes resp_bytes log = ()

val lemma_step_log_div_consistent
  (req_bytes: bytes{Seq.length req_bytes == 5})
  (resp_bytes: bytes{Seq.length resp_bytes == 5})
  (log: calc_log{log_consistent log})
  : Lemma
      (requires
        parse_request req_bytes == Some Div /\
        serialize_response (snd (step log.current_state Div)) `Seq.equal` resp_bytes)
      (ensures log_consistent (step_log_div req_bytes resp_bytes log))

let lemma_step_log_div_consistent req_bytes resp_bytes log =
  let new_log = step_log_div req_bytes resp_bytes log in
  let (new_state, spec_resp) = step log.current_state Div in
  let (old_state, old_resps) = run [] log.requests in
  lemma_run_extend [] log.requests Div old_state old_resps new_state spec_resp;
  
  lemma_parse_requests_single req_bytes Div;
  lemma_parse_requests_append_one log.input_bytes req_bytes Div;
  
  // Length invariants (needed for all_parse refinement).  State the append
  // lengths explicitly rather than leaving them to the `% 5` obligations.
  Seq.lemma_len_append log.input_bytes req_bytes;
  Seq.lemma_len_append log.output_bytes resp_bytes;
  assert (Seq.length new_log.input_bytes % 5 == 0);
  assert (Seq.length new_log.output_bytes % 5 == 0);
  
  // Prove all_parse for new log
  lemma_all_parse_append log.input_bytes req_bytes;
  assert (all_parse new_log.input_bytes);
  
  lemma_serialize_responses_single spec_resp;
  lemma_serialize_responses_append log.responses [spec_resp]

val lemma_step_log_div_evolves
  (req_bytes: bytes{Seq.length req_bytes == 5})
  (resp_bytes: bytes{Seq.length resp_bytes == 5})
  (log: calc_log)
  : Lemma (log_single_step log (step_log_div req_bytes resp_bytes log))

let lemma_step_log_div_evolves req_bytes resp_bytes log = ()
#pop-options
