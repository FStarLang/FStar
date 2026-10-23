module Calc.Server

#lang-pulse

(**
  Modular Pulse implementation with separate handler modules.
  Demonstrates clean dispatcher architecture with wire-to-semantic proof.
**)

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module SZ = FStar.SizeT
module Seq = FStar.Seq
module SM = Pulse.Lib.Protocol.StateMachine

open Pulse.Lib.Pervasives
module Vec = Pulse.Lib.Vec
module B = Pulse.Lib.Box
module MR = Pulse.Lib.MonotonicGhostRef

open Calc.Wire
open Calc.Wire.Lemmas
open Calc.Log
open Calc.Impl.Types
module CalcP = Calc.Protocol
open Calc.Impl.Parser

// Import all handlers
module Push = Calc.Impl.Push
module Peek = Calc.Impl.Peek
module Add = Calc.Impl.Add
module Sub = Calc.Impl.Sub
module Mul = Calc.Impl.Mul
module Div = Calc.Impl.Div

(** Maximum stack size **)
let max_stack_size : SZ.t = 10sz

(** Create new server with empty stack and initial ghost log **)
fn new_server ()
  requires emp
  returns srv: server_state
  ensures
    server_exactly srv initial_log **
    pure (Vec.is_full_vec srv.stack /\ Vec.is_full_vec srv.size)
{
  lemma_initial_log_consistent ();
  let stack = Vec.alloc 0ul 10sz;
  let size_vec = Vec.alloc 0sz 1sz;  // Single-element vector for size
  let ghost_log = MR.alloc #_ #log_evolves initial_log;
  let srv = {
    stack = stack;
    size = size_vec;
    ghost_log = ghost_log;
  };
  
  // Rewrite predicates to match srv fields
  with stack_bytes. rewrite (Vec.pts_to stack stack_bytes) as (Vec.pts_to srv.stack stack_bytes);
  with size_seq. rewrite (Vec.pts_to size_vec size_seq) as (Vec.pts_to srv.size size_seq);
  rewrite (MR.pts_to ghost_log #1.0R initial_log) as (MR.pts_to srv.ghost_log #1.0R initial_log);
  
  fold (server_exactly srv initial_log);
  assert (pure (Vec.is_full_vec srv.stack));
  assert (pure (Vec.is_full_vec srv.size));
  srv
}

(** Lemma: parse_request b <> None => first byte tag is in [0..5] **)
let lemma_valid_tag (b: bytes{Seq.length b == 5 /\ parse_request b <> None})
  : Lemma (U8.v (Seq.index b 0) < 6)
  = ()

(**
  process_request: modular dispatcher.
  
  Architecture:
  1. Parse tag from request buffer
  2. For Push: parse value, dispatch to Push.process_push
  3. For other ops: dispatch to appropriate handler module
  
  Postcondition (strengthened):
  - log1 contains exact step_log_* transformation
  - log1.input_bytes == log0.input_bytes @ req_bytes
  - log1.output_bytes == log0.output_bytes @ resp_bytes1
  - log_single_step log0 log1 (witnesses progression)
  - log_consistent log1
**)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 200"
fn process_request
  (srv: server_state)
  (req_buf: Vec.vec U8.t)
  (resp_buf: Vec.vec U8.t)
  (#log0: erased calc_log)
requires
  server_exactly srv log0 **
  Vec.pts_to req_buf 'req_bytes **
  Vec.pts_to resp_buf 'resp_bytes **
  pure (
    Seq.length 'req_bytes == 5 /\
    Seq.length 'resp_bytes == 5 /\
    parse_request 'req_bytes <> None
  )
ensures exists* (resp_bytes1: bytes) (log1: calc_log).
  server_exactly srv log1 **
  Vec.pts_to req_buf 'req_bytes **
  Vec.pts_to resp_buf resp_bytes1 **
  pure (
    Seq.length 'req_bytes == 5 /\
    parse_request 'req_bytes <> None /\
    log_single_step log0 log1 /\
    log1.input_bytes `Seq.equal` Seq.append log0.input_bytes 'req_bytes /\
    log1.output_bytes `Seq.equal` Seq.append log0.output_bytes resp_bytes1 /\
    CalcP.calc_frame_network_step_ok log0 'req_bytes log1 resp_bytes1
  )
{
  lemma_valid_tag 'req_bytes;
  let tag = parse_tag req_buf;
  assert (pure (U8.v tag < 6));
  
  if U8.eq tag 0uy {
    // PUSH - parse value (postcondition proves be_to_n correspondence)
    let value = parse_push_value req_buf;
    
    // Connect unrefined to be_to_n and parse_request
    Calc.Wire.Lemmas.lemma_be_to_n_equiv (Seq.slice 'req_bytes 1 5);
    assert (pure (U32.v value == be_to_n (Seq.slice 'req_bytes 1 5)));
    assert (pure (parse_request 'req_bytes == Some (Push (U32.v value))));
    
    Push.process_push srv value req_buf resp_buf;
    // Postcondition from Push.process_push gives us log1 == step_log_push ...
    // Need to show log_single_step log0 log1
    with resp_bytes1 log1. _;
    assert (pure (CalcP.calc_frame_network_step_ok log0 'req_bytes log1 resp_bytes1));
    assert (pure (log_single_step log0 log1))
  } else if U8.eq tag 1uy {
    // PEEK
    assert (pure (parse_request 'req_bytes == Some Peek));
    Peek.process_peek srv req_buf resp_buf;
    with resp_bytes1 log1. _;
    assert (pure (CalcP.calc_frame_network_step_ok log0 'req_bytes log1 resp_bytes1));
    assert (pure (log_single_step log0 log1))
  } else if U8.eq tag 2uy {
    // ADD
    assert (pure (parse_request 'req_bytes == Some Add));
    Add.process_add srv req_buf resp_buf;
    with resp_bytes1 log1. _;
    assert (pure (CalcP.calc_frame_network_step_ok log0 'req_bytes log1 resp_bytes1));
    assert (pure (log_single_step log0 log1))
  } else if U8.eq tag 3uy {
    // SUB
    assert (pure (parse_request 'req_bytes == Some Sub));
    Sub.process_sub srv req_buf resp_buf;
    with resp_bytes1 log1. _;
    assert (pure (CalcP.calc_frame_network_step_ok log0 'req_bytes log1 resp_bytes1));
    assert (pure (log_single_step log0 log1))
  } else if U8.eq tag 4uy {
    // MUL
    assert (pure (parse_request 'req_bytes == Some Mul));
    Mul.process_mul srv req_buf resp_buf;
    with resp_bytes1 log1. _;
    assert (pure (CalcP.calc_frame_network_step_ok log0 'req_bytes log1 resp_bytes1));
    assert (pure (log_single_step log0 log1))
  } else if U8.eq tag 5uy {
    // DIV
    assert (pure (parse_request 'req_bytes == Some Div));
    Div.process_div srv req_buf resp_buf;
    with resp_bytes1 log1. _;
    assert (pure (CalcP.calc_frame_network_step_ok log0 'req_bytes log1 resp_bytes1));
    assert (pure (log_single_step log0 log1))
  } else {
    // Unreachable: tag < 6 /\ tag != 0..5 → False
    assert (pure False)
  }
}
#pop-options
