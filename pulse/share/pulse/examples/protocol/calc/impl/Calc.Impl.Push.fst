module Calc.Impl.Push

#lang-pulse

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module SZ = FStar.SizeT
module Seq = FStar.Seq

open Pulse.Lib.Pervasives
module Vec = Pulse.Lib.Vec
module B = Pulse.Lib.Box
module MR = Pulse.Lib.MonotonicGhostRef

open Calc.Spec
open Calc.Wire
open Calc.Log
open Calc.Impl.Types

(** Write Ok response (5 zero bytes) **)
fn write_ok_response (resp_buf: Vec.vec U8.t)
  requires Vec.pts_to resp_buf 'bytes ** pure (Seq.length 'bytes == 5)
  ensures exists* (resp_bytes1: bytes).
    Vec.pts_to resp_buf resp_bytes1 **
    pure (
      Seq.length resp_bytes1 == 5 /\ 
      Seq.index resp_bytes1 0 == 0uy /\
      Seq.index resp_bytes1 1 == 0uy /\
      Seq.index resp_bytes1 2 == 0uy /\
      Seq.index resp_bytes1 3 == 0uy /\
      Seq.index resp_bytes1 4 == 0uy
    )
{
  Vec.op_Dot_Lparen_Rparen_Less_Minus resp_buf 0sz 0uy;
  Vec.op_Dot_Lparen_Rparen_Less_Minus resp_buf 1sz 0uy;
  Vec.op_Dot_Lparen_Rparen_Less_Minus resp_buf 2sz 0uy;
  Vec.op_Dot_Lparen_Rparen_Less_Minus resp_buf 3sz 0uy;
  Vec.op_Dot_Lparen_Rparen_Less_Minus resp_buf 4sz 0uy
}

(** Write Error response (tag 2, then zeros) **)
fn write_error_response (resp_buf: Vec.vec U8.t)
  requires Vec.pts_to resp_buf 'bytes ** pure (Seq.length 'bytes == 5)
  ensures exists* (resp_bytes1: bytes).
    Vec.pts_to resp_buf resp_bytes1 **
    pure (
      Seq.length resp_bytes1 == 5 /\ 
      Seq.index resp_bytes1 0 == 2uy /\
      Seq.index resp_bytes1 1 == 0uy /\
      Seq.index resp_bytes1 2 == 0uy /\
      Seq.index resp_bytes1 3 == 0uy /\
      Seq.index resp_bytes1 4 == 0uy
    )
{
  Vec.op_Dot_Lparen_Rparen_Less_Minus resp_buf 0sz 2uy;
  Vec.op_Dot_Lparen_Rparen_Less_Minus resp_buf 1sz 0uy;
  Vec.op_Dot_Lparen_Rparen_Less_Minus resp_buf 2sz 0uy;
  Vec.op_Dot_Lparen_Rparen_Less_Minus resp_buf 3sz 0uy;
  Vec.op_Dot_Lparen_Rparen_Less_Minus resp_buf 4sz 0uy
}

(** 
  Process Push request.
  
  Precondition: server state is valid, buffers contain valid bytes
  Postcondition: 
    - log1 == step_log_push value req_bytes resp_bytes1 log0
    - log1.input_bytes == log0.input_bytes @ req_bytes
    - log1.output_bytes == log0.output_bytes @ resp_bytes1
**)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
fn process_push
  (srv: server_state)
  (value: U32.t)
  (req_buf: Vec.vec U8.t)
  (resp_buf: Vec.vec U8.t)
  (#log0: erased calc_log)
  (#req_bytes: erased bytes{Seq.length req_bytes == 5})
requires
  server_exactly srv log0 **
  Vec.pts_to req_buf req_bytes **
  Vec.pts_to resp_buf 'resp_bytes **
  pure (
    parse_request req_bytes == Some (Push (U32.v value)) /\
    Seq.length 'resp_bytes == 5
  )
ensures exists* (resp_bytes1: bytes{Seq.length resp_bytes1 == 5}) (log1: calc_log).
  server_exactly srv log1 **
  Vec.pts_to req_buf req_bytes **
  Vec.pts_to resp_buf resp_bytes1 **
  pure (
    log1 == step_log_push (U32.v value) req_bytes resp_bytes1 log0 /\
    log1.input_bytes `Seq.equal` Seq.append log0.input_bytes req_bytes /\
    log1.output_bytes `Seq.equal` Seq.append log0.output_bytes resp_bytes1 /\
    serialize_response (snd (step log0.current_state (Push (U32.v value)))) `Seq.equal` resp_bytes1
  )
{
  let v_int : int = U32.v value;
  
  unfold (server_exactly srv log0);
  with sb size_seq. _;
  let csz = Vec.op_Dot_Lparen_Rparen srv.size 0sz;

  if SZ.lt csz 10sz {
    // Push success: stack not full
    Vec.op_Dot_Lparen_Rparen_Less_Minus srv.stack csz value;
    Vec.op_Dot_Lparen_Rparen_Less_Minus srv.size 0sz (SZ.add csz 1sz);
    write_ok_response resp_buf;
    with resp_bytes1. _;
    
    // Establish serialize_response correspondence (write_ok_response ensures all bytes are 0)
    Calc.Wire.lemma_serialize_ok_bytes resp_bytes1;
    assert (pure (snd (step log0.current_state (Push v_int)) == Ok));
    assert (pure (serialize_response (snd (step log0.current_state (Push v_int))) `Seq.equal` resp_bytes1));
    
    assert (pure (
      (step_log_push v_int req_bytes resp_bytes1 log0).current_state ==
      v_int :: log0.current_state
    ));
    
    lemma_step_log_push_consistent v_int req_bytes resp_bytes1 log0;
    lemma_step_log_push_evolves v_int req_bytes resp_bytes1 log0;
    MR.update srv.ghost_log (step_log_push v_int req_bytes resp_bytes1 log0);
    fold (server_exactly srv (step_log_push v_int req_bytes resp_bytes1 log0))
  } else {
    // Push error: stack full
    write_error_response resp_buf;
    with resp_bytes1. _;
    
    // Establish serialize_response correspondence (write_error_response ensures all bytes match Error)
    Calc.Wire.lemma_serialize_error_bytes resp_bytes1;
    assert (pure (snd (step log0.current_state (Push v_int)) == Error));
    assert (pure (serialize_response (snd (step log0.current_state (Push v_int))) `Seq.equal` resp_bytes1));
    
    assert (pure (
      (step_log_push v_int req_bytes resp_bytes1 log0).current_state ==
      log0.current_state
    ));
    
    lemma_step_log_push_consistent v_int req_bytes resp_bytes1 log0;
    lemma_step_log_push_evolves v_int req_bytes resp_bytes1 log0;
    MR.update srv.ghost_log (step_log_push v_int req_bytes resp_bytes1 log0);
    fold (server_exactly srv (step_log_push v_int req_bytes resp_bytes1 log0))
  }
}
#pop-options
