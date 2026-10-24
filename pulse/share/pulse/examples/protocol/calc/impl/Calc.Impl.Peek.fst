module Calc.Impl.Peek

#lang-pulse

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Cast = FStar.Int.Cast
module L = FStar.List.Tot

open Pulse.Lib.Pervasives
module Vec = Pulse.Lib.Vec
module B = Pulse.Lib.Box
module MR = Pulse.Lib.MonotonicGhostRef

open Calc.Spec
open Calc.Wire
open Calc.Wire.Lemmas
open Calc.Log
open Calc.Impl.Types

fn write_error_response (resp_buf: Vec.vec U8.t)
  requires Vec.pts_to resp_buf 'bytes ** pure (Seq.length 'bytes == 5)
  ensures exists* (resp_bytes1: bytes).
    Vec.pts_to resp_buf resp_bytes1 **
    pure (
      Seq.length resp_bytes1 == 5 /\
      Seq.index resp_bytes1 0 == 2uy /\
      (forall (i:nat{i > 0 /\ i < 5}). Seq.index resp_bytes1 i == 0uy)
    )
{
  Vec.op_Dot_Lparen_Rparen_Less_Minus resp_buf 0sz 2uy;
  Vec.op_Dot_Lparen_Rparen_Less_Minus resp_buf 1sz 0uy;
  Vec.op_Dot_Lparen_Rparen_Less_Minus resp_buf 2sz 0uy;
  Vec.op_Dot_Lparen_Rparen_Less_Minus resp_buf 3sz 0uy;
  Vec.op_Dot_Lparen_Rparen_Less_Minus resp_buf 4sz 0uy
}

(** Write Result response (tag 1, then big-endian value) **)
#push-options "--z3rlimit 30"
fn write_result_response (resp_buf: Vec.vec U8.t) (value: U32.t)
  requires Vec.pts_to resp_buf 'bytes ** pure (Seq.length 'bytes == 5)
  ensures exists* (resp_bytes1: bytes).
    Vec.pts_to resp_buf resp_bytes1 **
    pure (
      Seq.length resp_bytes1 == 5 /\
      Seq.index resp_bytes1 0 == 1uy /\
      Calc.Wire.be_to_n (Seq.slice resp_bytes1 1 5) == U32.v value
    )
{
  Vec.op_Dot_Lparen_Rparen_Less_Minus resp_buf 0sz 1uy;
  with rb1. _;
  Vec.op_Dot_Lparen_Rparen_Less_Minus resp_buf 1sz (Cast.uint32_to_uint8 (U32.shift_right value 24ul));
  with rb2. _;
  Vec.op_Dot_Lparen_Rparen_Less_Minus resp_buf 2sz (Cast.uint32_to_uint8 (U32.shift_right value 16ul));
  with rb3. _;
  Vec.op_Dot_Lparen_Rparen_Less_Minus resp_buf 3sz (Cast.uint32_to_uint8 (U32.shift_right value 8ul));
  with rb4. _;
  Vec.op_Dot_Lparen_Rparen_Less_Minus resp_buf 4sz (Cast.uint32_to_uint8 value);
  with resp_bytes1. _;
  
  // Assert the concrete byte values
  assert (pure (
    Seq.index resp_bytes1 0 == 1uy /\
    Seq.index resp_bytes1 1 == Cast.uint32_to_uint8 (U32.shift_right value 24ul) /\
    Seq.index resp_bytes1 2 == Cast.uint32_to_uint8 (U32.shift_right value 16ul) /\
    Seq.index resp_bytes1 3 == Cast.uint32_to_uint8 (U32.shift_right value 8ul) /\
    Seq.index resp_bytes1 4 == Cast.uint32_to_uint8 value
  ));
  
  // The big-endian arithmetic is discharged entirely by this pure lemma.  Do
  // not inline it: leaving `be_to_n (Seq.slice _ 1 5) == U32.v value` to the
  // Pulse VC makes Z3 4.15.3 diverge without ever consuming rlimit.
  lemma_write_result_be_to_n value resp_bytes1;
  // Pin the decoded value so the `ensures` existential can be discharged by
  // matching hypotheses rather than by re-running the arithmetic.
  assert (pure (Seq.length resp_bytes1 == 5));
  assert (pure (be_to_n (Seq.slice resp_bytes1 1 5) == U32.v value))
}
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
fn process_peek
  (srv: server_state)
  (req_buf: Vec.vec U8.t)
  (resp_buf: Vec.vec U8.t)
  (#log0: erased calc_log)
  (#req_bytes: erased bytes{Seq.length req_bytes == 5})
requires
  server_exactly srv log0 **
  Vec.pts_to req_buf req_bytes **
  Vec.pts_to resp_buf 'resp_bytes **
  pure (
    parse_request req_bytes == Some Peek /\
    Seq.length 'resp_bytes == 5
  )
ensures exists* (resp_bytes1: bytes{Seq.length resp_bytes1 == 5}) (log1: calc_log).
  server_exactly srv log1 **
  Vec.pts_to req_buf req_bytes **
  Vec.pts_to resp_buf resp_bytes1 **
  pure (
    log1 == step_log_peek req_bytes resp_bytes1 log0 /\
    log1.input_bytes `Seq.equal` Seq.append log0.input_bytes req_bytes /\
    log1.output_bytes `Seq.equal` Seq.append log0.output_bytes resp_bytes1 /\
    serialize_response (snd (step log0.current_state Peek)) `Seq.equal` resp_bytes1
  )
{
  unfold (server_exactly srv log0);
  with sb size_seq. _;
  let csz = Vec.op_Dot_Lparen_Rparen srv.size 0sz;

  if SZ.gt csz 0sz {
    // Peek success: read top element
    let top = Vec.op_Dot_Lparen_Rparen srv.stack (SZ.sub csz 1sz);
    write_result_response resp_buf top;
    with resp_bytes1. _;
    
    assert (pure (
      (step_log_peek req_bytes resp_bytes1 log0).current_state ==
      log0.current_state
    ));
    
    // Establish serialize_response correspondence for Result
    Calc.Wire.lemma_serialize_result_bytes (U32.v top) resp_bytes1;
    assert (pure (snd (step log0.current_state Peek) == Result (L.hd log0.current_state)));
    assert (pure (L.hd log0.current_state == U32.v top));
    assert (pure (serialize_response (snd (step log0.current_state Peek)) `Seq.equal` resp_bytes1));
    
    lemma_step_log_peek_consistent req_bytes resp_bytes1 log0;
    lemma_step_log_peek_evolves req_bytes resp_bytes1 log0;
    MR.update srv.ghost_log (step_log_peek req_bytes resp_bytes1 log0);
    fold (server_exactly srv (step_log_peek req_bytes resp_bytes1 log0))
  } else {
    // Peek error: empty stack
    write_error_response resp_buf;
    with resp_bytes1. _;
    
    assert (pure (
      (step_log_peek req_bytes resp_bytes1 log0).current_state ==
      log0.current_state
    ));
    
    // Establish serialize_response correspondence for Error
    Calc.Wire.lemma_serialize_error_bytes resp_bytes1;
    assert (pure (snd (step log0.current_state Peek) == Error));
    assert (pure (serialize_response (snd (step log0.current_state Peek)) `Seq.equal` resp_bytes1));
    
    lemma_step_log_peek_consistent req_bytes resp_bytes1 log0;
    lemma_step_log_peek_evolves req_bytes resp_bytes1 log0;
    MR.update srv.ghost_log (step_log_peek req_bytes resp_bytes1 log0);
    fold (server_exactly srv (step_log_peek req_bytes resp_bytes1 log0))
  }
}
#pop-options
