module Calc.Server.Socket

#lang-pulse

open Pulse.Lib.Pervasives

module Seq = FStar.Seq
module SZ = FStar.SizeT
module TCP = Pulse.Lib.TCP
module U16 = FStar.UInt16
module U8 = FStar.UInt8
module Vec = Pulse.Lib.Vec
module MR = Pulse.Lib.MonotonicGhostRef
module R = Pulse.Lib.Reference

module CalcCP = Calc.Server.CanonicalProtocol

open Calc.Log
open Calc.Wire
open Calc.Impl.Types

inline_for_extraction
fn free_server_state
  (srv:server_state)
requires
  exists* log.
    server_exactly srv log **
    pure (Vec.is_full_vec srv.stack /\ Vec.is_full_vec srv.size)
ensures emp
{
  with log.
    assert (
      server_exactly srv log **
      pure (Vec.is_full_vec srv.stack /\ Vec.is_full_vec srv.size));
  unfold (server_exactly srv log);
  with stack_bytes size_seq. _;
  Vec.free srv.stack;
  Vec.free srv.size;
  drop_ (MR.pts_to srv.ghost_log #1.0R log)
}

#push-options "--z3rlimit 100"
inline_for_extraction
fn run_connection_loop
  (srv:server_state)
  (ch:TCP.channel)
  (req:Vec.vec U8.t)
  (resp:Vec.vec U8.t)
  (fuel:SZ.t)
requires
  exists* received sent log req_bytes resp_bytes.
    server_exactly srv log **
    TCP.is_channel ch received sent **
    Vec.pts_to req req_bytes **
    Vec.pts_to resp resp_bytes **
    pure (
      Seq.length req_bytes == 5 /\
      Seq.length resp_bytes == 5 /\
      Vec.length req == 5 /\
      Vec.length resp == 5 /\
      Vec.is_full_vec req /\
      Vec.is_full_vec resp /\
      Vec.is_full_vec srv.stack /\
      Vec.is_full_vec srv.size)
ensures
  exists* (received1:Ghost.erased TCP.bytes)
          (sent1:Ghost.erased TCP.bytes)
          (log1:Ghost.erased calc_log)
          (req_bytes1:TCP.bytes)
          (resp_bytes1:TCP.bytes).
    server_exactly srv (Ghost.reveal log1) **
    TCP.is_channel ch (Ghost.reveal received1) (Ghost.reveal sent1) **
    Vec.pts_to req req_bytes1 **
    Vec.pts_to resp resp_bytes1 **
    pure (
      Seq.length req_bytes1 == 5 /\
      Seq.length resp_bytes1 == 5 /\
      Vec.length req == 5 /\
      Vec.length resp == 5 /\
      Vec.is_full_vec req /\
      Vec.is_full_vec resp /\
      Vec.is_full_vec srv.stack /\
      Vec.is_full_vec srv.size)
{
      let mut remaining = fuel;
      let mut running = true;
      while (
        let keep = R.read running;
        let rem = R.read remaining;
        keep && not (rem = 0sz)
      )
        invariant live remaining
        invariant live running
        invariant exists* received_loop sent_loop log_loop req_bytes_loop resp_bytes_loop.
          server_exactly srv (Ghost.reveal log_loop) **
          TCP.is_channel ch (Ghost.reveal received_loop) (Ghost.reveal sent_loop) **
          Vec.pts_to req req_bytes_loop **
          Vec.pts_to resp resp_bytes_loop **
          pure (
            Seq.length req_bytes_loop == 5 /\
            Seq.length resp_bytes_loop == 5 /\
            Vec.length req == 5 /\
            Vec.length resp == 5 /\
            Vec.is_full_vec req /\
            Vec.is_full_vec resp /\
            Vec.is_full_vec srv.stack /\
            Vec.is_full_vec srv.size /\
            SZ.v (R.read remaining) <= SZ.v fuel)
      decreases %[(if !running then 1 else 0); SZ.v (!remaining)]
      {
        with rem_live keep_live received_loop sent_loop log_loop req_bytes_loop resp_bytes_loop.
          assert (
            R.pts_to remaining rem_live **
            R.pts_to running keep_live **
            server_exactly srv (Ghost.reveal log_loop) **
            TCP.is_channel ch (Ghost.reveal received_loop) (Ghost.reveal sent_loop) **
            Vec.pts_to req req_bytes_loop **
            Vec.pts_to resp resp_bytes_loop **
            pure (
              Seq.length req_bytes_loop == 5 /\
              Seq.length resp_bytes_loop == 5 /\
              Vec.length req == 5 /\
              Vec.length resp == 5 /\
              Vec.is_full_vec req /\
              Vec.is_full_vec resp /\
              Vec.is_full_vec srv.stack /\
              Vec.is_full_vec srv.size /\
              SZ.v rem_live <= SZ.v fuel));
        Vec.to_array_pts_to req;
        let nread = TCP.read_full ch (Vec.vec_to_array req) 5sz;
        with req_bytes_after chunk. _;
    assert (pure (nread == 5sz));
    assert (pure (Seq.length req_bytes_after == 5));
    assert (pure (Seq.length chunk == 5));
    Vec.to_vec_pts_to req;
    if (nread = 5sz) {
      let tag = Calc.Impl.Parser.parse_tag req;
      if U8.lt tag 6uy {
        assert (pure (U8.v tag < 6));
        assert (pure (tag == Seq.index req_bytes_after 0));
        assert (pure (U8.v (Seq.index req_bytes_after 0) < 6));
        CalcCP.lemma_parse_request_some_if_valid_tag req_bytes_after;
        assert (pure (parse_request req_bytes_after <> None));
        Calc.Server.process_request srv req resp;
        with resp_bytes_after log_after. _;
        Vec.pts_to_len resp;
        assert (pure (Seq.length resp_bytes_after == 5));
        Vec.to_array_pts_to resp;
        let nwritten = TCP.write ch (Vec.vec_to_array resp) 5sz;
        assert (pure (nwritten == 5sz));
        Vec.to_vec_pts_to resp;
        let received_after = Ghost.hide (Seq.append (Ghost.reveal received_loop) chunk);
        let sent_after =
          Ghost.hide
            (Seq.append
              (Ghost.reveal sent_loop)
              (if SZ.v nwritten <= Seq.length resp_bytes_after
               then Seq.slice resp_bytes_after 0 (SZ.v nwritten)
               else Seq.create 0 0uy));
        assert (pure (Ghost.reveal received_after == Seq.append (Ghost.reveal received_loop) chunk));
        assert (pure (Ghost.reveal sent_after ==
          Seq.append
            (Ghost.reveal sent_loop)
            (if SZ.v nwritten <= Seq.length resp_bytes_after
             then Seq.slice resp_bytes_after 0 (SZ.v nwritten)
             else Seq.create 0 0uy)));
        rewrite
          (TCP.is_channel
            ch
            (Seq.append (Ghost.reveal received_loop) chunk)
            (Seq.append
              (Ghost.reveal sent_loop)
              (if SZ.v nwritten <= Seq.length resp_bytes_after
               then Seq.slice resp_bytes_after 0 (SZ.v nwritten)
               else Seq.create 0 0uy)))
          as
          (TCP.is_channel ch (Ghost.reveal received_after) (Ghost.reveal sent_after));
        if (nwritten = 5sz) {
          let rem_now = R.read remaining;
          assert (pure (not (rem_now = 0sz)));
          assert (pure (0 < SZ.v rem_now));
          let next = SZ.sub rem_now 1sz;
          assert (pure (SZ.v next < SZ.v rem_now));
          assert (pure (SZ.v next <= SZ.v fuel));
          remaining := next
        } else {
          running := false
        }
      } else {
        let received_after = Ghost.hide (Seq.append (Ghost.reveal received_loop) chunk);
        let sent_after = Ghost.hide (Ghost.reveal sent_loop);
        assert (pure (Seq.length req_bytes_after == 5));
        assert (pure (Seq.length resp_bytes_loop == 5));
        rewrite
          (TCP.is_channel ch (Seq.append (Ghost.reveal received_loop) chunk) (Ghost.reveal sent_loop))
          as
          (TCP.is_channel ch (Ghost.reveal received_after) (Ghost.reveal sent_after));
        running := false
      }
    } else {
      let received_after = Ghost.hide (Seq.append (Ghost.reveal received_loop) chunk);
      let sent_after = Ghost.hide (Ghost.reveal sent_loop);
      rewrite
        (TCP.is_channel ch (Seq.append (Ghost.reveal received_loop) chunk) (Ghost.reveal sent_loop))
        as
        (TCP.is_channel ch (Ghost.reveal received_after) (Ghost.reveal sent_after));
      running := false
    }
  }
}
#pop-options

fn run_channel
  (ch:TCP.channel)
  (fuel:SZ.t)
requires TCP.is_channel ch (Seq.create 0 0uy) (Seq.create 0 0uy)
ensures emp
{
  let srv = Calc.Server.new_server ();
  let req = Vec.alloc 0uy 5sz;
  let resp = Vec.alloc 0uy 5sz;
  run_connection_loop
    srv
    ch
    req
    resp
    fuel;
  with received1 sent1 log1 req_bytes1 resp_bytes1. _;
  TCP.close ch;
  Vec.free req;
  Vec.free resp;
  free_server_state srv
}

noextract
fn serve
  (bind_host:array U8.t)
  (bind_host_len:SZ.t)
  (port:U16.t)
  (fuel:SZ.t)
requires
  pts_to bind_host 'bind_host_bytes **
  pure (Seq.length 'bind_host_bytes == SZ.v bind_host_len)
returns ok:bool
ensures pts_to bind_host 'bind_host_bytes
{
  let listener_opt = TCP.listen_tcp bind_host bind_host_len port;
  match listener_opt {
    None -> { false }
    Some listener -> {
      let ch_opt = TCP.accept_tcp listener;
      match ch_opt {
        None -> {
          TCP.close_listener listener;
          false
        }
        Some ch -> {
          let srv = Calc.Server.new_server ();
          let req = Vec.alloc 0uy 5sz;
          let resp = Vec.alloc 0uy 5sz;
          run_connection_loop
            srv
            ch
            req
            resp
            fuel;
          with received1 sent1 log1 req_bytes1 resp_bytes1. _;
          TCP.close ch;
          Vec.free req;
          Vec.free resp;
          free_server_state srv;
          TCP.close_listener listener;
          true
        }
      }
    }
  }
}
