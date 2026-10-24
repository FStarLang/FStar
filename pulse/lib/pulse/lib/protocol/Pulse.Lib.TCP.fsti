module Pulse.Lib.TCP

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module Seq = FStar.Seq
module SZ = FStar.SizeT
module U16 = FStar.UInt16
module U8 = FStar.UInt8

include Pulse.Lib.TCP.History

val channel : Type0
val listener : Type0

val is_channel: channel -> received:bytes -> sent:bytes -> slprop
val is_listener: listener -> bind_host:bytes -> port:U16.t -> slprop

fn connect_tcp (hostname: array U8.t) (hostname_len: SZ.t) (port: U16.t)
  requires pts_to hostname 'hostname_bytes **
           pure (Seq.length 'hostname_bytes == SZ.v hostname_len)
  returns ch: option channel
  ensures pts_to hostname 'hostname_bytes **
          (match ch with
           | Some c -> is_channel c (Seq.create 0 0uy) (Seq.create 0 0uy)
           | None -> emp)

fn listen_tcp (bind_host: array U8.t) (bind_host_len: SZ.t) (port: U16.t)
  requires pts_to bind_host 'bind_host_bytes **
          pure (Seq.length 'bind_host_bytes == SZ.v bind_host_len)
  returns l: option listener
  ensures pts_to bind_host 'bind_host_bytes **
          (match l with
          | Some listener -> is_listener listener 'bind_host_bytes port
          | None -> emp)

fn accept_tcp (l: listener)
  requires is_listener l 'bind_host 'port
  returns ch: option channel
  ensures is_listener l 'bind_host 'port **
          (match ch with
          | Some c -> is_channel c (Seq.create 0 0uy) (Seq.create 0 0uy)
          | None -> emp)

fn close_listener (l: listener)
  requires is_listener l 'bind_host 'port
  ensures emp

fn read (ch: channel) (out: array U8.t) (max_len: SZ.t)
  requires is_channel ch 'received 'sent **
           pts_to out 'old **
           pure (Seq.length 'old == SZ.v max_len)
  returns n: SZ.t
  ensures exists* bytes chunk.
          is_channel ch (Seq.append (Ghost.reveal 'received) chunk) (Ghost.reveal 'sent) **
          pts_to out bytes **
          pure (Seq.length bytes == SZ.v max_len /\
                SZ.v n <= SZ.v max_len /\
                Seq.length chunk == SZ.v n /\
                Seq.equal chunk
                  (if SZ.v n <= Seq.length bytes
                   then Seq.slice bytes 0 (SZ.v n)
                   else Seq.create 0 0uy))

fn read_full (ch: channel) (out: array U8.t) (len: SZ.t)
  requires is_channel ch 'received 'sent **
           pts_to out 'old **
           pure (Seq.length 'old == SZ.v len)
  returns n: SZ.t
  ensures exists* bytes chunk.
          is_channel ch (Seq.append (Ghost.reveal 'received) chunk) (Ghost.reveal 'sent) **
          pts_to out bytes **
          pure (Seq.length bytes == SZ.v len /\
                n == len /\
                Seq.length chunk == SZ.v len /\
                Seq.equal chunk (Seq.slice bytes 0 (SZ.v len)))

fn write (ch: channel) (buf: array U8.t) (len: SZ.t)
  requires is_channel ch 'received 'sent **
           pts_to buf 'bytes **
           pure (SZ.v len <= Seq.length 'bytes)
  returns n: SZ.t
  ensures is_channel ch (Ghost.reveal 'received)
            (Seq.append (Ghost.reveal 'sent)
              (if SZ.v n <= Seq.length (Ghost.reveal 'bytes)
               then Seq.slice (Ghost.reveal 'bytes) 0 (SZ.v n)
               else Seq.create 0 0uy)) **
          pts_to buf 'bytes **
          pure (n == len)

fn close (ch: channel)
  requires is_channel ch 'received 'sent
  ensures emp
