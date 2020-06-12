(*
   Copyright 2020 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module PingPong
open Steel.Effect
open Steel.Memory
open Steel.Channel.Protocol
open Steel.Channel.Duplex
module P = Steel.Channel.Protocol
open Steel.SteelT.Basics

let pingpong : prot =
  x <-- P.send (p:string{p="ping"});
  y <-- P.recv (q:string{q="pong"});
  P.done

let client (c:chan pingpong)
  : SteelT unit
           (endpoint c pingpong)
           (fun _ -> endpoint c P.done)
  = send c "ping";
    let y = recv c in
    assert (y="pong");
    return ()

let server (c:chan pingpong)
  : SteelT unit
           (endpoint c (P.dual pingpong))
           (fun _ -> endpoint c P.done)
  = let y = recv c in
    assert (y = "ping");
    send c "pong"

let client_server (_:unit)
  : SteelT unit emp (fun _ -> emp)
  = let c = new_chan pingpong in
    par (fun _ -> client c) (fun _ -> server c);
    drop _

module T = Steel.Primitive.ForkJoin

let rec join_all (threads:list (T.thread emp))
  : SteelT unit emp (fun _ -> emp)
  = match threads with
    | [] -> return ()
    | hd::tl ->
      T.join hd;
      join_all tl

let rec many (n:nat) (threads:list (T.thread emp))
  : SteelT unit emp (fun _ -> emp)
  = if n = 0 then join_all threads
    else begin
      h_intro_emp_l _;
      T.fork client_server (fun t _ -> many (n - 1) (t::threads))
    end
