module Calc.Server.EndpointRunner

#lang-pulse

open Pulse.Lib.Pervasives

module Endpoint = Calc.Server.Endpoint
module SZ = FStar.SizeT
module TCP = Pulse.Lib.TCP

fn run_channel_endpoint
  (ch:TCP.channel)
  (fuel:SZ.t)
requires TCP.is_channel ch Endpoint.calc_empty_bytes Endpoint.calc_empty_bytes
ensures emp
{
  Endpoint.run_channel_endpoint_impl ch fuel
}
