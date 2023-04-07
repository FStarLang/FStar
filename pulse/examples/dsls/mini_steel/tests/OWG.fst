module OWG

module T = FStar.Tactics
open Pulse.Syntax
open Pulse.Main
open Steel.ST.Util 
open Steel.ST.Reference
open Pulse.Steel.Wrapper
open Steel.FractionalPermission
open FStar.Ghost

module U32 = FStar.UInt32

open Tests.Common

#push-options "--ide_id_info_off"
#push-options "--print_universes --print_implicits"
