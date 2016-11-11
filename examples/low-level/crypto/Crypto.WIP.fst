module Crypto.WIP

// We implement ideal AEAD on top of ideal Chacha20 and ideal Poly1305. 
// We precisely relate AEAD's log to their underlying state.

// This file intends to match the spec of AEAD0.fst in mitls-fstar. 

open FStar.UInt32
open FStar.Ghost
open Buffer.Utils
open FStar.Monotonic.RRef

open Crypto.Indexing
open Crypto.Symmetric.Bytes
open Crypto.Plain
open Flag

open Crypto.Symmetric.PRF
open Crypto.AEAD.Encoding 
open Crypto.AEAD.Invariant
open Crypto.AEAD.Lemmas
open Crypto.AEAD.Lemmas.Part2
open Crypto.AEAD.BufferUtils
open Crypto.AEAD

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module CMA = Crypto.Symmetric.UF1CMA
module MAC = Crypto.Symmetric.MAC

module Cipher = Crypto.Symmetric.Cipher
module PRF = Crypto.Symmetric.PRF
module Plain = Crypto.Plain

   

