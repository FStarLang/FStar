(*
   Copyright 2025 Microsoft Research

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

module Pulse.Lib.RWLock
#lang-pulse

open Pulse.Lib.Pervasives
open PulseCore.FractionalPermission
open Pulse.Lib.Fractional

///
/// Reader-Writer Lock with Fractional Permissions
///
/// A reader-writer lock protects a predicate indexed by a permission fraction.
/// Multiple readers can acquire the lock simultaneously, each receiving a 
/// fraction of the protected permission. A writer acquires exclusive access
/// with the full permission.
///
/// Key properties:
/// - Multiple concurrent readers allowed
/// - Writers have exclusive access  
/// - Readers receive fractional permissions (halving on each acquire)
/// - No starvation guarantees (simple spin-loop implementation)
///
/// Usage:
///   // Define a fractional predicate
///   let my_pred (f:perm) : slprop = my_resource f
///   
///   // Create lock with proof that predicate is fractional
///   let lock = create #my_pred () // pass () for squash proof
///   
///   // Acquire/release for reading
///   let f = acquire_reader lock
///   // Use pred f here...
///   release_reader lock
///   
///   // Acquire/release for writing  
///   acquire_writer lock
///   // Have pred 1.0R here...
///   release_writer lock
///

/// Type of reader-writer locks (abstract)  
val rwlock (pred : perm -> slprop) : Type0

/// Predicate asserting the lock is alive with permission p
val is_rwlock (#pred : perm -> slprop) (l : rwlock pred) (#p:perm) : slprop

/// Internal token tracking reader's position in the permission table
/// This is used alongside pred f to form the full reader state
val reader_parts (#pred : perm -> slprop) (l : rwlock pred) (f : perm) : slprop

/// Token representing writer's exclusive access
val writer_token (#pred : perm -> slprop) (l : rwlock pred) : slprop

/// Create a new reader-writer lock
/// Requires: the predicate with full permission (pred 1.0R)
///           and a proof that the predicate is fractional (can be split/combined)
/// Ensures: is_rwlock with full permission, lock initially unlocked
fn create (#pred : perm -> slprop) {| fractional pred |}
          (_u : unit)
  requires pred 1.0R
  returns l : rwlock pred
  ensures is_rwlock l #1.0R

/// Acquire reader access
/// Spins until a reader slot is available
/// Receives: reader_parts token and pred f separately so caller can use the predicate
fn acquire_reader (#pred : perm -> slprop) {| fractional pred |} (#perm_lock:perm) (l : rwlock pred)
  preserves is_rwlock l #perm_lock
  returns f : perm
  ensures reader_parts l f
  ensures pred f

/// Release reader access
/// Returns the reader's fraction to the lock
/// Requires both reader_parts and pred f
fn release_reader (#pred : perm -> slprop) {| fractional pred |} (#perm_lock:perm) (l : rwlock pred) (#f:perm)
  preserves is_rwlock l #perm_lock
  requires reader_parts l f
  requires pred f

/// Acquire writer access
/// Spins until all readers have released and no other writer holds the lock
/// Receives: full permission to the predicate (pred 1.0R)
fn acquire_writer (#pred : perm -> slprop) {| fractional pred |} (#perm_lock:perm) (l : rwlock pred)
  preserves is_rwlock l #perm_lock
  ensures writer_token l
  ensures pred 1.0R

/// Release writer access
/// Returns full permission to the lock
fn release_writer (#pred : perm -> slprop) {| fractional pred |} (#perm_lock:perm) (l : rwlock pred)
  preserves is_rwlock l #perm_lock
  requires writer_token l
  requires pred 1.0R

/// Try to free the lock when it is not acquired
/// Returns pred 1.0R on success, otherwise returns the lock back
fn try_free (#pred : perm -> slprop) {| fractional pred |} (l : rwlock pred)
  requires is_rwlock l #1.0R
  returns b:bool
  ensures cond b (pred 1.0R) (is_rwlock l #1.0R)

/// Share is_rwlock permission (for multiple users of the same lock)
ghost
fn share (#pred:perm -> slprop) {| fractional pred |} (#p:perm) (l:rwlock pred)
  requires is_rwlock l #p
  ensures is_rwlock l #(p /. 2.0R)
  ensures is_rwlock l #(p /. 2.0R)

/// Gather is_rwlock permissions
ghost
fn gather (#pred:perm -> slprop) {| fractional pred |} (#p1 #p2:perm) (l:rwlock pred)
  requires is_rwlock l #p1
  requires is_rwlock l #p2
  ensures is_rwlock l #(p1 +. p2)
