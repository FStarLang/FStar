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

/// Property that a predicate is fractional (can be split and combined)
/// A fractional predicate satisfies: pred f1 ** pred f2 <==> pred (f1 +. f2)
let fractional (p : perm -> slprop) : prop =
  forall (f1 f2 : perm). p f1 ** p f2 == p (f1 +. f2)

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
fn create (#pred : perm -> slprop) 
          (frac_pred : squash (fractional pred))
  requires pred 1.0R
  returns l : rwlock pred
  ensures is_rwlock l #1.0R

/// Acquire reader access
/// Spins until a reader slot is available
/// Receives: reader_parts token and pred f separately so caller can use the predicate
fn acquire_reader (#pred : perm -> slprop) (#perm_lock:perm) (l : rwlock pred)
  preserves is_rwlock l #perm_lock
  returns f : perm
  ensures reader_parts l f ** pred f

/// Release reader access
/// Returns the reader's fraction to the lock
/// Requires both reader_parts and pred f
fn release_reader (#pred : perm -> slprop) (#perm_lock:perm) (l : rwlock pred) (#f:perm)
  requires is_rwlock l #perm_lock ** reader_parts l f ** pred f
  ensures is_rwlock l #perm_lock

/// Acquire writer access
/// Spins until all readers have released and no other writer holds the lock
/// Receives: full permission to the predicate (pred 1.0R)
fn acquire_writer (#pred : perm -> slprop) (#perm_lock:perm) (l : rwlock pred)
  requires is_rwlock l #perm_lock
  ensures is_rwlock l #perm_lock ** writer_token l ** pred 1.0R

/// Release writer access
/// Returns full permission to the lock
fn release_writer (#pred : perm -> slprop) (#perm_lock:perm) (l : rwlock pred)
  requires is_rwlock l #perm_lock ** writer_token l ** pred 1.0R
  ensures is_rwlock l #perm_lock

/// Share is_rwlock permission (for multiple users of the same lock)
ghost
fn share (#pred:perm -> slprop) (#p:perm) (l:rwlock pred)
  requires is_rwlock l #p
  ensures is_rwlock l #(p /. 2.0R) ** is_rwlock l #(p /. 2.0R)

/// Gather is_rwlock permissions
ghost
fn gather (#pred:perm -> slprop) (#p1 #p2:perm) (l:rwlock pred)
  requires is_rwlock l #p1 ** is_rwlock l #p2
  ensures is_rwlock l #(p1 +. p2)
