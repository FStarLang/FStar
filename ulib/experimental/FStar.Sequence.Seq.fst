(*
   Copyright 2008-2021 Jay Lorch, Rustan Leino, Alex Summers, Dan
   Rosen, Nikhil Swamy, Microsoft Research, and contributors to
   the Dafny Project

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Includes material from the Dafny project
   (https://github.com/dafny-lang/dafny) which carries this license
   information:

     Created 9 February 2008 by Rustan Leino.
     Converted to Boogie 2 on 28 June 2008.
     Edited sequence axioms 20 October 2009 by Alex Summers.
     Modified 2014 by Dan Rosen.
     Copyright (c) 2008-2014, Microsoft.
     Copyright by the contributors to the Dafny Project
     SPDX-License-Identifier: MIT
*)

(**
This module relates FStar.Seq.seq to FStar.Sequence.seq and provides
a bijection between the two. As such, it provides a path for migrating developments based on FStar.Seq to FStar.Sequence, or vice versa
*)

module FStar.Sequence.Seq
module Seq = FStar.Seq
module Sequence = FStar.Sequence
open FStar.Sequence

let rec sequence_of_seq (#a:Type) (s:Seq.seq a)
  : Tot (Sequence.seq a)
        (decreases (Seq.length s))
  = if Seq.length s = 0
    then Sequence.empty
    else let prefix, last = Seq.un_snoc s in
         sequence_of_seq prefix $:: last

let rec seq_of_sequence (#a:Type) (s:Sequence.seq a)
  : Tot (Seq.seq a)
        (decreases (Sequence.length s))
  = if Sequence.length s = 0
    then Seq.empty
    else let prefix = Sequence.take s (Sequence.length s - 1) in
         Seq.snoc (seq_of_sequence prefix)
                  (s$@(Sequence.length s - 1))

let rec related_sequence_of_seq (#a:Type) (s:Seq.seq a)
  : Lemma
    (ensures related s (sequence_of_seq s))
    (decreases (Seq.length s))
  = if Seq.length s = 0 then ()
    else (
      let prefix, last = Seq.un_snoc s in
      related_sequence_of_seq prefix
    )

let rec related_seq_of_sequence (#a:Type) (s:Sequence.seq a)
  : Lemma
    (ensures related (seq_of_sequence s) s)
    (decreases (Sequence.length s))
  = if Sequence.length s = 0
    then ()
    else (
       related_seq_of_sequence (Sequence.take s (Sequence.length s - 1))
    )

let seq_of_sequence_of_seq (#a:Type) (s:Seq.seq a)
  : Lemma (seq_of_sequence (sequence_of_seq s) == s)
  = related_sequence_of_seq s;
    related_seq_of_sequence (sequence_of_seq s);
    assert (Seq.equal (seq_of_sequence (sequence_of_seq s)) s)

let sequence_of_seq_of_sequence (#a:Type) (s:Sequence.seq a)
  : Lemma (sequence_of_seq (seq_of_sequence s) == s)
  = related_seq_of_sequence s;
    related_sequence_of_seq (seq_of_sequence s);
    assert (Sequence.equal (sequence_of_seq (seq_of_sequence s)) s)
