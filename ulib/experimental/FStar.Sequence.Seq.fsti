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
module Sequence = FStar.Sequence.Base

val sequence_of_seq (#a:Type) (s:Seq.seq a) : Sequence.seq a

val seq_of_sequence (#a:Type) (s:Sequence.seq a) : Seq.seq a

let related #a (s:Seq.seq a) (s':Sequence.seq a) =
  Seq.length s == Sequence.length s' /\
  (forall i.{:pattern (Seq.index s i) \/ (Sequence.index s' i)}
      Seq.index s i == Sequence.index s' i)

val related_sequence_of_seq (#a:Type) (s:Seq.seq a)
  : Lemma (related s (sequence_of_seq s))

val related_seq_of_sequence (#a:Type) (s:Sequence.seq a)
  : Lemma (related (seq_of_sequence s) s)

val seq_of_sequence_of_seq (#a:Type) (s:Seq.seq a)
  : Lemma (seq_of_sequence (sequence_of_seq s) == s)

val sequence_of_seq_of_sequence (#a:Type) (s:Sequence.seq a)
  : Lemma (sequence_of_seq (seq_of_sequence s) == s)
