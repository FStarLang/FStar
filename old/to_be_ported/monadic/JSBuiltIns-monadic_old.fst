(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
module JSBuiltIns

type PrimVal' =
  | PrimBool' : bool -> PrimVal'
  | PrimFunction' : (PrimVal' -> ST (ref PrimVal' -> ST PrimVal')) -> PrimVal'
  | PrimNull' : PrimVal'
  | PrimNum' : float -> PrimVal'
  | PrimObject' : list string -> PrimVal'
  | PrimString' : string -> PrimVal'
  | PrimUndefined' : PrimVal' 
  | PrimReturn' : PrimVal' -> PrimVal'
  | PrimBreak' : PrimVal' -> PrimVal'

val primToBool': PrimVal' -> ST bool
val primToFunction': PrimVal' -> ST ((PrimVal' -> ST (ref PrimVal' -> ST PrimVal')))
val primToNum' : PrimVal' -> ST float
val primToString' : PrimVal' -> ST string
val jsNewObject' : list (string * PrimVal') -> ST PrimVal'  
val jsGetField': PrimVal' -> ST (PrimVal' -> ST PrimVal')
val jsUpdateField' : PrimVal' -> ST (PrimVal' -> ST (PrimVal' -> ST PrimVal'))

val toNumber' : PrimVal' -> ST PrimVal' 
val toObject' : PrimVal' -> ST PrimVal'         
val toString' : PrimVal' -> ST PrimVal'         

val abstractEquality' : PrimVal' -> ST (PrimVal' -> ST PrimVal')
val addition' : PrimVal' -> ST (PrimVal' -> ST PrimVal')

val global' : ref PrimVal'
(* let global' = (ref(jsNewObject' [])) *)
