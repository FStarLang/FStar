(*
   Copyright 2008-2018 Microsoft Research

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
module Test
open JSONParser

let key
  (c: Spec.char {c <> Spec.double_quote} )
: Tot Spec.key
= Spec.Key (Spec.string_of_char c)

let a = Char.char_of_int 65
let ka = key a
let b = Char.char_of_int 66
let kb = key b
let c = Char.char_of_int 67
let kc = key c

let schema: Spec.json_schema =
    Spec.Object [
      (ka, Spec.String);
      (kb, Spec.Object [
	(kc, Spec.String)
      ])
    ]

let s: Spec.string =
Seq.cons Spec.left_brace (
  Seq.cons Spec.double_quote (
    Seq.cons a (
      Seq.cons Spec.double_quote (
	Seq.cons Spec.colon (
	  Seq.cons Spec.double_quote (
	    Seq.cons Spec.double_quote (
	      Seq.cons Spec.comma (
		Seq.cons Spec.double_quote (
		  Seq.cons b (
		    Seq.cons Spec.double_quote (
		      Seq.cons Spec.colon (
			Seq.cons Spec.left_brace (
			  Seq.cons Spec.double_quote (
			    Seq.cons c (
			      Seq.cons Spec.double_quote (
				Seq.cons Spec.colon (
				  Seq.cons Spec.double_quote (
				    Seq.cons Spec.double_quote (
				      Seq.cons Spec.right_brace (
					Seq.cons Spec.right_brace (
					  Seq.empty
)))))))))))))))))))))

(* // This is too slow
let test
: squash
  (Some? (Spec.gparse_string schema d s))
= assert_norm (None? (Spec.gparse schema d s))
*)
