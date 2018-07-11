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
