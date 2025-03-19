module FStarC.TypeChecker.Primops.Docs

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Class.Monad

module Z = FStarC.BigInt
module PC = FStarC.Parser.Const

open FStarC.TypeChecker.Primops.Base

(* FIXME: most of these disabled as they would break extraction.
In extracted code, we need to turn the doc into a term representation
for it. I'm actually not sure how to do that since the document
type is abstract even internally. *)

let ops =
  let nm l = PC.p2l ["FStar"; "Pprint"; l] in
    let open FStarC.Pprint in
    [
      (* mk1 0 (nm "doc_of_char") doc_of_char; *)
      (* mk1 0 (nm "doc_of_string") doc_of_string; *)
      (* mk1 0 (nm "doc_of_bool") doc_of_bool; *)
      (* mk3 0 (nm "substring") (fun s i j -> substring s (Z.to_int_fs i) (Z.to_int_fs j)); *)
      (* mk2 0 (nm "fancystring") (fun s i -> fancystring s (Z.to_int_fs i)); *)
      (* mk4 0 (nm "fancysubstring") (fun s i j k -> fancysubstring s (Z.to_int_fs i) (Z.to_int_fs j) (Z.to_int_fs k)); *)
      (* mk1 0 (nm "utf8string") utf8string; *)
      //hardline & others: zero-arity...
      (* mk1 0 (nm "blank") (fun i -> blank (Z.to_int_fs i)); *)
      (* mk1 0 (nm "break_") (fun i -> break_ (Z.to_int_fs i)); *)

      (* mk2 0 (nm "op_Hat_Hat") (^^); *)
      (* mk2 0 (nm "op_Hat_Slash_Hat") (^/^); *)
      (* mk2 0 (nm "nest") (fun i d -> nest (Z.to_int_fs i) d); *)
      (* mk1 0 (nm "group") group; *)
      (* mk2 0 (nm "ifflat") ifflat; *)

      (* mk2 0 (nm "precede") precede; *)
      (* mk2 0 (nm "terminate") terminate; *)
      (* mk3 0 (nm "enclose") enclose; *)
      (* mk1 0 (nm "squotes") squotes; *)
      (* mk1 0 (nm "dquotes") dquotes; *)
      (* mk1 0 (nm "bquotes") bquotes; *)
      (* mk1 0 (nm "braces") braces; *)
      (* mk1 0 (nm "parens") parens; *)
      (* mk1 0 (nm "angles") angles; *)
      (* mk1 0 (nm "brackets") brackets; *)
      (* mk1 0 (nm "twice") twice; *)
      (* mk2 0 (nm "repeat") (fun i d -> repeat (Z.to_int_fs i) d); *)
      (* mk1 0 (nm "concat") concat; *)
      (* mk2 0 (nm "separate") separate; *)

      //concat_map: higher-order
      //separate_map: higher-order

      (* mk3 0 (nm "separate2") separate2; *)

      //optional: higher-order

      (* mk1 0 (nm "lines") lines; *)
      mk1 0 (nm "arbitrary_string") arbitrary_string;
      (* mk1 0 (nm "words") words; *)

      //split: higher-order
      (* mk2 0 (nm "flow") flow; *)
      //flow_map: higher-order

      (* mk1 0 (nm "url") url; *)
      (* mk1 0 (nm "align") align; *)
      (* mk2 0 (nm "hang") (fun i d -> hang (Z.to_int_fs i) d); *)
      (* mk4 0 (nm "prefix") (fun i j d1 d2 -> *)
      (*                       prefix (Z.to_int_fs i) (Z.to_int_fs j) d1 d2); *)
      (* mk3 0 (nm "jump") (fun i j d -> jump (Z.to_int_fs i) (Z.to_int_fs j) d); *)
      (* mk5 0 (nm "infix") (fun i j d1 d2 d3 -> infix (Z.to_int_fs i) (Z.to_int_fs j) d1 d2 d3); *)
      (* mk5 0 (nm "surround") (fun i j d1 d2 d3 -> surround (Z.to_int_fs i) (Z.to_int_fs j) d1 d2 d3); *)
      (* mk5 0 (nm "soft_surround") (fun i j d1 d2 d3 -> soft_surround (Z.to_int_fs i) (Z.to_int_fs j) d1 d2 d3); *)

      // surround separate: arity too big :-)
      // surroundd_separate_map: higher-order

      // pretty_string: float
      mk1 0 (nm "render") render;
    ]
