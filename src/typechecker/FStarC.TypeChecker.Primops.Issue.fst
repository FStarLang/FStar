module FStarC.TypeChecker.Primops.Issue

open FStarC
open FStarC.Effect
open FStarC.Errors
open FStarC.Class.Monad

open FStarC.TypeChecker.Primops.Base

module PC = FStarC.Parser.Const
module Z = FStarC.BigInt

let ops : list primitive_step =
  let mk_lid l = PC.p2l ["FStar"; "Issue"; l] in [
    mk1 0 (mk_lid "message_of_issue") Mkissue?.issue_msg;
    mk1 0 (mk_lid "level_of_issue") (fun i -> Errors.string_of_issue_level i.issue_level);
    mk1 0 (mk_lid "number_of_issue") (fun i -> fmap Z.of_int_fs i.issue_number);
    mk1 0 (mk_lid "range_of_issue") Mkissue?.issue_range;
    mk1 0 (mk_lid "context_of_issue") Mkissue?.issue_ctx;
    mk1 0 (mk_lid "render_issue") Errors.format_issue;
    mk5 0 (mk_lid "mk_issue_doc") (fun level msg range number context ->
          { issue_level = Errors.issue_level_of_string level;
            issue_range = range;
            issue_number = fmap Z.to_int_fs number;
            issue_msg = msg;
            issue_ctx = context}
    );
  ]
