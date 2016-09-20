open FStar_Parser_Parse
open FStar_Options
open FStar_Util
open Lexing

let stringOfPos (p:position) = spr "(%d:%d)" p.pos_lnum (p.pos_cnum - p.pos_bol)
let outputPos os (p:position) = Printf.fprintf os "(%d:%d)" p.pos_lnum (p.pos_cnum - p.pos_bol)
let warningStringOfPos (p:position) = spr "(%d:%d)" p.pos_lnum ((p.pos_cnum - p.pos_bol) + 1)

type context =
    | CtxtLetDecl of bool * position
    | CtxtIf of position
    | CtxtTry of position
    | CtxtFun of position
    | CtxtFunction of position
    | CtxtWithAsLet of position
    | CtxtMatch of position
    | CtxtWhen of position
    | CtxtVanilla of position * bool
    | CtxtThen of position
    | CtxtElse of position
    | CtxtTypeDefns of position
    | CtxtModuleHead of position  * token
    | CtxtModuleBody of position  * bool
    (*| CtxtException of position*)
    | CtxtParen of token * position
    | CtxtSeqBlock of firstInSequence * position * addBlockEnd
    | CtxtMatchClauses of bool * position
and addBlockEnd = AddBlockEnd | NoAddBlockEnd | AddOneSidedBlockEnd
and firstInSequence = FirstInSeqBlock | NotFirstInSeqBlock

let start_pos = function
    | CtxtModuleHead (p,_) | CtxtModuleBody (p,_)
    | CtxtLetDecl (_,p) | CtxtTypeDefns p | CtxtParen (_,p)
    | CtxtWithAsLet p
    | CtxtMatchClauses (_,p) | CtxtIf p | CtxtMatch p | CtxtWhen p | CtxtFunction p | CtxtFun p | CtxtTry p | CtxtThen p | CtxtElse p | CtxtVanilla (p,_)
    | CtxtSeqBlock (_,p,_) -> p
let start_col ctxt = (start_pos ctxt).pos_cnum - (start_pos ctxt).pos_bol
let isInfix token =
    match token with
    | COMMA
    | OPINFIX0a "||"
    | OPINFIX0b "&&"
    | AMP
    | DOLLAR
    | OPINFIX1 _
    | OPINFIX2 _
    | COLON_COLON
    | COLON_EQUALS
    | MINUS -> true
    | _ -> false
let isNonAssocInfixToken token =
    match token with
    | EQUALS -> true
    | _ -> false
let infixTokenLength token =
    match token with
    | COMMA  -> 1
    | AMP -> 1
    | DOLLAR -> 1
    | MINUS -> 1
    | BAR -> 1
    (*| LESS false -> 1*)
    | EQUALS -> 1
    | COLON_COLON -> 2
    | COLON_EQUALS -> 2
    | OPINFIX0a d
    | OPINFIX0b d
    | OPINFIX1 d
    | OPINFIX2 d -> String.length d
    | _ -> assert false; 1
let rec isIfBlockContinuator token =
    match token with
    | THEN | ELSE -> true
    | END | RPAREN -> true
    | ORIGHT_BLOCK_END | OBLOCKEND | ODECLEND -> true
    | ODUMMY(token) -> isIfBlockContinuator(token)
    | _ -> false
let rec isTryBlockContinuator token =
    match token with
    | WITH -> true
    | ORIGHT_BLOCK_END | OBLOCKEND | ODECLEND -> true
    | ODUMMY(token) -> isTryBlockContinuator(token)
    | _ -> false
let rec isThenBlockContinuator token =
    match token with
    | ORIGHT_BLOCK_END | OBLOCKEND | ODECLEND -> true
    | ODUMMY(token) -> isThenBlockContinuator(token)
    | _ -> false
let rec isTypeContinuator token =
    match token with
    | RBRACE | WITH | BAR | AND | END -> true
    | ORIGHT_BLOCK_END | OBLOCKEND | ODECLEND -> true
    | ODUMMY(token) -> isTypeContinuator(token)
    | _ -> false
let rec isLetContinuator token =
    match token with
    | AND -> true
    | ORIGHT_BLOCK_END | OBLOCKEND | ODECLEND -> true
    | ODUMMY(token) -> isLetContinuator(token)
    | _ -> false
let rec isTypeSeqBlockElementContinuator token =
    match token with
    | BAR -> true
    | OBLOCKBEGIN | ORIGHT_BLOCK_END | OBLOCKEND | ODECLEND -> true
    | ODUMMY(token) -> isTypeSeqBlockElementContinuator token
    | _ -> false
let rec isSeqBlockElementContinuator token =
    isInfix token ||
    match token with
    | END | AND | WITH | THEN | RPAREN | RBRACE | RBRACK | BAR_RBRACK -> true
    | ORIGHT_BLOCK_END | OBLOCKEND | ODECLEND -> true
    | ODUMMY(token) -> isSeqBlockElementContinuator token
    | _ -> false
let isLongIdentifier token = (match token with IDENT _ | DOT -> true | _ -> false)
let isLongIdentifierOrGlobal token = (match token with IDENT _ | DOT -> true | _ -> false)
let isAtomicExprEndToken token =
    match token with
    | IDENT _
    | INT8 _ | INT16 _ | INT32 _ | INT64 _ (*| NATIVEINT _*)
    | UINT8 _ | UINT16 _ | UINT32 _ | UINT64 _ (*| UNATIVEINT _*)
    | (*DECIMAL _ | BIGNUM _  |*) STRING _ | BYTEARRAY _  | CHAR _
    | (*IEEE32 _ |*) IEEE64 _
    | RPAREN | RBRACK | RBRACE | BAR_RBRACK | END
    | FALSE | TRUE | UNDERSCORE -> true
    | _ -> false
let parenTokensBalance t1 t2 =
    match t1,t2 with
    | (LPAREN,RPAREN)
    | (LBRACE,RBRACE)
    | (LBRACK,RBRACK)
    | (LBRACK_BAR,BAR_RBRACK)
    | (BEGIN,END) -> true
    | _ -> false
type lexbufState =
    {
        startPos: position;
        endPos  : position;
        pastEOF : bool
    }
type positionTuple =
    {
        x: position;
        y: position
    }
type tokenTup =
    {
        token: token;
        lexbufState: lexbufState;
        lastTokenPos: positionTuple
    }
let shiftColumnBy p n = {p with pos_bol = p.pos_cnum - p.pos_bol + n}
let startPos (t: tokenTup) = t.lexbufState.startPos
let endPos (t: tokenTup)   = t.lexbufState.endPos
let useLocation (t: tokenTup) tok =
    {
        token = tok;
        lexbufState = {startPos = t.lexbufState.startPos; endPos = t.lexbufState.endPos; pastEOF = false};
        lastTokenPos = t.lastTokenPos
    }
let useShiftedLocation (t: tokenTup) tok shiftLeft shiftRight =
    {
        token = tok;
        lexbufState =
            {
                startPos = shiftColumnBy t.lexbufState.startPos shiftLeft;
                endPos   = shiftColumnBy t.lexbufState.endPos shiftRight;
                pastEOF  = false
            };
        lastTokenPos = t.lastTokenPos
    }
type positionWithColumn =
    {
        position: position;
        column: int
    }
let tokenizer lexer (lexbuf: lexbuf) =
    set_option "light" (Bool false);
    let lexbufStateForInsertedDummyTokens (lastTokenStartPos, lastTokenEndPos) =
        {
            startPos = lastTokenStartPos;
            endPos   = lastTokenEndPos;
            pastEOF  = false
        } in
    let getLexbufState() =
        {
            startPos = lexbuf.lex_start_p;
            endPos   = lexbuf.lex_curr_p;
            pastEOF  = lexbuf.lex_eof_reached
        } in
    let setLexbufState (p:lexbufState) =
        lexbuf.lex_start_p <- p.startPos;
        lexbuf.lex_curr_p <- p.endPos;
        lexbuf.lex_eof_reached <- p.pastEOF in
    let startPosOfTokenTup (tokenTup:tokenTup) =
        match tokenTup.token with
        | EOF _ -> shiftColumnBy tokenTup.lexbufState.startPos (-1)
        | _ ->  tokenTup.lexbufState.startPos in
    let savedLexbufState = ref {startPos = lexbuf.lex_start_p; endPos = lexbuf.lex_curr_p; pastEOF = false} in
    let haveLexbufState = ref false in
    let runWrappedLexerInConsistentLexbufState() =
        let state = if !haveLexbufState then !savedLexbufState else getLexbufState() in
        setLexbufState state;
        let lastTokenStart = state.startPos in
        let lastTokenEnd = state.endPos in
        let token = lexer lexbuf in
        let tokenLexbufState = getLexbufState() in
        savedLexbufState := tokenLexbufState;
        haveLexbufState := true;
        {token = token; lexbufState = tokenLexbufState; lastTokenPos = {x = lastTokenStart; y = lastTokenEnd}} in
    let delayedStack = ref [] in
    let tokensThatNeedNoProcessingCount = ref 0 in
    let delayToken tokenTup = delayedStack := tokenTup :: !delayedStack in
    let delayTokenNoProcessing tokenTup = delayToken tokenTup; tokensThatNeedNoProcessingCount := !tokensThatNeedNoProcessingCount + 1 in
    let popNextTokenTup() =
        if List.length !delayedStack > 0
        then begin
            let tokenTup = List.hd !delayedStack in
            delayedStack := List.tl !delayedStack;
            tokenTup
        end else
            runWrappedLexerInConsistentLexbufState() in
    let initialized = ref false in
    let offsideStack = ref [] in
    let prevWasAtomicEnd = ref false in
    let peekInitial() =
        let initialLookaheadTokenTup  = popNextTokenTup() in
        delayToken initialLookaheadTokenTup;
        initialized := true;
        offsideStack := (CtxtSeqBlock(FirstInSeqBlock,startPosOfTokenTup initialLookaheadTokenTup,NoAddBlockEnd)) :: !offsideStack;
        initialLookaheadTokenTup in
    let pushCtxt tokenTup (newCtxt:context) =
        let rec unindentationLimit strict stack =
            match newCtxt,stack with
            | _, [] -> {position = start_pos newCtxt;  column = -1}
            | _, (CtxtVanilla _ :: rest) -> unindentationLimit strict rest
            | _, (CtxtSeqBlock _ :: rest) when not strict -> unindentationLimit strict rest
            | _, (CtxtParen _ :: rest) when not strict -> unindentationLimit strict rest
            | _,(((CtxtMatch _) as ctxt1) :: CtxtSeqBlock _ :: (CtxtParen ((BEGIN | LPAREN),_) as ctxt2) :: _rest)
                        -> if start_col ctxt1 <= start_col ctxt2
                            then {position = start_pos ctxt1; column = start_col ctxt1}
                            else {position = start_pos ctxt2; column = start_col ctxt2}
            | (CtxtMatchClauses _), (CtxtFunction _ :: CtxtSeqBlock _ :: (CtxtLetDecl  _ as limitCtxt) :: _rest)
                        -> {position = start_pos limitCtxt; column = start_col limitCtxt}
            | (CtxtMatchClauses _), (CtxtFunction _ :: rest)
                        -> unindentationLimit false rest
            | _,(CtxtMatchClauses _ :: (CtxtTry _ as limitCtxt) :: _rest)
                        -> {position = start_pos limitCtxt; column = start_col limitCtxt}
            | _,(CtxtFun _ :: rest)
                        -> unindentationLimit false rest
            | _,(CtxtParen (LBRACE,_) :: CtxtVanilla _ :: CtxtSeqBlock _ :: rest)
            | _,(CtxtSeqBlock _ :: CtxtParen(LBRACE,_) :: CtxtVanilla _ :: CtxtSeqBlock _ :: rest)
                        -> unindentationLimit false rest
            | CtxtSeqBlock _, (CtxtElse _  :: (CtxtIf _ as limitCtxt) :: _rest)
                        -> {position = start_pos limitCtxt; column = start_col limitCtxt}
            | _,((CtxtThen _ | CtxtElse _)  :: rest)
                      -> unindentationLimit false rest
            | _,(CtxtFunction _ :: rest)
                        -> unindentationLimit false rest
            | _,(CtxtParen (((*SIG | STRUCT |*) BEGIN),_) :: CtxtSeqBlock _  :: (CtxtModuleBody (_,false) as limitCtxt) ::  _)
            | _,(CtxtParen ((BEGIN | LPAREN | LBRACK | LBRACE | LBRACK_BAR)      ,_) :: CtxtSeqBlock _ :: CtxtThen _ :: (CtxtIf _         as limitCtxt) ::  _)
            | _,(CtxtParen ((BEGIN | LPAREN | LBRACK | LBRACE | LBRACK_BAR)      ,_) :: CtxtSeqBlock _ :: CtxtElse _ :: (CtxtIf _         as limitCtxt) ::  _)
            | _,(CtxtParen ((BEGIN | LPAREN | (*LESS true |*) LBRACK | LBRACK_BAR)      ,_) :: CtxtVanilla _ :: (CtxtSeqBlock _         as limitCtxt) ::  _)
            | _,(CtxtSeqBlock _ :: CtxtParen((BEGIN | LPAREN | LBRACK | LBRACK_BAR),_) :: CtxtVanilla _ :: (CtxtSeqBlock _ as limitCtxt) :: _)
            | (CtxtSeqBlock _),(CtxtParen ((BEGIN | LPAREN | LBRACE | LBRACK | LBRACK_BAR)      ,_) :: CtxtSeqBlock _ :: ((CtxtTypeDefns _ | CtxtLetDecl _ | CtxtWithAsLet _) as limitCtxt) ::  _)
                        -> {position = start_pos limitCtxt; column = start_col limitCtxt + 1}
            | (CtxtIf   _ | CtxtElse _ | CtxtThen _), (CtxtIf _ as limitCtxt) :: _rest
                        -> {position = start_pos limitCtxt; column = start_col limitCtxt}
            | _,((CtxtModuleHead _ (*| CtxtException _ *)| CtxtModuleBody (_,false) | CtxtIf _ | CtxtWithAsLet _ | CtxtLetDecl _) as limitCtxt :: _)
                        -> {position = start_pos limitCtxt; column = start_col limitCtxt + 1}
            | _,((CtxtParen _ | CtxtWhen _ | CtxtTypeDefns _ | CtxtMatch _  | CtxtModuleBody (_,true) | CtxtTry _ | CtxtMatchClauses _ | CtxtSeqBlock _) as limitCtxt :: _)
                        -> {position = start_pos limitCtxt; column = start_col limitCtxt} in
        offsideStack := newCtxt :: !offsideStack in
    let popCtxt() =
        match !offsideStack with
        | [] -> ()
        | h :: rest ->
            offsideStack := rest in
    let replaceCtxt p ctxt =
        popCtxt();
        pushCtxt p ctxt in
    let peekNextTokenTup() =
        let tokenTup = popNextTokenTup() in
        delayToken tokenTup;
        tokenTup in
    let peekNextToken() =
        (peekNextTokenTup()).token in
    let returnToken (tokenLexbufState:lexbufState) tok =
        setLexbufState(tokenLexbufState);
        prevWasAtomicEnd := isAtomicExprEndToken(tok);
        tok in
    let rec hwTokenFetch (useBlockRule) =
        let tokenTup = popNextTokenTup() in
        let tokenStartPos = (startPosOfTokenTup tokenTup) in
        let token = tokenTup.token in
        let tokenLexbufState = tokenTup.lexbufState in
        let tokenStartCol = (tokenStartPos.pos_cnum - tokenStartPos.pos_bol) in
        let isSameLine() =
            match token with
            | EOF _ -> false
            | _ -> (startPosOfTokenTup (peekNextTokenTup())).pos_lnum = tokenStartPos.pos_lnum in
        let isControlFlowOrNotSameLine() =
            match token with
            | EOF _ -> false
            | _ ->
                not (isSameLine()) ||
                (match peekNextToken() with TRY | MATCH | IF | LET _ (*| FOR | WHILE *) -> true | _ -> false) in
        let rec isLongIdentEquals token =
            (match token with
            | IDENT _ ->
                let rec loop() =
                    let tokenTup = popNextTokenTup() in
                    let res =
                       (match tokenTup.token with
                        | EOF _ -> false
                        | DOT ->
                            let tokenTup = popNextTokenTup() in
                            let res =
                               (match tokenTup.token with
                                | EOF _ -> false
                                | IDENT _ -> loop()
                                | _ -> false) in
                            delayToken tokenTup;
                            res
                        | EQUALS ->
                            true
                        | _ -> false) in
                    delayToken tokenTup;
                    res in
                loop()
            | _ -> false) in
        let reprocess() =
            delayToken tokenTup;
            hwTokenFetch(useBlockRule) in
        let reprocessWithoutBlockRule() =
            delayToken tokenTup;
            hwTokenFetch(false) in
        let insertTokenFromPrevPosToCurrentPos tok =
            delayToken tokenTup;
            let lastTokenPos =
                let pos = tokenTup.lastTokenPos.y in
                (* pos.ShiftColumnBy 1 in *)
                shiftColumnBy pos 1 in
            returnToken (lexbufStateForInsertedDummyTokens (lastTokenPos, tokenTup.lexbufState.startPos)) tok in
        let insertToken tok =
            delayToken tokenTup;
            returnToken (lexbufStateForInsertedDummyTokens (startPosOfTokenTup tokenTup, tokenTup.lexbufState.endPos)) tok in
        let isSemiSemi = (match token with SEMICOLON_SEMICOLON -> true | _ -> false) in
        let endTokenForACtxt ctxt =
            match ctxt with
            | CtxtFun _
            | CtxtMatchClauses _
            | CtxtWithAsLet _      ->
                Some OEND
            | CtxtLetDecl (true,_) ->
                Some ODECLEND
            | CtxtSeqBlock(_,_,AddBlockEnd) ->
                Some OBLOCKEND
            | CtxtSeqBlock(_,_,AddOneSidedBlockEnd) ->
                Some ORIGHT_BLOCK_END
            | _ ->
                None in
        let tokenBalancesHeadContext token stack =
            match token,stack with
            | ELSE, (CtxtIf _ :: _)
            | WITH         , (  ((CtxtMatch _ (*CtxtException _ | CtxtMemberHead _ | CtxtInterfaceHead _ *)| CtxtTry _ | CtxtTypeDefns _ (*| CtxtMemberBody _*))  :: _)
                                    | (CtxtSeqBlock _ :: CtxtParen(LBRACE,_)  :: _) ) ->
                true
            | IN           , (((*CtxtFor _ |*) CtxtLetDecl _) :: _) ->
                true
            | SEMICOLON_SEMICOLON, (CtxtSeqBlock _ :: CtxtModuleBody (_,true) :: _) ->
                true
            | t2           , (CtxtParen(t1,_) :: _) ->
                parenTokensBalance t1  t2
            | _ ->
                false in
        let rec suffixExists p l = match l with [] -> false | _::t -> p t || suffixExists p t in
        let nonNil x = match x with [] -> false | _ -> true in
        let tokenForcesHeadContextClosure token stack =
            nonNil stack &&
            match token with
            | EOF _ -> true
            | SEMICOLON_SEMICOLON  -> not (tokenBalancesHeadContext token stack)
            | END
            | ELSE
            | IN
            | RPAREN
            | RBRACE
            | RBRACK
            | BAR_RBRACK
            | WITH ->
                not (tokenBalancesHeadContext token stack) &&
                (stack |> suffixExists (tokenBalancesHeadContext token))
            | _ -> false in
        match token, !offsideStack with
        | _ when !tokensThatNeedNoProcessingCount > 0 ->
            tokensThatNeedNoProcessingCount := !tokensThatNeedNoProcessingCount - 1;
            returnToken tokenLexbufState token
        |  _  when tokenForcesHeadContextClosure token !offsideStack ->
            let ctxt = List.hd !offsideStack in
            popCtxt();
            (match endTokenForACtxt ctxt with
            | Some tok ->
                insertToken tok;
            | _ ->
                reprocess())
        |  IN, (CtxtLetDecl (blockLet,offsidePos) :: _) ->
            popCtxt();
            delayToken(useLocation tokenTup (ODUMMY token));
            returnToken tokenLexbufState (if blockLet then ODECLEND else token)
        |  ((END | RPAREN | RBRACE | RBRACK | BAR_RBRACK (*| GREATER true*)) as t2), (CtxtParen (t1,_) :: _)
                when parenTokensBalance t1 t2  ->
            popCtxt();
            delayToken(useLocation tokenTup (ODUMMY token));
            returnToken tokenLexbufState token
        | _, (CtxtModuleHead (moduleTokenPos,prevToken) :: _)  ->
            (match prevToken, token with
            | _ ->
                popCtxt();
                (match tokenTup.token with
                | EOF _ ->
                    returnToken tokenLexbufState token
                | _ ->
                    delayToken tokenTup;
                    pushCtxt tokenTup (CtxtModuleBody (moduleTokenPos,true));
                    pushCtxtSeqBlockAt (tokenTup, false, NoAddBlockEnd);
                    hwTokenFetch(false)))
        | _, (CtxtSeqBlock(_,offsidePos,addBlockEnd) :: rest) when
                ((isSemiSemi && not (match rest with (CtxtModuleBody (_,true)) :: _ -> true | _ -> false)) ||
                    let grace =
                        (match token, rest with
                        | BAR, (CtxtTypeDefns _ :: _) -> 2
                        | _, (CtxtTypeDefns posType :: _) when (offsidePos.pos_cnum - offsidePos.pos_bol) = posType.pos_bol && not (isTypeSeqBlockElementContinuator token) -> -1
                        | _ ->
                            (if isInfix token then infixTokenLength token + 1 else 0)) in
                    (tokenStartCol + grace < (offsidePos.pos_cnum - offsidePos.pos_bol))) ->
            popCtxt();
            (match addBlockEnd with
            | AddBlockEnd -> insertToken OBLOCKEND
            | AddOneSidedBlockEnd -> insertToken ORIGHT_BLOCK_END
            | NoAddBlockEnd -> reprocess())
        | _, (CtxtVanilla(offsidePos,_) :: _) when isSemiSemi || tokenStartCol <= (offsidePos.pos_cnum - offsidePos.pos_bol) ->
            popCtxt();
            reprocess()
        | _, (CtxtSeqBlock (FirstInSeqBlock,offsidePos,addBlockEnd) :: _) when useBlockRule ->
            replaceCtxt tokenTup (CtxtSeqBlock (NotFirstInSeqBlock,offsidePos,addBlockEnd));
            reprocessWithoutBlockRule()
        | _, (CtxtSeqBlock (NotFirstInSeqBlock,offsidePos,addBlockEnd) :: rest)
                when  useBlockRule
                    && not (let isTypeCtxt = (match rest with | (CtxtTypeDefns _ :: _) -> true | _ -> false) in
                            (if isTypeCtxt then isTypeSeqBlockElementContinuator token
                            else isSeqBlockElementContinuator  token))
                    && (tokenStartCol = (offsidePos.pos_cnum - offsidePos.pos_bol))
                    && (tokenStartPos.pos_lnum <> offsidePos.pos_lnum) ->
                replaceCtxt tokenTup (CtxtSeqBlock (FirstInSeqBlock,offsidePos,addBlockEnd));
                insertTokenFromPrevPosToCurrentPos OBLOCKSEP
        | _, (CtxtLetDecl (true,offsidePos) :: _) when
                        isSemiSemi || (if isLetContinuator token then tokenStartCol + 1 else tokenStartCol) <= (offsidePos.pos_cnum - offsidePos.pos_bol) ->
            popCtxt();
            insertToken ODECLEND
        | _, (CtxtTypeDefns offsidePos :: _)
                when isSemiSemi || (if isTypeContinuator token then tokenStartCol + 1 else tokenStartCol) <= (offsidePos.pos_cnum - offsidePos.pos_bol) ->
            popCtxt();
            reprocess()
        | _, ((CtxtModuleBody (offsidePos,wholeFile)) :: _) when (isSemiSemi && not wholeFile) ||  tokenStartCol <= (offsidePos.pos_cnum - offsidePos.pos_bol) ->
            popCtxt();
            reprocess()
        | _, (CtxtIf offsidePos :: _)
                    when isSemiSemi || (if isIfBlockContinuator token then  tokenStartCol + 1 else tokenStartCol) <= (offsidePos.pos_cnum - offsidePos.pos_bol) ->
            popCtxt();
            reprocess()
        | _, (CtxtMatch offsidePos :: _)
                    when isSemiSemi || tokenStartCol <= (offsidePos.pos_cnum - offsidePos.pos_bol) ->
            popCtxt();
            reprocess()
        | _, (CtxtWhen offsidePos :: _)
                    when isSemiSemi || tokenStartCol <= (offsidePos.pos_cnum - offsidePos.pos_bol) ->
            popCtxt();
            reprocess()
        | _, (CtxtFun offsidePos :: _)
                    when isSemiSemi || tokenStartCol <= (offsidePos.pos_cnum - offsidePos.pos_bol) ->
            popCtxt();
            insertToken OEND
        | _, (CtxtFunction offsidePos :: _)
                    when isSemiSemi || tokenStartCol <= (offsidePos.pos_cnum - offsidePos.pos_bol) ->
            popCtxt();
            reprocess()
        | _, (CtxtTry offsidePos :: _)
                    when isSemiSemi || (if isTryBlockContinuator token then  tokenStartCol + 1 else tokenStartCol) <= (offsidePos.pos_cnum - offsidePos.pos_bol) ->
            popCtxt();
            reprocess()
        | _, (CtxtThen offsidePos :: _) when isSemiSemi ||  (if isThenBlockContinuator token then  tokenStartCol + 1 else tokenStartCol)<= (offsidePos.pos_cnum - offsidePos.pos_bol) ->
            popCtxt();
            reprocess()
        | _, (CtxtElse (offsidePos) :: _) when isSemiSemi || tokenStartCol <= (offsidePos.pos_cnum - offsidePos.pos_bol) ->
            popCtxt();
            reprocess()
        | _, (CtxtMatchClauses (leadingBar,offsidePos) :: _)
                  when (isSemiSemi ||
                        (match token with
                            | BAR ->
                                let cond1 = tokenStartCol + (if leadingBar then 0 else 2)  < (offsidePos.pos_cnum - offsidePos.pos_bol) in
                                let cond2 = tokenStartCol + (if leadingBar then 1 else 2)  < (offsidePos.pos_cnum - offsidePos.pos_bol) in
                                if (cond1 <> cond2) then
                                    pr "Error";
                                cond1
                            | END -> tokenStartCol + (if leadingBar then -1 else 1) < (offsidePos.pos_cnum - offsidePos.pos_bol)
                            | _   -> tokenStartCol + (if leadingBar then -1 else 1) < (offsidePos.pos_cnum - offsidePos.pos_bol))) ->
            popCtxt();
            insertToken OEND
        |  MODULE,(_ :: _) ->
            pushCtxt tokenTup (CtxtModuleHead (tokenStartPos, token));
            delayTokenNoProcessing tokenTup;
            hwTokenFetch(useBlockRule)
        | LET(isUse), (ctxt :: _) ->
            let blockLet = (match ctxt with | CtxtSeqBlock _ -> true
                                            | CtxtMatchClauses _ -> true
                                            | _ -> false) in
            pushCtxt tokenTup (CtxtLetDecl(blockLet,tokenStartPos));
            returnToken tokenLexbufState (if blockLet then OLET(isUse) else token)
        | EQUALS, (CtxtLetDecl _ :: _) ->
            pushCtxtSeqBlock(true,AddBlockEnd);
            returnToken tokenLexbufState token
        | EQUALS, (CtxtTypeDefns _ :: _) ->
            pushCtxtSeqBlock(true,AddBlockEnd);
            returnToken tokenLexbufState token
        | (BEGIN | LPAREN (*| SIG *)| LBRACE | LBRACK | LBRACK_BAR (*| LQUOTE _ | LESS true*)), _ ->
            pushCtxt tokenTup (CtxtParen (token,tokenStartPos));
            pushCtxtSeqBlock(false,NoAddBlockEnd);
            returnToken tokenLexbufState token
        | RARROW, ctxts
                when (match ctxts with
                        | ((*CtxtWhile _ | CtxtFor _ |*) CtxtWhen _ | CtxtMatchClauses _ | CtxtFun _) :: _ -> true
                        | (CtxtSeqBlock _ :: CtxtParen ((LBRACK | LBRACE | LBRACK_BAR), _) :: _) -> true
                        | (CtxtSeqBlock _ :: ((*CtxtDo _ | CtxtWhile _ | CtxtFor _ |*) CtxtWhen _ | CtxtMatchClauses _  | CtxtTry _ | CtxtThen _ | CtxtElse _) :: _) -> true
                        | _ -> false) ->
            pushCtxtSeqBlock(false,AddOneSidedBlockEnd);
            returnToken tokenLexbufState token
        | LARROW, _  when isControlFlowOrNotSameLine() ->
            pushCtxtSeqBlock(true,AddBlockEnd);
            returnToken tokenLexbufState token
        | _, ctxts when (isInfix token &&
                            not (isSameLine()) &&
                            (match ctxts with CtxtMatchClauses _ :: _ -> false | _ -> true)) ->
            pushCtxtSeqBlock(false,NoAddBlockEnd);
            returnToken tokenLexbufState token
        | WITH, ((CtxtTry _ | CtxtMatch _) :: _)  ->
            let lookaheadTokenTup = peekNextTokenTup() in
            let lookaheadTokenStartPos = startPosOfTokenTup lookaheadTokenTup in
            let leadingBar = (match (peekNextToken()) with BAR -> true | _ -> false) in
            pushCtxt lookaheadTokenTup (CtxtMatchClauses(leadingBar,lookaheadTokenStartPos));
            returnToken tokenLexbufState OWITH
        | FUNCTION, _  ->
            let lookaheadTokenTup = peekNextTokenTup() in
            let lookaheadTokenStartPos = startPosOfTokenTup lookaheadTokenTup in
            let leadingBar = (match (peekNextToken()) with BAR -> true | _ -> false) in
            pushCtxt tokenTup (CtxtFunction(tokenStartPos));
            pushCtxt lookaheadTokenTup (CtxtMatchClauses(leadingBar,lookaheadTokenStartPos));
            returnToken tokenLexbufState OFUNCTION
        | THEN,_  ->
            pushCtxt tokenTup (CtxtThen(tokenStartPos));
            pushCtxtSeqBlock(true,AddBlockEnd);
            returnToken tokenLexbufState OTHEN
        | ELSE, _   ->
            let lookaheadTokenTup = peekNextTokenTup() in
            let lookaheadTokenStartPos = startPosOfTokenTup lookaheadTokenTup in
            (match peekNextToken() with
            | _ ->
                pushCtxt tokenTup (CtxtElse(tokenStartPos));
                pushCtxtSeqBlock(true,AddBlockEnd);
                returnToken tokenLexbufState OELSE)
        | IF, _   ->
            pushCtxt tokenTup (CtxtIf (tokenStartPos));
            returnToken tokenLexbufState token
        | MATCH, _   ->
            pushCtxt tokenTup (CtxtMatch (tokenStartPos));
            returnToken tokenLexbufState token
        | WHEN, ((CtxtSeqBlock _) :: _)  ->
            pushCtxt tokenTup (CtxtWhen (tokenStartPos));
            returnToken tokenLexbufState token
        | FUN, _   ->
            pushCtxt tokenTup (CtxtFun (tokenStartPos));
            returnToken tokenLexbufState OFUN
        | TYPE, _   ->
            pushCtxt tokenTup (CtxtTypeDefns(tokenStartPos));
            delayTokenNoProcessing tokenTup;
            hwTokenFetch(useBlockRule)
        | TRY, _   ->
            pushCtxt tokenTup (CtxtTry (tokenStartPos));
            pushCtxtSeqBlock(false,AddOneSidedBlockEnd);
            returnToken tokenLexbufState token
        |  OBLOCKBEGIN,_ ->
            returnToken tokenLexbufState token
        |  ODUMMY(_),_ ->
            hwTokenFetch (useBlockRule)
        |  _,CtxtSeqBlock _ :: _ ->
            pushCtxt tokenTup (CtxtVanilla(tokenStartPos, isLongIdentEquals token));
            returnToken tokenLexbufState token
        |  _ ->
            returnToken tokenLexbufState token
    and pushCtxtSeqBlock(addBlockBegin,addBlockEnd) = pushCtxtSeqBlockAt (peekNextTokenTup(),addBlockBegin,addBlockEnd)
    and pushCtxtSeqBlockAt((p:tokenTup),addBlockBegin,addBlockEnd) =
         if addBlockBegin then
            delayToken(useLocation p OBLOCKBEGIN);
         pushCtxt p (CtxtSeqBlock(FirstInSeqBlock, startPosOfTokenTup p,addBlockEnd)) in
    fun _ ->
        (if use_light () && not !initialized then
            let _firstTokenTup = peekInitial() in
            ());
        let tok = if use_light () then (hwTokenFetch true) else lexer lexbuf in
        tok
