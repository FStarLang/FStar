module Negotiation.Writers.Aux2

friend Parsers.ExtensionType
friend Parsers.ClientHelloExtension

module LWP = LowParseWriters.Compat
module LP = LowParse.Spec

#set-options "--z3rlimit 32" // necessary due to cluttered context (too many `friend`s)


inline_for_extraction
noextract
let che_dsum =
  let open Parsers.ClientHelloExtension in
  let open Parsers.ExtensionType in
  let open LWP in {
    dsum_kt = _;
    dsum_t = clientHelloExtension_sum;
    dsum_p = extensionType_repr_parser;
    dsum_s = extensionType_repr_serializer;
    dsum_pc = parse_clientHelloExtension_cases;
    dsum_sc = serialize_clientHelloExtension_cases;
    dsum_ku = _;
    dsum_pu = clientHelloExtension_CHE_default_parser;
    dsum_su = clientHelloExtension_CHE_default_serializer;
  }

inline_for_extraction
noextract
let che_enum : LWP.pparser _ _ _ (LP.serialize_maybe_enum_key _ che_dsum.LWP.dsum_s (LP.dsum_enum che_dsum.LWP.dsum_t)) =
  LWP.parse_maybe_enum
    LWP.parse_u16
    (LP.dsum_enum che_dsum.LWP.dsum_t)

#push-options "--z3rlimit 128"

#restart-solver

let valid_rewrite_constr_clientHelloExtension
  (k: Parsers.ExtensionType.extensionType { LP.list_mem k (LP.list_map fst Parsers.ExtensionType.extensionType_enum) })
  (p: LWP.pparser
       (Parsers.ClientHelloExtension.clientHelloExtension_case_of_extensionType k)
       _
       (dsnd (Parsers.ClientHelloExtension.parse_clientHelloExtension_cases k))
       (Parsers.ClientHelloExtension.serialize_clientHelloExtension_cases k)
  )
: Tot (LWP.valid_rewrite_t
  (Parsers.ExtensionType.lwp_extensionType `LWP.parse_pair` p)
  Parsers.ClientHelloExtension.lwp_clientHelloExtension
  (fun (k', _) -> k' == k)
  (fun (_, ext) -> Parsers.ClientHelloExtension.synth_known_clientHelloExtension_cases k ext)
)
=
  let open Parsers.ClientHelloExtension in
  let open Parsers.ExtensionType in
  assert_norm (LP.parse_dsum_kind (LP.get_parser_kind extensionType_repr_parser) clientHelloExtension_sum parse_clientHelloExtension_cases (LP.get_parser_kind clientHelloExtension_CHE_default_parser) == clientHelloExtension_parser_kind);
  lemma_synth_extensionType_inj ();
  lemma_synth_extensionType_inv ();
  LWP.valid_rewrite_implies _ _ _ _
  (LWP.valid_rewrite_compose
    _ _ _ _
    (LWP.valid_rewrite_parse_pair_compat_r
      _ _ _ _ _
      (LWP.valid_rewrite_compose
        _ _ _ _
        (LWP.valid_rewrite_parser_eq _ _)
        _ _ _
        (LWP.valid_rewrite_parse_synth_recip che_enum synth_extensionType synth_extensionType_inv ())
      )
    )
    _ _ _
    (LWP.valid_rewrite_parse_dsum_known
      che_dsum
      _
      _
      k
      _
    )
  )
  _ _

#pop-options

#restart-solver

let valid_rewrite_constr_clientHelloExtension_CHE_pre_shared_key =
  let open Parsers.ClientHelloExtension in
  let open Parsers.ExtensionType in
  assert_norm (LP.list_mem Pre_shared_key (LP.list_map fst extensionType_enum) == true);
  LWP.valid_rewrite_implies _ _ _ _
    (valid_rewrite_constr_clientHelloExtension Pre_shared_key lwp_clientHelloExtension_CHE_pre_shared_key)
    _ _

let valid_rewrite_constr_clientHelloExtension_CHE_psk_key_exchange_modes =
  let open Parsers.ClientHelloExtension in
  let open Parsers.ExtensionType in
  assert_norm (LP.list_mem Psk_key_exchange_modes (LP.list_map fst extensionType_enum) == true);
  LWP.valid_rewrite_implies _ _ _ _
    (valid_rewrite_constr_clientHelloExtension Psk_key_exchange_modes lwp_clientHelloExtension_CHE_psk_key_exchange_modes)
    _ _

let valid_rewrite_constr_clientHelloExtension_CHE_early_data =
  let open Parsers.ClientHelloExtension in
  let open Parsers.ExtensionType in
  assert_norm (LP.list_mem Early_data (LP.list_map fst extensionType_enum) == true);
  LWP.valid_rewrite_implies _ _ _ _
    (valid_rewrite_constr_clientHelloExtension Early_data lwp_clientHelloExtension_CHE_early_data)
    _ _

let valid_rewrite_constr_clientHelloExtension_CHE_key_share =
  let open Parsers.ClientHelloExtension in
  let open Parsers.ExtensionType in
  assert_norm (LP.list_mem Key_share (LP.list_map fst extensionType_enum) == true);
  LWP.valid_rewrite_implies _ _ _ _
    (valid_rewrite_constr_clientHelloExtension Key_share lwp_clientHelloExtension_CHE_key_share)
    _ _

let valid_rewrite_constr_clientHelloExtension_CHE_server_name =
  let open Parsers.ClientHelloExtension in
  let open Parsers.ExtensionType in
  assert_norm (LP.list_mem Server_name (LP.list_map fst extensionType_enum) == true);
  LWP.valid_rewrite_implies _ _ _ _
    (valid_rewrite_constr_clientHelloExtension Server_name lwp_clientHelloExtension_CHE_server_name)
    _ _

friend Parsers.ServerNameList

let valid_serverNameList_intro =
  let open Parsers.ServerName in
  let open Parsers.ServerNameList in
  Classical.forall_intro serverName_bytesize_eq;
  LWP.valid_rewrite_implies _ _ _ _
    (LWP.valid_rewrite_compose
      _ _ _ _
      (LWP.valid_rewrite_parse_synth (LWP.parse_vllist lwp_serverName 1ul 65535ul) synth_serverNameList synth_serverNameList_recip ())
      _ _ _
      (LWP.valid_rewrite_parser_eq _ _)
    )
  _ _
