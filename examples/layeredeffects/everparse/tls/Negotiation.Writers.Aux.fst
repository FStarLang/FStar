module Negotiation.Writers.Aux

friend Parsers.PskBinderEntry
friend Parsers.PskIdentity
friend Parsers.OfferedPsks_identities
friend Parsers.OfferedPsks_binders
friend Parsers.OfferedPsks
friend Parsers.ClientHelloExtension_CHE_pre_shared_key
friend Parsers.PskKeyExchangeModes
friend Parsers.ClientHelloExtension_CHE_psk_key_exchange_modes
friend Parsers.ClientHelloExtension_CHE_early_data
friend Parsers.ServerName
friend Parsers.NameType
friend Parsers.ClientHelloExtension_CHE_server_name

module LWP = LowParseWriters.Compat
module LP = LowParse.Spec

let valid_pskBinderEntry_intro =
   [@inline_let] let _ = assert_norm (Parsers.PskBinderEntry.pskBinderEntry == LowParse.Spec.Bytes.parse_bounded_vlbytes_t 32 255) in
   LWP.valid_rewrite_parser_eq (LWP.parse_vlbytes 32ul 255ul) Parsers.PskBinderEntry.lwp_pskBinderEntry

let valid_pskBinderEntry_elim =
   [@inline_let] let _ = assert_norm (Parsers.PskBinderEntry.pskBinderEntry == LowParse.Spec.Bytes.parse_bounded_vlbytes_t 32 255) in
   LWP.valid_rewrite_parser_eq Parsers.PskBinderEntry.lwp_pskBinderEntry (LWP.parse_vlbytes 32ul 255ul)

let valid_pskIdentity_intro =
  let open Parsers.PskIdentity in
  assert_norm (pskIdentity' == LP.get_parser_type pskIdentity'_parser);
  assert_norm (pskIdentity_parser_kind == pskIdentity'_parser_kind);
  synth_pskIdentity_injective ();
  synth_pskIdentity_inverse ();
  LWP.valid_rewrite_implies _ _ _ _
  (LWP.valid_rewrite_compose
    _ _ _ _
    (LWP.valid_rewrite_parse_synth (lwp_pskIdentity_identity `LWP.parse_pair` LWP.parse_u32) synth_pskIdentity synth_pskIdentity_recip ())
    _ _ _
    (LWP.valid_rewrite_parser_eq (LWP.parse_synth (lwp_pskIdentity_identity `LWP.parse_pair` LWP.parse_u32) synth_pskIdentity synth_pskIdentity_recip) lwp_pskIdentity)
  )
  _ _


let valid_offeredPsks_binders_intro =
  let open Parsers.OfferedPsks_binders in
  LWP.valid_rewrite_implies _ _ _ _
    (LWP.valid_rewrite_compose
      _ _ _ _
      (LWP.valid_rewrite_parse_synth (LWP.parse_vllist Parsers.PskBinderEntry.lwp_pskBinderEntry 33ul 65535ul) synth_offeredPsks_binders synth_offeredPsks_binders_recip ())
      _ _ _
      (LWP.valid_rewrite_parser_eq _ _)
    )
    _ _

let valid_offeredPsks_binders_elim =
  let open Parsers.OfferedPsks_binders in
  LWP.valid_rewrite_implies _ _ _ _
    (LWP.valid_rewrite_compose
      _ _ _ _
      (LWP.valid_rewrite_parser_eq _ _)
      _ _ _
      (LWP.valid_rewrite_parse_synth_recip (LWP.parse_vllist Parsers.PskBinderEntry.lwp_pskBinderEntry 33ul 65535ul) synth_offeredPsks_binders synth_offeredPsks_binders_recip ())
    )
    _ _

let valid_offeredPsks_identities_intro =
  let open Parsers.OfferedPsks_identities in
  LWP.valid_rewrite_implies _ _ _ _
    (LWP.valid_rewrite_compose
      _ _ _ _
      (LWP.valid_rewrite_parse_synth (LWP.parse_vllist Parsers.PskIdentity.lwp_pskIdentity 7ul 65535ul) synth_offeredPsks_identities synth_offeredPsks_identities_recip ())
      _ _ _
      (LWP.valid_rewrite_parser_eq _ _)
    )
    _ _

#set-options "--z3rlimit 16"

let valid_offeredPsks_identities_elim =
  let open Parsers.OfferedPsks_identities in
  LWP.valid_rewrite_implies _ _ _ _
    (LWP.valid_rewrite_compose
      _ _ _ _
      (LWP.valid_rewrite_parser_eq _ _)
      _ _ _
      (LWP.valid_rewrite_parse_synth_recip (LWP.parse_vllist Parsers.PskIdentity.lwp_pskIdentity 7ul 65535ul) synth_offeredPsks_identities synth_offeredPsks_identities_recip ())
    )
    _ _

let valid_offeredPsks_intro =
  let open Parsers.OfferedPsks in
  LWP.valid_rewrite_implies _ _ _ _
    (LWP.valid_rewrite_compose
      _ _ _ _
      (LWP.valid_rewrite_parse_synth (lwp_offeredPsks_identities `LWP.parse_pair` lwp_offeredPsks_binders) synth_offeredPsks synth_offeredPsks_recip ())
      _ _ _
      (LWP.valid_rewrite_parser_eq _ _)
    )
  _ _

let valid_clientHelloExtension_CHE_pre_shared_key_intro =
  let open Parsers.ClientHelloExtension_CHE_pre_shared_key in
  Classical.forall_intro Parsers.PreSharedKeyClientExtension.preSharedKeyClientExtension_bytesize_eq;
  LWP.valid_rewrite_implies _ _ _ _
    (LWP.valid_rewrite_compose
      _ _ _ _
      (LWP.valid_rewrite_parse_synth (LWP.parse_vldata Parsers.PreSharedKeyClientExtension.lwp_preSharedKeyClientExtension 0ul 65535ul) synth_clientHelloExtension_CHE_pre_shared_key synth_clientHelloExtension_CHE_pre_shared_key_recip ())
      _ _ _
      (LWP.valid_rewrite_parser_eq _ _)
    )
  _ _

let valid_rewrite_pskKeyExchangeModes_intro =
//  [@inline_let] let _ = assert_norm (LP.vldata_vlarray_precond 1 255 Parsers.PskKeyExchangeMode.pskKeyExchangeMode_parser 1 255 == true) in
  LWP.valid_rewrite_parse_vlarray_intro
    _
    Parsers.PskKeyExchangeMode.lwp_pskKeyExchangeMode
    1ul 255ul 1 255 ()

let valid_rewrite_pskKeyExchangeModes_elim =
  LWP.valid_rewrite_parse_vlarray_elim
    _
    Parsers.PskKeyExchangeMode.lwp_pskKeyExchangeMode
    1ul 255ul 1 255 ()

let valid_clientHelloExtension_CHE_psk_key_exchange_modes_intro =
  LWP.valid_rewrite_parse_bounded_vldata_intro _ _ _ _

let valid_clientHelloExtension_CHE_early_data_intro =
  LWP.valid_rewrite_parse_bounded_vldata_intro _ _ _ _

inline_for_extraction
noextract
let sni_dsum =
  let open Parsers.ServerName in
  let open Parsers.UnknownName in
  let open Parsers.NameType in
  let open LWP in {
    dsum_kt = _;
    dsum_t = serverName_sum;
    dsum_p = nameType_repr_parser;
    dsum_s = nameType_repr_serializer;
    dsum_pc = parse_serverName_cases;
    dsum_sc = serialize_serverName_cases;
    dsum_ku = _;
    dsum_pu = unknownName_parser;
    dsum_su = unknownName_serializer;
  }

inline_for_extraction
noextract
let sni_enum : LWP.pparser _ _ _ (LP.serialize_maybe_enum_key _ sni_dsum.LWP.dsum_s (LP.dsum_enum sni_dsum.LWP.dsum_t)) =
  LWP.parse_maybe_enum
    LWP.parse_u8
    (LP.dsum_enum sni_dsum.LWP.dsum_t)

let valid_rewrite_constr_sni
  (k: Parsers.NameType.nameType { LP.list_mem k (LP.list_map fst Parsers.NameType.nameType_enum) })
  (p: LWP.pparser
       (Parsers.ServerName.serverName_case_of_nameType k)
       _
       (dsnd (Parsers.ServerName.parse_serverName_cases k))
       (Parsers.ServerName.serialize_serverName_cases k)
  )
: Tot (LWP.valid_rewrite_t
  (Parsers.NameType.lwp_nameType `LWP.parse_pair` p)
  Parsers.ServerName.lwp_serverName
  (fun (k', _) -> k' == k)
  (fun (_, ext) -> Parsers.ServerName.synth_known_serverName_cases k ext)
)
=
  let open Parsers.ServerName in
  let open Parsers.NameType in
  let open Parsers.UnknownName in
  assert_norm (LP.parse_dsum_kind (LP.get_parser_kind nameType_repr_parser) serverName_sum parse_serverName_cases (LP.get_parser_kind unknownName_parser) == serverName_parser_kind);
  lemma_synth_nameType_inj ();
  lemma_synth_nameType_inv ();
  LWP.valid_rewrite_implies _ _ _ _
  (LWP.valid_rewrite_compose
    _ _ _ _
    (LWP.valid_rewrite_parse_pair_compat_r
      _ _ _ _ _
      (LWP.valid_rewrite_compose
        _ _ _ _
        (LWP.valid_rewrite_parser_eq _ _)
        _ _ _
        (LWP.valid_rewrite_parse_synth_recip sni_enum synth_nameType synth_nameType_inv ())
      )
    )
    _ _ _
    (LWP.valid_rewrite_parse_dsum_known
      sni_dsum
      _
      _
      k
      _
    )
  )
  _ _

let valid_rewrite_constr_sni_host_name =
  let open Parsers.ServerName in
  let open Parsers.HostName in
  let open Parsers.NameType in
  assert_norm (LP.list_mem Host_name (LP.list_map fst nameType_enum) == true);
  LWP.valid_rewrite_implies _ _ _ _
    (valid_rewrite_constr_sni Host_name lwp_hostName)
    _ _

let valid_clientHelloExtension_CHE_server_name_intro =
  let open Parsers.ClientHelloExtension_CHE_server_name in
  Classical.forall_intro Parsers.ServerNameList.serverNameList_bytesize_eq;
  LWP.valid_rewrite_implies _ _ _ _
    (LWP.valid_rewrite_compose
      _ _ _ _
      (LWP.valid_rewrite_parse_synth (LWP.parse_vldata Parsers.ServerNameList.lwp_serverNameList 0ul 65535ul) synth_clientHelloExtension_CHE_server_name synth_clientHelloExtension_CHE_server_name_recip ())
      _ _ _
      (LWP.valid_rewrite_parser_eq _ _)
    )
  _ _
