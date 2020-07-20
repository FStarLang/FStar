module Negotiation.Writers.NoHoare

module LWP = LowParseWriters.NoHoare.Parsers
module Aux = Negotiation.Writers.NoHoare.Aux
module Aux2 = Negotiation.Writers.NoHoare.Aux2

#reset-options "--z3cliopt smt.arith.nl=false"

open TLSConstants
open Extensions
open Negotiation


module U32 = FStar.UInt32
module B = LowStar.Buffer

#push-options "--z3rlimit 16 --query_stats"

inline_for_extraction
noextract
let compute_binder_ph1
  (inv: LWP.memory_invariant)
  (tc: LWP.ptr Parsers.TicketContents13.lwp_ticketContents13 inv)
  ()
: LWP.TWrite unit LWP.parse_empty lwp_pskBinderEntry inv
=
  let cs = Parsers.TicketContents13.lwps_accessor_ticketContents13_cs tc in
  let c = LWP.deref CipherSuite.cipherSuite13_reader cs in
  let (CipherSuite13 _ h) = cipherSuite_of_cipherSuite13 c in
  let len : U32.t = Hacl.Hash.Definitions.hash_len h in
  LWP.put_vlbytes 32ul 255ul len (Seq.create (U32.v len) 0uy) (fun b ->
    B.fill b 0uy len
  )
  
 // ; LWP.valid_rewrite Aux.valid_pskBinderEntry_intro' // automatic thanks to subcomp

noextract
let compute_binder_ph2 = compute_binder_ph1 // to avoid inline_for_extraction in effect indices, implicit args, etc.

// this will be extracted as a C function
let extract_compute_binder
  (inv: LWP.memory_invariant)
  (tc: LWP.ptr Parsers.TicketContents13.lwp_ticketContents13 inv)
: Tot (LWP.extract_t inv (compute_binder_ph2 inv tc))
= LWP.extract _ (compute_binder_ph1 inv tc)

// this will be inlined as an explicit function call
inline_for_extraction
noextract
let compute_binder_ph
  (#inv: LWP.memory_invariant)
  (tc: LWP.ptr Parsers.TicketContents13.lwp_ticketContents13 inv)
: LWP.TWrite unit LWP.parse_empty lwp_pskBinderEntry inv
= LWP.wrap_extracted_impl _ _ (extract_compute_binder inv tc)

inline_for_extraction
noextract
let obfuscate_age1
  (inv: LWP.memory_invariant)
  (now: U32.t)
  (ri: LWP.ptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
  ()
: LWP.TWrite unit LWP.parse_empty Parsers.PskIdentity.lwp_pskIdentity inv
=
  let id = Parsers.ResumeInfo13.lwps_accessor_resumeInfo13_identity ri in
  LWP.cat id;
  let tk = Parsers.ResumeInfo13.lwps_accessor_resumeInfo13_ticket ri in
  let ct = Parsers.TicketContents13.lwps_accessor_ticketContents13_creation_time tk in
  let creation_time = LWP.deref LowParse.Low.Int.read_u32 ct in
  let age = FStar.UInt32.((now -%^ creation_time) *%^ 1000ul) in
  let aa = Parsers.TicketContents13.lwps_accessor_ticketContents13_age_add tk in
  let age_add = LWP.deref LowParse.Low.Int.read_u32 aa in
  let obfuscated_age = PSK.encode_age age age_add in
  LWP.append LWP.parse_u32 LowParse.Low.Int.write_u32 obfuscated_age;
  LWP.valid_rewrite Aux.valid_pskIdentity_intro'

noextract
let obfuscate_age2 = obfuscate_age1

let extract_obfuscate_age
  (inv: LWP.memory_invariant)
  (now: U32.t)
  (ri: LWP.ptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
: Tot (LWP.extract_t inv (obfuscate_age2 inv now ri))
= LWP.extract inv (obfuscate_age1 inv now ri)

inline_for_extraction
noextract
let obfuscate_age
  (#inv: LWP.memory_invariant)
  (now: U32.t)
  (ri: LWP.ptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
: LWP.TWrite unit LWP.parse_empty Parsers.PskIdentity.lwp_pskIdentity inv
= LWP.wrap_extracted_impl _ _ (extract_obfuscate_age inv now ri)


inline_for_extraction
noextract
let write_psk_key_exchange_modes1
  (inv: LWP.memory_invariant)
  (_: unit)
: LWP.TWrite unit LWP.parse_empty Parsers.ClientHelloExtension.lwp_clientHelloExtension inv
=
  Aux2.constr_clientHelloExtension_CHE_psk_key_exchange_modes (fun _ ->
    LWP.parse_vldata_intro_weak_ho'
            Parsers.PskKeyExchangeModes.lwp_pskKeyExchangeModes 0ul 65535ul (fun _ ->
            let open Parsers.PskKeyExchangeMode in
            LWP.write_vllist_nil lwp_pskKeyExchangeMode 255ul;
            LWP.extend_vllist_snoc_ho lwp_pskKeyExchangeMode 0ul 255ul (fun _ ->
              LWP.start lwp_pskKeyExchangeMode pskKeyExchangeMode_writer Psk_ke
            );
            LWP.extend_vllist_snoc_ho lwp_pskKeyExchangeMode 0ul 255ul (fun _ ->
              LWP.start lwp_pskKeyExchangeMode pskKeyExchangeMode_writer Psk_dhe_ke
            );
            LWP.parse_vllist_recast _ _ _ 1ul 255ul;
            LWP.valid_rewrite
              Aux.valid_rewrite_pskKeyExchangeModes_intro'
        ) (* ;
          LWP.valid_rewrite
            Aux.valid_clientHelloExtension_CHE_psk_key_exchange_modes_intro'; // automatic thanks to subcomp
          () *)
  )

noextract
let write_psk_key_exchange_modes2 = write_psk_key_exchange_modes1

let extract_write_psk_key_exchange_modes
  (inv: LWP.memory_invariant)
: Tot (LWP.extract_t inv (write_psk_key_exchange_modes2 inv))
= LWP.extract _ (write_psk_key_exchange_modes1 inv)

inline_for_extraction
noextract
let write_psk_key_exchange_modes
  (#inv: LWP.memory_invariant)
  (_: unit)
: LWP.TWrite unit LWP.parse_empty Parsers.ClientHelloExtension.lwp_clientHelloExtension inv
= LWP.wrap_extracted_impl _ _ (extract_write_psk_key_exchange_modes inv)

#restart-solver

inline_for_extraction
noextract
let write_clientHelloExtension_CHE_early_data1
  (inv: LWP.memory_invariant)
  ()
: LWP.TWrite
    unit
    LWP.parse_empty
    Parsers.ClientHelloExtension.lwp_clientHelloExtension
    inv
=
  Aux2.constr_clientHelloExtension_CHE_early_data (fun _ ->
    LWP.parse_vldata_intro_weak_ho'
      LWP.parse_empty 0ul 65535ul (fun _ -> ());
    () // LWP.valid_rewrite Aux.valid_clientHelloExtension_CHE_early_data_intro' // automatic thanks to subcomp
  )

noextract
let write_clientHelloExtension_CHE_early_data2 = write_clientHelloExtension_CHE_early_data1

let extract_write_clientHelloExtension_CHE_early_data
  (inv: LWP.memory_invariant)
: Tot (LWP.extract_t inv (write_clientHelloExtension_CHE_early_data2 inv))
= LWP.extract inv (write_clientHelloExtension_CHE_early_data1 inv)

inline_for_extraction
noextract
let write_clientHelloExtension_CHE_early_data
  (#inv: LWP.memory_invariant)
  ()
: LWP.TWrite
    unit
    LWP.parse_empty
    Parsers.ClientHelloExtension.lwp_clientHelloExtension
    inv
= LWP.wrap_extracted_impl _ _ (extract_write_clientHelloExtension_CHE_early_data inv)

#restart-solver

inline_for_extraction
noextract
let write_psk_kex1
  (inv: LWP.memory_invariant)
  (allow_psk_resumption: bool)
  (allow_dhe_resumption: bool)
  ()
: LWP.TWrite
    unit
    LWP.parse_empty
    Parsers.ClientHelloExtension.lwp_clientHelloExtension
    inv
=
        Aux2.constr_clientHelloExtension_CHE_psk_key_exchange_modes (fun _ ->
          LWP.parse_vldata_intro_weak_ho' lwp_pskKeyExchangeModes 0ul 65535ul (fun _ ->
            LWP.write_vllist_nil lwp_pskKeyExchangeMode 255ul;
            if allow_psk_resumption
            then
              LWP.extend_vllist_snoc_ho _ _ _ (fun _ ->
                LWP.start _ pskKeyExchangeMode_writer Psk_ke
              );
            if allow_dhe_resumption
            then
              LWP.extend_vllist_snoc_ho _ _ _ (fun _ ->
                LWP.start _ pskKeyExchangeMode_writer Psk_dhe_ke
              );
            LWP.parse_vllist_recast _ _ _ 1ul 255ul;
            () // LWP.valid_rewrite Aux.valid_rewrite_pskKeyExchangeModes_intro' // automatic thanks to subcomp
          );
          () // LWP.valid_rewrite Aux.valid_clientHelloExtension_CHE_psk_key_exchange_modes_intro' // automatic thanks to subcomp
        )

noextract
let write_psk_kex2 = write_psk_kex1

let extract_write_psk_kex
  (inv: LWP.memory_invariant)
  (allow_psk_resumption: bool)
  (allow_dhe_resumption: bool)
: Tot (LWP.extract_t inv (write_psk_kex2 inv allow_psk_resumption allow_dhe_resumption))
= LWP.extract inv (write_psk_kex1 inv allow_psk_resumption allow_dhe_resumption)

inline_for_extraction
noextract
let write_psk_kex
  (#inv: LWP.memory_invariant)
  (allow_psk_resumption: bool)
  (allow_dhe_resumption: bool)
: LWP.TWrite 
    unit
    LWP.parse_empty
    Parsers.ClientHelloExtension.lwp_clientHelloExtension
    inv
=
  LWP.wrap_extracted_impl _ _ (extract_write_psk_kex inv allow_psk_resumption allow_dhe_resumption)

#restart-solver

inline_for_extraction
noextract
let write_binders1
  (inv: LWP.memory_invariant)
  (lri: LWP.lptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
  ()
: LWP.TWrite unit LWP.parse_empty lwp_offeredPsks_binders inv
=
        LWP.list_map
          Parsers.ResumeInfo13.lwp_resumeInfo13
          lwp_pskBinderEntry
          (fun r -> let tk = Parsers.ResumeInfo13.lwps_accessor_resumeInfo13_ticket r in compute_binder_ph tk)
          33ul 65535ul
          lri
          ;
        () // LWP.valid_rewrite Aux.valid_offeredPsks_binders_intro'

noextract
let write_binders2 = write_binders1

let extract_write_binders
  (inv: LWP.memory_invariant)
  (lri: LWP.lptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
: Tot (LWP.extract_t inv (write_binders2 inv lri))
= LWP.extract inv (write_binders1 inv lri)

inline_for_extraction
noextract
let write_binders
  (#inv: LWP.memory_invariant)
  (lri: LWP.lptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
: LWP.TWrite unit LWP.parse_empty lwp_offeredPsks_binders inv
= LWP.wrap_extracted_impl _ _ (extract_write_binders inv lri)

inline_for_extraction
noextract
let write_pskidentities1
  (inv: LWP.memory_invariant)
  (lri: LWP.lptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
  (now: U32.t)
  ()
: LWP.TWrite unit LWP.parse_empty lwp_offeredPsks_identities inv
=
        LWP.list_map
          Parsers.ResumeInfo13.lwp_resumeInfo13
          lwp_pskIdentity
          (obfuscate_age now)
          7ul 65535ul
          lri
          ;
        () // LWP.valid_rewrite Aux.valid_offeredPsks_identities_intro'

noextract
let write_pskidentities2 = write_pskidentities1

let extract_write_pskidentities
  (inv: LWP.memory_invariant)
  (lri: LWP.lptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
  (now: U32.t)
: Tot (LWP.extract_t inv (write_pskidentities2 inv lri now))
= LWP.extract inv (write_pskidentities1 inv lri now)

inline_for_extraction
noextract
let write_pskidentities
  (#inv: LWP.memory_invariant)
  (lri: LWP.lptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
  (now: U32.t)
: LWP.TWrite unit LWP.parse_empty lwp_offeredPsks_identities inv
= LWP.wrap_extracted_impl _ _ (extract_write_pskidentities inv lri now)

inline_for_extraction
noextract
let write_pre_shared_key1
  (inv: LWP.memory_invariant)
  (lri: LWP.lptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
  (now: U32.t)
  ()
: LWP.TWrite 
    unit
    LWP.parse_empty
    Parsers.ClientHelloExtension.lwp_clientHelloExtension
    inv
=
      Aux2.constr_clientHelloExtension_CHE_pre_shared_key (fun _ ->
        LWP.parse_vldata_intro_weak_ho' Parsers.PreSharedKeyClientExtension.lwp_preSharedKeyClientExtension 0ul 65535ul (fun _ ->
          write_pskidentities lri now;
          LWP.frame (fun _ -> write_binders lri);
          LWP.valid_rewrite Aux.valid_offeredPsks_intro' // FIXME: we might need something like valid_rewrite_trans
          // LWP.valid_rewrite Aux.valid_preSharedKeyClientExtension_intro'
        );
        () // LWP.valid_rewrite Aux.valid_clientHelloExtension_CHE_pre_shared_key_intro' // automatic thanks to subcomp
      )

noextract
let write_pre_shared_key2 = write_pre_shared_key1

let extract_write_pre_shared_key
  (inv: LWP.memory_invariant)
  (lri: LWP.lptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
  (now: U32.t)
: Tot (LWP.extract_t inv (write_pre_shared_key2 inv lri now))
= LWP.extract inv (write_pre_shared_key1 inv lri now)

inline_for_extraction
noextract
let write_pre_shared_key
  (#inv: LWP.memory_invariant)
  (lri: LWP.lptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
  (now: U32.t)
: LWP.TWrite 
    unit
    LWP.parse_empty
    Parsers.ClientHelloExtension.lwp_clientHelloExtension
    inv
=
  LWP.wrap_extracted_impl _ _ (extract_write_pre_shared_key inv lri now)

#restart-solver

inline_for_extraction
noextract
let write_final_extensions1
  (inv: LWP.memory_invariant)
  (cfg: LWP.ptr Parsers.MiTLSConfig.lwp_miTLSConfig inv)
  (edi: bool)
  (lri: LWP.lptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
  (now: U32.t)
  ()
: LWP.TWrite
    unit
    (LWP.parse_vllist Parsers.ClientHelloExtension.lwp_clientHelloExtension 0ul 65535ul)
    (LWP.parse_vllist Parsers.ClientHelloExtension.lwp_clientHelloExtension 0ul 65535ul)
    inv
= let mv = Parsers.MiTLSConfig.lwps_accessor_miTLSConfig_max_version cfg in
  let mv = Parsers.KnownProtocolVersion.lwps_knownProtocolVersion_accessor_tag mv in
  let max_version = LWP.deref Parsers.ProtocolVersion.protocolVersion_reader mv in
  match max_version with
  | TLS_1p3 ->
    let allow_psk_resumption = LWP.list_exists (fun _ -> true) lri in
    let allow_dhe_resumption = LWP.list_exists (fun _ -> true) lri in
    if allow_psk_resumption || allow_dhe_resumption
    then begin
      LWP.extend_vllist_snoc_ho _ _ _ (fun _ ->
        write_psk_kex allow_psk_resumption allow_dhe_resumption
      );
      if edi
      then
        LWP.extend_vllist_snoc_ho _ _ _
          write_clientHelloExtension_CHE_early_data;
      LWP.extend_vllist_snoc_ho _ _ _ (fun _ ->
        write_pre_shared_key lri now
      );
      ()
    end else begin
      LWP.extend_vllist_snoc_ho
        Parsers.ClientHelloExtension.lwp_clientHelloExtension 0ul 65535ul (fun _ ->
        write_psk_key_exchange_modes ()
      )
    end
  | _ -> ()

noextract
let write_final_extensions2 = write_final_extensions1

let extract_write_final_extensions
  (inv: LWP.memory_invariant)
  (cfg: LWP.ptr Parsers.MiTLSConfig.lwp_miTLSConfig inv)
  (edi: bool)
  (lri: LWP.lptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
  (now: U32.t)
: Tot (LWP.extract_t inv (write_final_extensions2 inv cfg edi lri now))
= LWP.extract inv (write_final_extensions1 inv cfg edi lri now)

inline_for_extraction
noextract
let write_final_extensions
  (#inv: LWP.memory_invariant)
  (cfg: LWP.ptr Parsers.MiTLSConfig.lwp_miTLSConfig inv)
  (edi: bool)
  (lri: LWP.lptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
  (now: U32.t)
: LWP.TWrite
    unit
    (LWP.parse_vllist Parsers.ClientHelloExtension.lwp_clientHelloExtension 0ul 65535ul)
    (LWP.parse_vllist Parsers.ClientHelloExtension.lwp_clientHelloExtension 0ul 65535ul)
    inv
= LWP.wrap_extracted_impl _ _ (extract_write_final_extensions inv cfg edi lri now)

inline_for_extraction
noextract
let keyshares1
  (inv: LWP.memory_invariant)
  (cfg: LWP.ptr Parsers.MiTLSConfig.lwp_miTLSConfig inv)
  (ks: option (LWP.ptr lwp_clientHelloExtension_CHE_key_share inv))
  ()
: LWP.TWrite unit (LWP.parse_vllist lwp_clientHelloExtension 0ul 65535ul) (LWP.parse_vllist lwp_clientHelloExtension 0ul 65535ul) inv
=
  let mv = Parsers.MiTLSConfig.lwps_accessor_miTLSConfig_max_version cfg in
  let mv = Parsers.KnownProtocolVersion.lwps_knownProtocolVersion_accessor_tag mv in
  let max_version = LWP.deref Parsers.ProtocolVersion.protocolVersion_reader mv in
  match max_version, ks with
  | TLS_1p3, Some ks ->
    LWP.frame (fun _ -> Aux2.constr_clientHelloExtension_CHE_key_share (fun _ -> LWP.cat ks));
    LWP.extend_vllist_snoc _ _ _
  | _ -> ()

noextract
let keyshares2 = keyshares1

let extract_keyshares
  (inv: LWP.memory_invariant)
  (cfg: LWP.ptr Parsers.MiTLSConfig.lwp_miTLSConfig inv)
  (ks: option (LWP.ptr lwp_clientHelloExtension_CHE_key_share inv))
: Tot (LWP.extract_t _ (keyshares2 inv cfg ks))
= LWP.extract _ (keyshares1 _ _ _)

inline_for_extraction
noextract
let keyshares
  (#inv: LWP.memory_invariant)
  (cfg: LWP.ptr Parsers.MiTLSConfig.lwp_miTLSConfig inv)
  (ks: option (LWP.ptr lwp_clientHelloExtension_CHE_key_share inv))
: LWP.TWrite unit (LWP.parse_vllist lwp_clientHelloExtension 0ul 65535ul) (LWP.parse_vllist lwp_clientHelloExtension 0ul 65535ul) inv
= LWP.wrap_extracted_impl _ _ (extract_keyshares inv cfg ks)

inline_for_extraction
noextract
let write_extensions1
  (inv: LWP.memory_invariant)
  (cfg: LWP.ptr Parsers.MiTLSConfig.lwp_miTLSConfig inv)
  (ks: option (LWP.ptr lwp_clientHelloExtension_CHE_key_share inv))
  (edi: bool)
  (lri: LWP.lptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
  (now: U32.t)
  ()
: LWP.TWrite
    unit
    LWP.parse_empty
    (LWP.parse_vllist Parsers.ClientHelloExtension.lwp_clientHelloExtension 0ul 65535ul)
    inv
=
  LWP.write_vllist_nil _ _;
  keyshares cfg ks;
  write_final_extensions cfg edi lri now

noextract
let write_extensions2 = write_extensions1

let write_extensions
  (inv: LWP.memory_invariant)
  (cfg: LWP.ptr Parsers.MiTLSConfig.lwp_miTLSConfig inv)
  (ks: option (LWP.ptr lwp_clientHelloExtension_CHE_key_share inv))
  (edi: bool)
  (lri: LWP.lptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
  (now: U32.t)
: Tot (LWP.extract_t _ (write_extensions2 inv cfg ks edi lri now))
= LWP.extract _ (write_extensions1 _ _ _ _ _ _)
