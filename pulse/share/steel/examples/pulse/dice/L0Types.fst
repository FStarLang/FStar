module L0Types
module U32 = FStar.UInt32

assume
val valid_key_usage (i: U32.t) : Type0

let key_usage_payload_t = i: U32.t { valid_key_usage i }

noeq
type deviceIDCSR_ingredients_t = {
  deviceIDCSR_ku: key_usage_payload_t;
  // deviceIDCSR_version: datatype_of_asn1_type INTEGER;
  // deviceIDCSR_s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING;
  // deviceIDCSR_s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING;
  // deviceIDCSR_s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING
}

assume
val x509_version_t : Type0

assume
val x509_serialNumber_t : Type0

noeq
type aliasKeyCRT_ingredients_t = {
  aliasKeyCrt_version: x509_version_t;
  aliasKeyCrt_serialNumber: x509_serialNumber_t;
  // aliasKeyCrt_i_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING;
  // aliasKeyCrt_i_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING;
  // aliasKeyCrt_i_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING;
  // aliasKeyCrt_notBefore: datatype_of_asn1_type UTC_TIME;
  // aliasKeyCrt_notAfter : datatype_of_asn1_type Generalized_Time;
  // aliasKeyCrt_s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING;
  // aliasKeyCrt_s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING;
  // aliasKeyCrt_s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING;
  // aliasKeyCrt_ku: key_usage_payload_t;
  // aliasKeyCrt_l0_version: datatype_of_asn1_type INTEGER;
}