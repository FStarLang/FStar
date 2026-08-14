/* The two C types this program passes around but never builds or inspects.
 *
 * Neither has an F* definition Custard could compile: hash_alg is EverCrypt's
 * algorithm tag, and FStar_Bytes_bytes is whatever the L0 implementation on
 * the other side of L0Core.fsti says it is.  Both are declared here rather
 * than borrowed from krmllib, so that the C Custard emits depends on this
 * example's own headers and on nothing else.
 *
 * --custard_extern_type points Custard at this file; see custard.Makefile.
 */

#ifndef __DICE_CUSTARD_EXTERNS_H
#define __DICE_CUSTARD_EXTERNS_H

#include <stdint.h>

typedef uint8_t Spec_Hash_Definitions_hash_alg;

typedef struct {
  uint32_t length;
  const char *data;
} FStar_Bytes_bytes;

#endif
