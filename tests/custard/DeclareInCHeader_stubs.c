#include "DeclareInCHeader.h"

DeclareInCHeader_pair DeclareInCHeader_swap(DeclareInCHeader_pair p) {
  DeclareInCHeader_pair r = { p.right, p.left };
  return r;
}

uint32_t header_named(uint32_t x) { return x + 1; }
uint32_t DeclareInCHeader_erased(uint32_t x) { return x; }
void DeclareInCHeader_tick(void) {}
const char *DeclareInCHeader_label(uint32_t x) { (void)x; return "header"; }
uint32_t DeclareInCHeader_rooted(uint32_t x) { return x; }
uint32_t DeclareInCHeader_private_hook(uint32_t x) { return x + 1; }
uint32_t DeclareInCHeaderIface_ping(uint32_t x) { return x + 1; }
