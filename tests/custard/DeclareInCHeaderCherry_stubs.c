#include "DeclareInCHeaderCherry.h"

uint32_t (*declare_header_step)(uint32_t) = DeclareInCHeaderCherry_step;

uint32_t DeclareInCHeaderCherry_step(uint32_t x) { return x + 1; }
