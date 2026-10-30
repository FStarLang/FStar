#include "StaticLib.h"
#include "StaticOther.h"
#include "StaticCmp.h"
#include "StaticLib.h"

uint32_t static_header_from_c(void) {
  StaticHeader_pair p = {1, 2};
  StaticHeaderOther_item q = {3, 4};
  return StaticHeader_equal(p, p) && StaticHeaderOther_equal(q, q) &&
         StaticHeaderCompare_equal(p, p) && STATICHEADER_LIMIT == 17 &&
         StaticHeader_countdown(3) == 0 && isnan(StaticHeader_get_nan()) ?
         StaticHeader_api(1) : 0;
}

uint32_t (*static_header_address(void))(uint32_t) { return StaticHeader_plain; }
