#include "StaticLib.h"
#include "StaticOther.h"
#include "StaticCmp.h"
#include <cmath>

extern "C" uint32_t static_header_from_c(void);
extern "C" uint32_t (*static_header_address(void))(uint32_t);

int main() {
  StaticHeader_pair p = {1, 2};
  StaticHeaderOther_item q = {3, 4};
  return static_header_from_c() == 12 && StaticHeader_api(1) == 12 &&
         StaticHeader_plain(2) == 3 &&
         StaticHeader_equal(p, p) && StaticHeaderOther_equal(q, q) &&
         StaticHeaderCompare_equal(p, p) &&
         StaticHeader_countdown(3) == 0 && std::isnan(StaticHeader_get_nan()) &&
         static_header_address() != &StaticHeader_plain ? 0 : 1;
}
