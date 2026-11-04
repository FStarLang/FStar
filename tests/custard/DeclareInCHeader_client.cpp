#include "DeclareInCHeader.h"
#include <cstring>

int main() {
  DeclareInCHeader_pair p = {3, 4};
  DeclareInCHeader_pair r = DeclareInCHeader_swap(p);
  DeclareInCHeader_tick();
  return r.left == 4 && r.right == 3 &&
         header_named(1) == 2 &&
         DeclareInCHeader_erased(5) == 5 &&
         DeclareInCHeader_rooted(6) == 6 &&
         DeclareInCHeaderIface_ping(7) == 8 &&
         std::strcmp(DeclareInCHeader_label(0), "header") == 0 ? 0 : 1;
}
