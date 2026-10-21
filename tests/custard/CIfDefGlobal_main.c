#include "CIfDefGlobal.h"

int main(void) {
  CIfDefGlobal_init_globals();
#ifdef CUSTARD_IFDEF_A
  return CIfDefGlobal_result != 7;
#else
  return CIfDefGlobal_result != 11;
#endif
}
