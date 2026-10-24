#include "GlobalRename.h"

static const uint32_t initial_limit = mixedCaseLimit;

#ifdef __cplusplus
extern "C" {
#endif

uint32_t ExternalStep(uint32_t x) { return x + 1; }
uint32_t AgreedStep(uint32_t x) { return x + 1; }

uint32_t CheckAPI(void)
{
  ApiPair p = ApiMake(1, 2);
  return ApiAdd(p) == 16 && api_global == 5 && initial_limit == 7 ? 0 : 1;
}

#ifdef __cplusplus
}
#endif
