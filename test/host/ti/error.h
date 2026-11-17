#ifndef TI_ERROR_H
#define TI_ERROR_H

#include <setjmp.h>

extern jmp_buf sim_os_err;
#define os_PushErrorHandler() setjmp(sim_os_err)
#define os_PopErrorHandler() ((void)0)

#endif
