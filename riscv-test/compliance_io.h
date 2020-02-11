// RISC-V Compliance IO Test Header File

#ifndef _COMPLIANCE_IO_H
#define _COMPLIANCE_IO_H

//-------------
// RV IO Macros
//-------------

#define RVTEST_IO_INIT
#define RVTEST_IO_WRITE_STR(_SP, _STR)
#define RVTEST_IO_CHECK()

// _SP: test register (volatile)
// _R: the destination register holding the result value
// _I: the correct value (immediate)
#define RVTEST_IO_ASSERT_GPR_EQ(_SP, _R, _I) \
  mv s0, _R; \
  li s1, _I; \
  bne s0, s1, looper;

#define RVTEST_IO_ASSERT_SFPR_EQ(_F, _R, _I)
#define RVTEST_IO_ASSERT_DFPR_EQ(_D, _R, _I)

#endif // _COMPLIANCE_IO_H
