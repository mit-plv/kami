// RISC-V Compliance Test Header File

#ifndef _COMPLIANCE_TEST_H
#define _COMPLIANCE_TEST_H

//---------------------
// RV Compliance Macros
//---------------------

#define RV_COMPLIANCE_HALT
#define RV_COMPLIANCE_RV32M

#define RV_COMPLIANCE_CODE_BEGIN \
  jal zero, test_start;          \
loop_fail:                       \
  jal zero, loop_fail;           \
test_start:

#define RV_COMPLIANCE_CODE_END \
loop_success: \
 jal zero, loop_success;

#define RV_COMPLIANCE_DATA_BEGIN
#define RV_COMPLIANCE_DATA_END

#endif // _COMPLIANCE_TEST_H
