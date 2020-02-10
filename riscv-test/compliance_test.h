// RISC-V Compliance Test Header File

#ifndef _COMPLIANCE_TEST_H
#define _COMPLIANCE_TEST_H

//---------------------
// RV Compliance Macros
//---------------------

#define RV_COMPLIANCE_HALT
#define RV_COMPLIANCE_RV32M
#define RV_COMPLIANCE_CODE_BEGIN \
looper: \
  jal zero, 0;

#define RV_COMPLIANCE_CODE_END \
  jal zero, 0;

#define RV_COMPLIANCE_DATA_BEGIN
#define RV_COMPLIANCE_DATA_END

#endif // _COMPLIANCE_TEST_H
