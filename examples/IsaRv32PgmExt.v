(** List of RISC-V/Kami benchmarks *)

(* Note that our current multiprocessor + memory case study does not support a
 * single-core machine; we at least need 2 cores to run benchmarks. In other
 * words, even if a target benchmark can run in single-core, you should set 2
 * cores with the same benchmark.
 *)

(* 1. Euclid's GCD: single-thread *)
Require Export IsaRv32PgmGcd.

(* 2. Factorial: single-thread *)
Require Export IsaRv32PgmFact.

(* 3. Bubble Sort: single-thread *)
Require Export IsaRv32PgmBsort.

(* 4. Towers of Hanoi: single-thread *)
Require Export IsaRv32PgmHanoi.

(* 5. Shared counter (Dekker’s): 2 threads *)
Require Export IsaRv32PgmDekker1.
Require Export IsaRv32PgmDekker2.

(* 6. Shared counter (Peterson’s): 2 threads *)
Require Export IsaRv32PgmPeterson1.
Require Export IsaRv32PgmPeterson2.

(* 7. Parallel Matrix Multiply: 4 threads *)
Require Export IsaRv32PgmMatMulInit.
Require Export IsaRv32PgmMatMulNormal1.
Require Export IsaRv32PgmMatMulNormal2.
Require Export IsaRv32PgmMatMulReport.

(* 8. Concurrent Bank Transactions: 4 threads *)
Require Import IsaRv32PgmBankerInit.
Require Import IsaRv32PgmBankerWorker1.
Require Import IsaRv32PgmBankerWorker2.
Require Import IsaRv32PgmBankerWorker3.
