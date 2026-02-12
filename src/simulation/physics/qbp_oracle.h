/*
 * QBP Oracle C Interface
 *
 * Header for Lean-compiled physics oracle functions.
 * These functions are exported from Lean via @[export] annotations
 * in proofs/QBP/Oracle/FFI.lean.
 *
 * Fallback: If shared library linking is not available, the Go code
 * calls `lake exe oracle` via subprocess and parses JSON output.
 */

#ifndef QBP_ORACLE_H
#define QBP_ORACLE_H

#ifdef __cplusplus
extern "C" {
#endif

/* Probability of spin-up for state at angle theta from z-axis */
double qbp_prob_up(double theta);

/* Expectation value for state at angle theta from z-axis */
double qbp_expectation(double theta);

/* Probability of spin-down for state at angle theta from z-axis */
double qbp_prob_down(double theta);

#ifdef __cplusplus
}
#endif

#endif /* QBP_ORACLE_H */
