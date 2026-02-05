/*
 * qphysics.h — Minimal C port of src/qphysics.py
 *
 * Quaternion math for the QBP interactive proof visualization.
 * Only the functions needed for the Stern-Gerlach proof chain are included.
 */

#ifndef QBP_QPHYSICS_H
#define QBP_QPHYSICS_H

typedef struct {
    double w;  /* scalar part  */
    double x;  /* i component  */
    double y;  /* j component  */
    double z;  /* k component  */
} Quat;

/* Standard spin observables */
extern const Quat SPIN_X;
extern const Quat SPIN_Y;
extern const Quat SPIN_Z;

/* Create a normalized quaternion */
Quat quat_normalize(Quat q);

/* Check if a quaternion is pure (w == 0) */
int quat_is_pure(Quat q);

/* Check if a quaternion is unit (norm == 1) */
int quat_is_unit(Quat q);

/* Dot product of two quaternions' vector parts */
double quat_vec_dot(Quat a, Quat b);

/* Expectation value: vecDot(vecPart(psi), vecPart(O)) */
double quat_expectation(Quat psi, Quat obs);

/* Probability of measuring +1 (spin up): (1 + <O>) / 2 */
double quat_prob_up(Quat psi, Quat obs);

/* Probability of measuring -1 (spin down): (1 - <O>) / 2 */
double quat_prob_down(Quat psi, Quat obs);

#endif /* QBP_QPHYSICS_H */
