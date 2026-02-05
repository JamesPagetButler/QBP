/*
 * qphysics.c — Minimal C port of src/qphysics.py
 */

#include "qphysics.h"
#include <math.h>

const Quat SPIN_X = { 0.0, 1.0, 0.0, 0.0 };
const Quat SPIN_Y = { 0.0, 0.0, 1.0, 0.0 };
const Quat SPIN_Z = { 0.0, 0.0, 0.0, 1.0 };

Quat quat_normalize(Quat q)
{
    double n = sqrt(q.w*q.w + q.x*q.x + q.y*q.y + q.z*q.z);
    if (n == 0.0) return (Quat){ 1.0, 0.0, 0.0, 0.0 };
    return (Quat){ q.w/n, q.x/n, q.y/n, q.z/n };
}

int quat_is_pure(Quat q)
{
    return q.w == 0.0;
}

int quat_is_unit(Quat q)
{
    double n = q.w*q.w + q.x*q.x + q.y*q.y + q.z*q.z;
    return fabs(n - 1.0) < 1e-12;
}

double quat_vec_dot(Quat a, Quat b)
{
    return a.x*b.x + a.y*b.y + a.z*b.z;
}

double quat_expectation(Quat psi, Quat obs)
{
    return quat_vec_dot(psi, obs);
}

double quat_prob_up(Quat psi, Quat obs)
{
    return (1.0 + quat_expectation(psi, obs)) / 2.0;
}

double quat_prob_down(Quat psi, Quat obs)
{
    return (1.0 - quat_expectation(psi, obs)) / 2.0;
}
