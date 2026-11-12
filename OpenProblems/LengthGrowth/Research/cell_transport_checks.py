"""Exact rational checks for the cell-transport research note; not a flow simulation."""
from fractions import Fraction as Q
import json
from pathlib import Path

a, b = -Q(257, 480), Q(17, 480)
# K(u)=a cos u+b cos 2u+(epsilon/4)sin u, k(s)=1+2K(2s).
# Store coefficients of epsilon separately where appropriate.
jets = {
    "k0": 1 + 2 * (a + b),
    "k1_coefficient_of_epsilon": Q(1),
    "k2": 8 * (-a - 4 * b),
    "k3_coefficient_of_epsilon": Q(-4),
    "k4": 32 * (a + 16 * b),
}
assert jets == {
    "k0": Q(0), "k1_coefficient_of_epsilon": Q(1),
    "k2": Q(63, 20), "k3_coefficient_of_epsilon": Q(-4), "k4": Q(1),
}
# At k=0: F=k'', F_s=k''', F_ss=k'''' and material k_t=-F_ss.
jets.update(F0=jets["k2"], Fs0_coefficient_of_epsilon=jets["k3_coefficient_of_epsilon"],
            Fss0=jets["k4"], material_kt0=-jets["k4"])
assert -jets["material_kt0"] == 1  # zero-marker arclength speed = 1/epsilon.

alpha, eta = Q(1, 5), Q(1, 10)
orders = {
    "cell_scale_lambda": alpha,
    "cell_count_N": alpha,
    "length": 2 * alpha,
    "energy_excess_above_positive_limit": -eta,
    "D": -1 - eta,
    "M6": -6 * alpha,
    "Y": -2 * alpha,
    "Z": -6 * alpha,
    "force_gradient_budget": -1 - eta - 2 * alpha,
    "persistent_cell_displacement_action_density": 2 * alpha - 2,
    "dimensionless_force_residual_squared": 4 * alpha - 1 - eta,
    "displacement_action_over_force_gradient_budget": 4 * alpha - 1 + eta,
}
assert orders["length"] > Q(1, 4) and orders["length"] < Q(1, 2)
assert orders["force_gradient_budget"] < -1
assert orders["persistent_cell_displacement_action_density"] < -1
assert orders["dimensionless_force_residual_squared"] < 0
assert orders["displacement_action_over_force_gradient_budget"] < 0
result = {
    "status": "Exact rational checks passed; no geometric trajectory is constructed.",
    "actual_closed_initial_curve_jets": {k: str(v) for k, v in jets.items()},
    "scaling_budget_diagnostic_only": {k: str(v) for k, v in orders.items()},
}
out = Path(__file__).with_name("length_cell_transport_checks.json")
out.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
print(json.dumps(result, indent=2, ensure_ascii=False))
