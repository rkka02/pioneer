"""Reproduce the numerical checks and vector figures for the corner-boost paper.

Run with Python 3, NumPy, SciPy and Matplotlib. The finite spectra are
constructed controls with the stipulated limiting area law.
"""

from fractions import Fraction
from math import factorial
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from scipy.integrate import quad
from scipy.optimize import linprog, root
from scipy.special import hyp1f1, roots_jacobi, roots_legendre


ALPHA = 257 / 90


def finite_area_law(levels):
    """s_j = j log 2, multiplicity = 2**j times the j-th count increment."""
    indices = np.arange(1, levels + 1)
    # Certify each integer floor by using 90th powers of Python integers.
    counts = []
    for j in map(int, indices):
        c = int(j**ALPHA)
        power = j**257
        while c**90 > power:
            c -= 1
        while (c + 1)**90 <= power:
            c += 1
        counts.append(c)
    mass = np.diff(np.array([0, *counts], dtype=float)) / counts[-1]
    return indices / levels, mass


def moment_columns(x, messages, scaled_step):
    # scaled_step = eta * s_star / (4 pi**2)
    phase = 2 * np.pi * scaled_step * np.outer(x, np.arange(1, messages))
    return np.column_stack((np.cos(phase), np.sin(phase)))


def balanced_filter(x, mass, raw_filter, messages, scaled_step):
    features = moment_columns(x, messages, scaled_step)
    weight = mass * raw_filter
    matrix = features.T @ (weight[:, None] * features)
    adjustment = np.linalg.solve(matrix, weight @ features)
    margin = np.sqrt(messages - 1) * np.linalg.norm(adjustment)
    accept = raw_filter * (1 - features @ adjustment) / (1 + margin)
    if accept.min() < -1e-12 or accept.max() > 1 + 1e-12:
        raise ValueError("The finite model is too coarse for this correction.")
    return accept


def gram_matrix(x, probability, messages, scaled_step):
    amplitude = np.exp(2j * np.pi * scaled_step * np.outer(x, np.arange(messages)))
    return amplitude.conj().T @ (probability[:, None] * amplitude)


def largest_success(x, mass, messages, scaled_step):
    features = moment_columns(x, messages, scaled_step)
    result = linprog(
        -np.ones(len(x)), A_eq=features.T, b_eq=np.zeros(features.shape[1]),
        bounds=list(zip(np.zeros(len(x)), mass)), method="highs",
        options={"primal_feasibility_tolerance": 1e-10,
                 "dual_feasibility_tolerance": 1e-10},
    )
    if not result.success:
        raise RuntimeError(result.message)
    assert np.max(np.abs(features.T @ result.x)) < 1e-8
    return max(0.0, -result.fun)


def certify_replica_zero():
    """Bound F and F' at a rational center using 71 exact Taylor terms."""
    re = Fraction(3597298, 10**6)
    im = Fraction(8246609, 10**6)
    tr, ti = Fraction(1), Fraction(0)
    fr, fi, dr, di = [Fraction(0)] * 4
    for k in range(71):
        c = Fraction(257, 257 + 90*k)
        d = -Fraction(257, 257 + 90*(k+1))
        fr, fi = fr + c*tr, fi + c*ti
        dr, di = dr + d*tr, di + d*ti
        tr, ti = (-re*tr + im*ti)/(k+1), (-im*tr - re*ti)/(k+1)
    tail = Fraction(2*10**71, factorial(71))
    residual = Fraction(26, 10**10)
    slope = Fraction(86, 10**4)
    radius = Fraction(1, 10**6)
    assert re**2 + im**2 < 100 and tail < residual
    assert fr**2 + fi**2 < (residual - tail)**2
    assert dr**2 + di**2 > (slope + tail)**2
    assert residual + radius**2/2 < slope * radius  # |F''| <= 1 on disk
    z0 = complex(float(re), float(im))
    z = root(lambda pair: complex_parts(hyp1f1(ALPHA, ALPHA+1, -complex(*pair))),
             (z0.real, z0.imag), tol=1e-11)
    assert z.success and abs(complex(*z.x) - z0) < float(radius)
    return complex(*z.x)


def complex_parts(z):
    return [z.real, z.imag]


def binary_optimum(epsilon):
    """Endpoint filter and dual certificate near the binary threshold."""
    p = ALPHA
    t = np.pi / (1-epsilon)
    left_node, left_weight = roots_jacobi(40, 0, p-1)
    right_node, right_weight = roots_legendre(40)
    u, left_weight = (1+left_node)/2, left_weight / 2**p
    v, right_weight = (1+right_node)/2, right_weight/2

    def balance(pair):
        a_scale, b_scale = pair
        a_phase = a_scale*u
        b_phase = 1 - b_scale*epsilon**(p-1)*v
        left = p*a_scale**p*left_weight
        right = p*b_scale*(1-b_scale*epsilon**p*v)**(p-1)*right_weight
        left_angle, right_angle = t*epsilon*a_phase, t*epsilon*b_phase
        # Imaginary part divided by t*epsilon for conditioning at threshold.
        return [left @ np.cos(left_angle) - right @ np.cos(right_angle),
                left @ (a_phase*np.sinc(left_angle/np.pi))
                - right @ (b_phase*np.sinc(right_angle/np.pi))]

    a_limit = (p+1)/p
    solution = root(balance, (a_limit, a_limit**p/p), tol=1e-10)
    assert solution.success and np.max(np.abs(balance(solution.x))) < 1e-10
    a, b = solution.x * [epsilon, epsilon**p]
    half_gap = t*(1-b-a)/2
    center = t*(a+1-b)/2
    assert 0 < half_gap < np.pi/2 and max(center, t-center) < np.pi
    # The dual 1 - cos(t*x - center)/cos(half_gap) changes sign at a, 1-b.
    assert abs(1-np.cos(t*a-center)/np.cos(half_gap)) < 1e-10
    probability = a**p - np.expm1(p*np.log1p(-b))
    return probability, a, b


def verify():
    probability = ALPHA / 2**ALPHA
    variance = ALPHA / ((ALPHA+1)**2 * (ALPHA+2))
    print(f"Continuum filter success {probability:.10f}, area variance {variance:.10f}")
    assert abs(quad(lambda x: ALPHA * x**(ALPHA-1), 0, 1)[0] - 1) < 2e-10
    z = certify_replica_zero()
    print(f"Replica zero {z:.9f}, real tilt success {hyp1f1(ALPHA, ALPHA+1, -z.real):.9f}")
    print("levels  success     maximum Gram error    uncorrected error")
    for levels in (32, 128, 512):
        x, mass = finite_area_law(levels)
        raw = np.where(x >= 0.5, (0.5/x)**(ALPHA-1), 0.0)
        selected = balanced_filter(x, mass, raw, 4, 2)
        weights = mass * selected
        gram = gram_matrix(x, weights / weights.sum(), 4, 2)
        error = np.max(np.abs(gram - np.eye(4)))
        uncorrected = gram_matrix(x, mass * raw / (mass @ raw), 4, 2)
        print(f"{levels:6}  {weights.sum():.8f}  {error:16.3e}  "
              f"{np.max(np.abs(uncorrected - np.eye(4))):.6f}")
        assert error < 2e-12
        # A left Fourier result adds the same phase to each right codeword.
        left_phase = np.exp(-2j * np.pi * 7 * np.arange(levels) / levels)
        states = np.sqrt(weights / weights.sum())[:, None] * left_phase[:, None]
        states = states * np.exp(4j * np.pi * np.outer(x, np.arange(4)))
        np.testing.assert_allclose(states.conj().T @ states, np.eye(4), atol=2e-12)
    for messages in (2, 3, 4):
        threshold = 1 - 1/messages
        assert largest_success(x, mass, messages, threshold - 0.025) < 1e-8
        assert largest_success(x, mass, messages, threshold + 0.08) > 1e-4
    constant = 2*((ALPHA+1)/ALPHA)**ALPHA
    print("epsilon   continuum optimum    ratio to leading power")
    for eps in (.10, .03, .01, .001):
        best, _, _ = binary_optimum(eps)
        print(f"{eps:7.3f}   {best:.10g}        {best/(constant*eps**ALPHA):.8f}")
    # Independent LP, using a mesh dense near either end of the area interval.
    edges = np.sin(np.pi*np.linspace(0, 1, 2305)/2)**2
    nodes = (edges[:-1] + edges[1:])/2
    weights = np.diff(edges**ALPHA)
    for eps in (.06, .10):
        best, _, _ = binary_optimum(eps)
        numerical = largest_success(nodes, weights, 2, 1/(2*(1-eps)))
        assert abs(numerical/best - 1) < 1e-5
        print(f"LP / continuum at epsilon={eps:g}: {numerical/best:.8f}")
    # Independent integral of the complex response at an off-grid real boost.
    t = 3.7
    observed = 2 * complex(quad(lambda u: np.cos(t*u), 0.5, 1)[0],
                            quad(lambda u: np.sin(t*u), 0.5, 1)[0])
    np.testing.assert_allclose(observed, np.exp(0.75j*t) * np.sinc(t/(4*np.pi)))


def figures():
    from matplotlib.ticker import FuncFormatter, NullFormatter

    output_dir = Path(__file__).resolve().parent / "figures"
    output_dir.mkdir(exist_ok=True)
    metadata = {"Creator": "Pioneer verification script", "CreationDate": None, "ModDate": None}
    teal, orange, purple = "#076960", "#AA531B", "#614989"
    plt.rcParams.update({
        "font.family": "DejaVu Sans", "mathtext.fontset": "dejavusans",
        "font.size": 9, "axes.titlesize": 10, "axes.titlelocation": "left",
        "axes.titlepad": 7, "axes.spines.top": False, "axes.spines.right": False,
        "pdf.fonttype": 42, "axes.axisbelow": True,
    })
    fig, (left, right) = plt.subplots(1, 2, figsize=(7.1, 2.85), layout="constrained")
    v = np.linspace(0, 6.12, 620)
    left.plot(v, np.ones_like(v), "--", color="#66747A", label="Either boundary")
    left.plot(v, np.sinc(v/2)**2, color=teal, lw=2.2, label="Joint state")
    left.scatter([2, 4, 6], [0, 0, 0], s=22, color=teal, zorder=3)
    left.set(title="(a) A four-message code", xlabel=r"Boost from the initial state, $v$",
             ylabel="Fidelity to initial state", xlim=(-0.08, 6.17),
             ylim=(-0.05, 1.10), xticks=[0, 2, 4, 6])
    left.legend(loc="center right", frameon=False, fontsize=8)
    x, mass = finite_area_law(384)
    steps = np.linspace(0.4, 1.35, 116)
    for messages, color, line in [(2, teal, "-"), (3, purple, "--"), (4, orange, "-.")]:
        success = [largest_success(x, mass, messages, step) for step in steps]
        right.plot(steps, success, line, lw=1.9, color=color, label=rf"$M={messages}$")
        right.axvline(1-1/messages, lw=1, ls=":", color=color)
    right.set(title="(b) Optimal filtering on 384 levels", xlabel=r"Step between messages, $v$",
              ylabel="Preparation probability", xlim=(0.4, 1.35), ylim=(-0.025, 0.74),
              xticks=[0.5, 0.75, 1, 1.25])
    right.legend(loc="upper left", frameon=False, fontsize=8)
    for ax in (left, right):
        ax.grid(axis="y", color="#e0e6e6", lw=0.7)
    fig.savefig(output_dir / "boosts.pdf", metadata=metadata)
    plt.close(fig)

    epsilon = np.geomspace(0.001, 0.19, 40)
    optimum, low_width, high_width = np.array([binary_optimum(e) for e in epsilon]).T
    leading = 2*((ALPHA+1)/ALPHA * epsilon)**ALPHA
    fig, (left, right) = plt.subplots(1, 2, figsize=(7.1, 2.9), layout="constrained")
    left.loglog(epsilon, low_width, color=teal, lw=2, label=r"Low-area tail $a$")
    left.loglog(epsilon, high_width, "--", color=purple, lw=2, label=r"High-area tail $b$")
    left.set(title="(a) Width of each accepted tail", ylabel="Fraction of area range")
    left.legend(loc="lower right", frameon=False, fontsize=8)
    right.loglog(epsilon, leading, "--", color=orange, lw=1.6, label=r"Leading $C\epsilon^{257/90}$")
    right.loglog(epsilon[::3], optimum[::3], "o", ms=3.6, mfc="white", mec=teal,
                 mew=1.2, label="Optimal filter")
    right.set(title="(b) Maximum binary success", ylabel="Preparation probability")
    right.legend(loc="upper left", frameon=False, fontsize=8)
    for ax in (left, right):
        ax.set_xlabel(r"Excess above threshold, $\epsilon=1-\eta_c/\eta$")
        ax.grid(True, which="major", color="#e0e6e6", lw=0.7)
        for axis in (ax.xaxis, ax.yaxis):
            axis.set_major_formatter(FuncFormatter(lambda value, _: rf"$10^{{{round(np.log10(value))}}}$"))
            axis.set_minor_formatter(NullFormatter())
    fig.savefig(output_dir / "threshold.pdf", metadata=metadata)
    plt.close(fig)


if __name__ == "__main__":
    verify()
    figures()
