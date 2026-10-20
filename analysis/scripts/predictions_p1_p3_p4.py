"""Finite P1/P3/P4 monitors: no asymptotic or non-halting claim.

The P4 z transform is descriptive, not an iid chi-square p-value: adjacent
words overlap. Monte Carlo uses iid streams with the same length, extraction,
window pairs, and max-|z| family statistic as the data.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import math
from pathlib import Path
import numpy as np

PHI = (1 + math.sqrt(5)) / 2


def validated_bits(parities):
    p = np.asarray(parities)
    if p.ndim != 1 or not len(p) or not np.all((p == 0) | (p == 1)):
        raise ValueError("parities must be a nonempty one-dimensional bit array")
    return p.astype(np.uint8, copy=False)


def window_statistics(parities, max_window=16):
    p = validated_bits(parities)
    if not 2 <= max_window <= min(20, len(p)):
        raise ValueError("max_window must lie between 2 and min(20, N)")
    code = p.astype(np.int64)
    rows = []
    for length in range(2, max_window + 1):
        code = (code[:-1] << 1) | p[length - 1:]
        counts = np.bincount(code, minlength=1 << length).astype(float)
        for j in range(1, length):
            k = length - j
            joint = counts.reshape(1 << j, 1 << k)
            row = joint.sum(axis=1)
            col = joint.sum(axis=0)
            expected = row[:, None] * col[None, :] / counts.sum()
            active = expected > 0
            chi = float(np.sum((joint[active] - expected[active]) ** 2 / expected[active]))
            dof = (int(np.count_nonzero(row)) - 1) * (int(np.count_nonzero(col)) - 1)
            z = (chi - dof) / math.sqrt(2 * dof) if dof else None
            rows.append({"j": j, "k": k, "samples": int(counts.sum()),
                         "chi2": chi, "active_dof": dof, "z_descriptive": z,
                         "min_positive_expected": float(expected[active].min())})
    return rows


def family_statistic(rows):
    values = [abs(r["z_descriptive"]) for r in rows if r["z_descriptive"] is not None]
    return max(values) if values else None


def calibrate_p4(parities, max_window=16, replicates=99, seed=20261020):
    """Family-wise Monte Carlo tail rank, conditional on an iid(1/2) null."""
    p = validated_bits(parities)
    if replicates < 1:
        raise ValueError("replicates must be positive")
    observed = family_statistic(window_statistics(p, max_window))
    if observed is None:
        raise ValueError("all observed tables are degenerate; P4 is not evaluable")
    rng = np.random.default_rng(seed)
    controls = []
    for _ in range(replicates):
        control = rng.integers(0, 2, len(p), dtype=np.uint8)
        controls.append(family_statistic(window_statistics(control, max_window)))
    if any(x is None for x in controls):
        raise ValueError("a null stream was degenerate; increase sample length")
    exceed = sum(x >= observed for x in controls)
    return {"null": "iid Bernoulli(1/2), overlapping windows, max abs z over all pairs",
            "seed": seed, "replicates": replicates, "steps_per_stream": len(p),
            "max_window": max_window, "observed_max_abs_z": observed,
            "null_max_abs_z": controls, "exceedances": exceed,
            "monte_carlo_tail_rank": (1 + exceed) / (replicates + 1),
            "minimum_tail_rank": 1 / (replicates + 1),
            "interpretation": "finite diagnostic under this null; not proof of orbit independence"}


def prediction_report(parities, lo=1_000_000, max_window=16):
    p = validated_bits(parities)
    if not 2 <= lo <= len(p):
        raise ValueError("lo must be between 2 and N")
    steps = np.arange(1, len(p) + 1, dtype=np.int64)
    counter = np.cumsum(np.where(p == 0, 2, -1), dtype=np.int64)
    peak = np.maximum.accumulate(np.maximum(counter, 0))  # includes a_0 = 0
    drawdown = np.maximum.accumulate(peak - counter)
    records = np.flatnonzero(np.diff(drawdown, prepend=0) > 0)
    selected = [i for i in records if steps[i] >= lo]
    record_rows = [{"t": int(steps[i]), "drawdown": int(drawdown[i]),
                    "ratio": float(drawdown[i] * math.log(PHI) / math.log(int(steps[i])))}
                   for i in selected]
    ratios = [r["ratio"] for r in record_rows]
    tt = steps[lo - 1:]
    scaled_deviation = np.abs(counter[lo - 1:] / tt - 0.5) / (3 * np.sqrt(np.log(tt) / tt))
    worst = int(np.argmax(scaled_deviation))
    negatives = np.flatnonzero(counter < 0)
    rows = window_statistics(p, max_window)
    zs = [r["z_descriptive"] for r in rows if r["z_descriptive"] is not None]
    nondegenerate = len(zs) == len(rows)
    return {
        "status": "finite numerical evidence only",
        "N": len(p), "lo": lo,
        "parities_sha256": hashlib.sha256(p.tobytes()).hexdigest(),
        "walk": {"start_counter": 0, "final_counter": int(counter[-1]),
                 "minimum_counter": int(counter.min()),
                 "first_negative_t": int(negatives[0] + 1) if len(negatives) else None,
                 "minimum_t_ge_15": int(counter[14:].min()) if len(p) >= 15 else None},
        "P1": {"scope": "new drawdown records with lo <= t <= N",
               "records": record_rows,
               "record_band_0_8_1_25": all(0.8 <= x <= 1.25 for x in ratios) if ratios else None,
               "record_alert_above_1_5": any(x > 1.5 for x in ratios),
               "no_records_is_inconclusive": not ratios,
               "endpoint_drawdown": int(drawdown[-1]),
               "endpoint_ratio": float(drawdown[-1] * math.log(PHI) / math.log(len(p)))},
        "P3": {"band": "3 * sqrt(ln(t)/t); not an iterated-logarithm band",
               "max_ratio_to_band": float(scaled_deviation[worst]),
               "worst_t": int(tt[worst]), "band_holds": bool(scaled_deviation[worst] <= 1)},
        "P4": {"scope": "all positive j,k with j+k <= max_window",
               "max_window": max_window, "pairs": len(rows),
               "all_tables_nondegenerate": nondegenerate,
               "z_min": min(zs) if zs else None, "z_max": max(zs) if zs else None,
               "descriptive_abs_z_le_4": all(abs(z) <= 4 for z in zs) if nondegenerate else None,
               "descriptive_positive_z_gt_6": any(z > 6 for z in zs),
               "warning": "overlapping samples: z is not an iid chi-square significance test",
               "tables": rows},
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("parities", type=Path)
    parser.add_argument("--lo", type=int, default=1_000_000)
    parser.add_argument("--max-window", type=int, default=16)
    parser.add_argument("--null-replicates", type=int, default=0)
    parser.add_argument("--seed", type=int, default=20261020)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args(argv)
    if args.null_replicates < 0:
        parser.error("--null-replicates cannot be negative")
    p = np.load(args.parities, allow_pickle=False)
    report = prediction_report(p, args.lo, args.max_window)
    if args.null_replicates:
        report["P4_calibration"] = calibrate_p4(p, args.max_window, args.null_replicates, args.seed)
    rendered = json.dumps(report, indent=2, allow_nan=False) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered)
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
