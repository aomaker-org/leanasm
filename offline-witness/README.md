<!-- Path: leanasm/offline-witness/README.md -->
# Offline Witness Verification Suite
<!-- Max Column: 80 Columns -->

This directory contains standalone computational witness scripts and stress
probes for the `QuasiRiemann` ladder architecture in `leanasm`.

## Key Probes & Mathematical Invariants

### 1. Height Scale Probes: $t \sim 10^{60}$ and $t \sim 10^{120}$
- **$t \sim 10^{60}$**: Checked across dyadic rungs $k = 10, 11, 12, 13, 14$.
  Validates short-interval bounds, factored power bases ($10^{12 \cdot 2^{k-1}}$
  and $10^{6 \cdot 2^{k-1}}$), and phase reduction precision.
- **$t \sim 10^{120}$**: High-range stress probe (`stress_high_k_t120.py`)
  probing rungs $k = 15 \dots 20$. Evaluates numerical stability of phase
  reduction under ultra-high height scales.

### 2. $c(k) < 10^{18}$ Boundary: $k = 20$ vs. $k = 21$
The Chebyshev envelope coefficient is given by:
$$c(k) = 2 \cdot (2 \cdot (29 \cdot 2^{k-1})^2) \cdot 1000 + 2$$
- For $k = 20$:
  $$c(20) \approx 9.2469 \times 10^{17} < 10^{18}$$
- For $k = 21$:
  $$c(21) \approx 3.6988 \times 10^{18} \ge 10^{18}$$
Hence $k = 20$ marks the sharp boundary where $c(k) < 10^{18}$ holds within
standard 64-bit bounds.

### 3. $2^{2k+10}$ Tail Gate Closure
The `InvSqrtTailGateSpec` requires exact balance between scale factor
$N_k = 2^{2k-6}$ and denominator $M_k = 2^{k+5}$ with tail bound 256:
$$\text{LHS} = N_k \cdot 256^2 = 2^{2k-6} \cdot 2^{16} = 2^{2k+10}$$
$$\text{RHS} = M_k^2 \cdot 1^2 = (2^{k+5})^2 = 2^{2k+10}$$
This identity holds identically for all integer $k \ge 5$.

### 4. Precision Thresholds $P \ge 180$ and $P \ge 240$
At height scale $t \sim 10^{120}$, the phase uncertainty satisfies:
$$\Delta(\text{phase}) \sim t \cdot 10^{-P} = 10^{120 - P}\text{ rad}$$
- **Target $\le 10^{-60}$ rad**:
  $$120 - P \le -60 \iff P \ge 180\text{ digits}$$
- **Target $\le 10^{-120}$ rad**:
  $$120 - P \le -120 \iff P \ge 240\text{ digits}$$

## Inventory of Witness Scripts

- `check_rung10.py`: Exponent and monotonicity check for $k = 10$.
- `stress_rung10_t60.py`: Stress check for $k = 10$ at $t \sim 10^{60}$.
- `stress_rung11_t60.py`: Stress check for $k = 11$ at $t \sim 10^{60}$.
- `stress_rung12_t60.py`: Stress check for $k = 12$ at $t \sim 10^{60}$.
- `stress_rung13_t60.py`: Stress check for $k = 13$ at $t \sim 10^{60}$.
- `stress_rung14_t60.py`: Stress check for $k = 14$ at $t \sim 10^{60}$.
- `stress_high_k_t120.py`: High rung ($k = 15\dots 20$) and $t \sim 10^{120}$
  probe.

<!-- end of file: leanasm/offline-witness/README.md -->
