# Summary of changes for run 7d0e0050-9625-4dba-a73c-237cb4f86539
I cloned `enuminous/Monlithic_EFMW_102_Lean4` (commit `58f743b`) and worked out which laws actually follow from its equations. That repository records all 102 equations and gives types for some of them, but contains only one theorem: \(\varphi^{46} = (\varphi^{23})^2\). I proved **about 40 laws** in Lean. They are in five files under `RequestProject/`, and all five build with no `sorry` and only Lean's standard axioms. The full table, with the Lean name for each law, is in `LAWS.md`.

These are mathematical consequences of the equations as written, under the hypotheses stated in each theorem. None of them is evidence that EFMW describes the physical world; that is what ME-102 is meant to test.

**Golden-ratio / Scalar-φ** (`Golden.lean`)
- \(\varphi^2=\varphi+1\), and \(\varphi^{n+1}=F_{n+1}\varphi+F_n\) (Fibonacci numbers).
- ME-042: \(\varphi^{23}=28657\varphi+17711\).
- ME-043: \(\varphi^{46}=1836311903\varphi+1134903170\).
- ME-044: \(\varphi^{13}=233\varphi+144\).
- ME-046: the φ-tiled operator is a weighted average, \(C_\varphi[X]=\varphi^{-1}X+\varphi^{-2}A(\varphi X)\), with weights summing to 1.
- ME-085: the Scalar-23 operator is invertible.
- **A negative result for ME-086/088:** \(S_{23}(0)=0\), and only the null state maps to 0, so Scalar-23 scaling cannot turn a null state into a non-zero one.

**Coherence and Red Queen** (`Coherence.lean`)
- For \(a>0\), the potential \(U\) has its minimum \(-b^2/(4a)\) exactly where \(\Phi^2=b/a\).
- The equilibria of the coherence equation are \(\Phi=0\) and \(\Phi^2=b/a\).
- **Lyapunov law:** along \(\tau\dot\Phi=b\Phi-a\Phi^3\), \(U\) never increases. This covers only the coupling-free, noise-free part of ME-024.
- ME-062 gives ME-063, and **an equilibrium exists if and only if \(\beta D-\gamma\dot D\le \alpha K/4\)**, a maximum sustainable disorder load.

**Relaxation, decay and time** (`Dynamics.lean`)
- ME-078 is exactly the unique solution of ME-082 with \(\eta_{eq}=\eta_0\) and \(\eta(0)=0\), and \(\eta(t)\to\eta_0\) over time.
- ME-079 is the unique solution of \(\rho'=-\rho/\tau_n\), with half-life \(\tau_n\ln 2\).
- ME-076 implies ME-075. When \(\omega_{rec}>0\), the accumulated phase is strictly increasing, so it works as a clock.

**Metrics** (`Metrics.lean`)
- ME-047: the coherence score lies in \([0,1]\), and equals 1 exactly when \(x=m\).
- ME-048: recursive integrity is at most the coherence score.
- ME-091: the Kuramoto order parameter lies in \([0,1]\).
- ME-092: KL divergence is non-negative (Gibbs' inequality).
- ME-034: phrase entropy lies between 0 and \(\log n\).
- ME-061: collapse probabilities are non-negative and sum to 1.
- ME-059: the Collapse-Ω minimiser exists for any finite set of outcomes.
- ME-089: risk lies between 0 and \(P(H)\) and does not increase as coherence grows.

**Fields, PDE and recursion** (`Fields.lean`)
- ME-003 reduces to ME-004 in flat spacetime.
- **ME-005 has time coefficient \((1-\alpha^2)/c^2\):** it is a wave equation only when \(\alpha^2<1\), and when \(\alpha^2=1\) it becomes a Poisson equation with no propagation. This is stated pointwise, treating derivative values as numbers.
- ME-006 equals ME-015 plus \(R_{\mu\nu}\), and ME-007 is equivalent to ME-008.
- ME-016 gives ME-017.
- **In ME-036/037 only \(\alpha+\beta\) matters**, and the two equations are mirror images under swapping S and O.
- ME-065 gives \(S_{n+1}=S_nO_nS_n\).
- ME-073/074 make \(T\circ U\) an involution (applying it twice gives the identity).
- ME-094/101 grow linearly without bound when \(\Delta E\cdot C>0\).

**Not derived** (listed in `LAWS.md`):
- Field equations from the action principles (ME-009, ME-013, ME-014).
- The Bianchi-identity consistency condition for ME-007. It is a real constraint, because \(\nabla^\mu R_{\mu\nu}\neq 0\) in general.
- Existence, uniqueness and attractor results (ME-022–033), PDE well-posedness, and the fluid and cosmology items.
- The empirical claims in ME-089–102, beyond the bounds listed above.

The main results are registered in the Properties table as proved.