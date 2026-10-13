# Schlagblatt — Lean formalization

Machine-checked core of the nitrogen optimization (companion to
`docs/optimization_formulation.md`). We formalize the **abstract implication**,
not the crop models: the pipeline supplies response maps `g = Y_F`,
`h = (S-L)/100` with derivative-sign hypotheses (justified by the modeling /
validation conditions V1–V2); Lean proves

```
sign hypotheses  ⟹  B'' < 0  ⟹  B concave  ⟹  N*_BZE ≤ N*_raw .
```

## Status

| result | Lean object | state |
|--------|-------------|-------|
| Prop 1 (B'' < 0, strict) | `Bsecond_neg` | **proved** (nlinarith + linarith) |
| Prop 1 (B'' ≤ 0)         | `Bsecond_nonpos` | **proved** |
| Prop 1 (concavity)       | `B_concave` | proved **modulo** analytic bridge `hderiv2` |
| Thm A3 (monotone N*)     | `nstar_monotone` | statement done, proof `sorry` |

The two `Bsecond_*` lemmas are the mathematical heart and are self-contained.
Open work: (a) fill the `HasDerivAt` chain so `deriv^[2] B = Bsecond R` instead
of taking it as a hypothesis; (b) discharge `nstar_monotone` (interior-maximiser
⟹ critical point; strict-concave ⟹ strictly-decreasing derivative).

## Build (needs the toolchain installed)

```bash
# 1. install elan (Lean version manager) if absent
#    https://github.com/leanprover/elan
# 2. reconcile toolchain with the pinned Mathlib, then build
cd lean
lake update mathlib
cp .lake/packages/mathlib/lean-toolchain ./lean-toolchain   # match versions
lake exe cache get            # download prebuilt Mathlib (avoids hours of build)
lake build
```

`lake build` reports remaining `sorry`s as warnings; `Bsecond_neg` /
`Bsecond_nonpos` must compile with none.
