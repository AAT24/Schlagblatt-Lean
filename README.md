# Schlagblatt Lean formalization

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
