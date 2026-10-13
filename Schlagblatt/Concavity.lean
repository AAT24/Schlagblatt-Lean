/-
  Schlagblatt / Concavity.lean
  Formal core of the nitrogen optimization (Prop 1 + Thm A3).

  Interface principle
  -------------------
  The black-box pipeline (DSSAT, sugar GBM, loss model) supplies the response
  maps g = Y_F and h = (S - L)/100 together with their first/second derivatives.
  Whether these satisfy the sign hypotheses below is the MODELING question
  (validation conditions V1-V2: slpf-concavity after calibration; sugar
  monotonicity on the PD curve). Lean does not see DSSAT; it proves the
  mathematical IMPLICATION:  sign hypotheses  =>  B concave  =>  N*_BZE <= N*_raw.
-/
import Mathlib

open Set

namespace Schlagblatt

variable {Nmax : ℝ}

/-- The response data on the feasible interval `I = Icc 0 Nmax`.
    `g = Y_F` (fresh yield), `h = (S - L)/100` (recoverable fraction);
    `gp,gpp,hp,hpp` are their first/second derivatives. -/
structure ResponseHyp (Nmax : ℝ) where
  g   : ℝ → ℝ
  h   : ℝ → ℝ
  gp  : ℝ → ℝ
  gpp : ℝ → ℝ
  hp  : ℝ → ℝ
  hpp : ℝ → ℝ
  g_pos  : ∀ x ∈ Icc (0:ℝ) Nmax, 0 < g x        -- fresh yield positive
  h_pos  : ∀ x ∈ Icc (0:ℝ) Nmax, 0 < h x        -- recoverable fraction positive
  gp_pos : ∀ x ∈ Icc (0:ℝ) Nmax, 0 ≤ gp x       -- g increasing  (slpf saturation)
  gpp_np : ∀ x ∈ Icc (0:ℝ) Nmax, gpp x ≤ 0      -- g concave     (Lemma 1)
  hp_neg : ∀ x ∈ Icc (0:ℝ) Nmax, hp x < 0       -- h strictly decreasing (S↓, L↑)
  hpp_np : ∀ x ∈ Icc (0:ℝ) Nmax, hpp x ≤ 0      -- h concave/affine (Lemma 2)
  -- The supplied maps are the genuine derivatives (globally; the Mitscherlich
  -- and affine instances satisfy this via Mitscherlich.lean). These primitive
  -- facts discharge the analytic bridge `deriv^[2] B = Bsecond R` below.
  hg_hasderiv  : ∀ x : ℝ, HasDerivAt g (gp x) x
  hgp_hasderiv : ∀ x : ℝ, HasDerivAt gp (gpp x) x
  hh_hasderiv  : ∀ x : ℝ, HasDerivAt h (hp x) x
  hhp_hasderiv : ∀ x : ℝ, HasDerivAt hp (hpp x) x

/-- Second derivative of `B = g·h` via the product rule:
    `B'' = g''h + 2 g'h' + g h''`. -/
def Bsecond (R : ResponseHyp Nmax) (x : ℝ) : ℝ :=
  R.gpp x * R.h x + 2 * R.gp x * R.hp x + R.g x * R.hpp x

/-- **Proposition 1 (heart).** Wherever `g` is strictly increasing
    (`0 < gp x`), the second derivative of BZE is strictly negative:
    the cross term `2 g'h'` is `< 0`, the other two terms are `≤ 0`. -/
theorem Bsecond_neg (R : ResponseHyp Nmax) {x : ℝ}
    (hx : x ∈ Icc (0:ℝ) Nmax) (hgp : 0 < R.gp x) :
    Bsecond R x < 0 := by
  have h1 : R.gpp x * R.h x ≤ 0 := by
    nlinarith [R.gpp_np x hx, R.h_pos x hx]
  have h2 : 2 * R.gp x * R.hp x < 0 := by
    nlinarith [hgp, R.hp_neg x hx]
  have h3 : R.g x * R.hpp x ≤ 0 := by
    nlinarith [R.g_pos x hx, R.hpp_np x hx]
  unfold Bsecond
  linarith [h1, h2, h3]

/-- Nonstrict form on the whole interval (uses only `gp ≥ 0`):
    `B'' ≤ 0`, the basis of (non-strict) concavity. -/
theorem Bsecond_nonpos (R : ResponseHyp Nmax) {x : ℝ}
    (hx : x ∈ Icc (0:ℝ) Nmax) : Bsecond R x ≤ 0 := by
  have h1 : R.gpp x * R.h x ≤ 0 := by
    nlinarith [R.gpp_np x hx, R.h_pos x hx]
  have h2 : 2 * R.gp x * R.hp x ≤ 0 := by
    nlinarith [R.gp_pos x hx, R.hp_neg x hx]
  have h3 : R.g x * R.hpp x ≤ 0 := by
    nlinarith [R.g_pos x hx, R.hpp_np x hx]
  unfold Bsecond
  linarith [h1, h2, h3]

/-- Product rule for `B = g·h`: `HasDerivAt B (g'h + gh')` at every `x`. -/
theorem hasDerivAt_B (R : ResponseHyp Nmax) (x : ℝ) :
    HasDerivAt (fun y => R.g y * R.h y) (R.gp x * R.h x + R.g x * R.hp x) x :=
  (R.hg_hasderiv x).mul (R.hh_hasderiv x)

/-- Hence `deriv B` is the product-rule function, everywhere. -/
theorem deriv_B_eq (R : ResponseHyp Nmax) :
    deriv (fun y => R.g y * R.h y) = fun x => R.gp x * R.h x + R.g x * R.hp x := by
  funext x; exact (hasDerivAt_B R x).deriv

/-- Differentiating `deriv B` again yields exactly `Bsecond R x`. -/
theorem hasDerivAt_derivB (R : ResponseHyp Nmax) (x : ℝ) :
    HasDerivAt (fun y => R.gp y * R.h y + R.g y * R.hp y) (Bsecond R x) x := by
  have t1 : HasDerivAt (fun y => R.gp y * R.h y)
      (R.gpp x * R.h x + R.gp x * R.hp x) x := (R.hgp_hasderiv x).mul (R.hh_hasderiv x)
  have t2 : HasDerivAt (fun y => R.g y * R.hp y)
      (R.gp x * R.hp x + R.g x * R.hpp x) x := (R.hg_hasderiv x).mul (R.hhp_hasderiv x)
  have hsum := t1.add t2
  have hval : R.gpp x * R.h x + R.gp x * R.hp x + (R.gp x * R.hp x + R.g x * R.hpp x)
      = Bsecond R x := by unfold Bsecond; ring
  rwa [hval] at hsum

/-- The analytic bridge, now a theorem: `deriv^[2] B = Bsecond R`. -/
theorem deriv2_B_eq (R : ResponseHyp Nmax) (x : ℝ) :
    deriv^[2] (fun y => R.g y * R.h y) x = Bsecond R x := by
  change deriv (deriv (fun y => R.g y * R.h y)) x = _
  rw [deriv_B_eq R]
  exact (hasDerivAt_derivB R x).deriv

/-- **Proposition 1 (concavity), self-contained.** `B = g·h` is concave on
    `Icc 0 Nmax` with no assumed analytic bridge: the `HasDerivAt` fields of
    `ResponseHyp` discharge the `deriv^[2] B = Bsecond R` step, and the sign
    hypotheses give `Bsecond R ≤ 0`. -/
theorem B_concave (R : ResponseHyp Nmax) :
    ConcaveOn ℝ (Icc 0 Nmax) (fun x => R.g x * R.h x) := by
  have hg_diff  : Differentiable ℝ R.g  := fun x => (R.hg_hasderiv x).differentiableAt
  have hh_diff  : Differentiable ℝ R.h  := fun x => (R.hh_hasderiv x).differentiableAt
  have hgp_diff : Differentiable ℝ R.gp := fun x => (R.hgp_hasderiv x).differentiableAt
  have hhp_diff : Differentiable ℝ R.hp := fun x => (R.hhp_hasderiv x).differentiableAt
  have hB_diff : Differentiable ℝ (fun x => R.g x * R.h x) := hg_diff.mul hh_diff
  have hderivB_diff : Differentiable ℝ (deriv (fun x => R.g x * R.h x)) := by
    rw [deriv_B_eq R]; exact (hgp_diff.mul hh_diff).add (hg_diff.mul hhp_diff)
  refine concaveOn_of_deriv2_nonpos (convex_Icc 0 Nmax)
    hB_diff.continuous.continuousOn hB_diff.differentiableOn
    hderivB_diff.differentiableOn ?_
  intro x hx
  rw [deriv2_B_eq R]
  exact Bsecond_nonpos R (interior_subset hx)

/-- **Theorem A3 (monotone N reduction), abstract.**
    `B = B0 - P` with `P` strictly increasing at `b` (i.e. `P'(b) > 0`), `B`
    strictly concave; `a` and `b` the interior stationary points of `B` and `B0`
    (their unique maximisers). Then `a ≤ b`: the BZE optimum never exceeds the
    raw optimum.

    Proof: `B'(b) = B0'(b) - P'(b) = -P'(b) < 0`; `B'` is strictly antitone on the
    interior (strict concavity) and `B'(a) = 0 > B'(b)`, hence `a ≤ b`. -/
theorem nstar_monotone
    (B B0 P : ℝ → ℝ) (a b : ℝ)
    (hPB : B = fun x => B0 x - P x)
    (hBdiff : ∀ x ∈ Icc (0:ℝ) Nmax, DifferentiableAt ℝ B x)
    (hB0diff : DifferentiableAt ℝ B0 b)
    (hPdiff : DifferentiableAt ℝ P b)
    (hP'pos : 0 < deriv P b)
    (hB0crit : deriv B0 b = 0)
    (hBcrit : deriv B a = 0)
    (hBconc : StrictConcaveOn ℝ (Icc 0 Nmax) B)
    (ha : a ∈ Ioo (0:ℝ) Nmax) (hb : b ∈ Ioo (0:ℝ) Nmax) :
    a ≤ b := by
  have hBb : deriv B b < 0 := by
    have h1 : deriv B b = deriv B0 b - deriv P b := by
      rw [hPB]; exact deriv_sub hB0diff hPdiff
    rw [h1, hB0crit]; linarith [hP'pos]
  have hanti : StrictAntiOn (deriv B) (Icc (0:ℝ) Nmax) :=
    hBconc.strictAntiOn_deriv hBdiff
  have ha' : a ∈ Icc (0:ℝ) Nmax := Ioo_subset_Icc_self ha
  have hb' : b ∈ Icc (0:ℝ) Nmax := Ioo_subset_Icc_self hb
  by_contra hcon
  rw [not_le] at hcon              -- hcon : b < a
  have key := hanti hb' ha' hcon   -- deriv B a < deriv B b
  rw [hBcrit] at key               -- 0 < deriv B b
  linarith [hBb]

end Schlagblatt
