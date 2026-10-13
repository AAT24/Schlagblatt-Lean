/-
  Schlagblatt / Mitscherlich.lean   (L2)
  The concrete N→resource map is strictly increasing and strictly concave —
  supplying Lemma 1's hypotheses for the actual pipeline (not an abstract g).

      slpf(N) = smax − (smax − smin) · exp(−cN),   0 < smin < smax, c > 0.

  deriv slpf  = (smax−smin)·c·exp(−cN) > 0   (strictly increasing)
  deriv² slpf = −(smax−smin)·c²·exp(−cN) < 0 (strictly concave)
-/
import Mathlib

open Real Set

namespace Schlagblatt

variable (smin smax c : ℝ)

/-- Mitscherlich soil-productivity map. -/
noncomputable def slpf (N : ℝ) : ℝ := smax - (smax - smin) * Real.exp (-(c * N))

/-- First derivative. -/
theorem hasDerivAt_slpf (N : ℝ) :
    HasDerivAt (slpf smin smax c) ((smax - smin) * c * Real.exp (-(c * N))) N := by
  unfold slpf
  have hcy : HasDerivAt (fun y => c * y) c N := by
    simpa using (hasDerivAt_id N).const_mul c
  have hin : HasDerivAt (fun y => -(c * y)) (-c) N := hcy.neg
  have he : HasDerivAt (fun y => Real.exp (-(c * y))) (Real.exp (-(c * N)) * -c) N := hin.exp
  have h2 : HasDerivAt (fun y => (smax - smin) * Real.exp (-(c * y)))
      ((smax - smin) * (Real.exp (-(c * N)) * -c)) N := he.const_mul (smax - smin)
  have h3 := (hasDerivAt_const N smax).sub h2
  have hval : (smax - smin) * c * Real.exp (-(c * N))
      = 0 - (smax - smin) * (Real.exp (-(c * N)) * -c) := by ring
  rw [hval]; exact h3

theorem deriv_slpf (N : ℝ) :
    deriv (slpf smin smax c) N = (smax - smin) * c * Real.exp (-(c * N)) :=
  (hasDerivAt_slpf smin smax c N).deriv

/-- Strictly increasing. -/
theorem slpf_strictMono (hlt : smin < smax) (hc : 0 < c) :
    StrictMono (slpf smin smax c) := by
  apply strictMono_of_deriv_pos
  intro N
  rw [deriv_slpf]
  have hs : 0 < smax - smin := by linarith
  exact mul_pos (mul_pos hs hc) (Real.exp_pos _)

/-- Derivative of the first-derivative function. -/
theorem hasDerivAt_deriv_slpf (N : ℝ) :
    HasDerivAt (fun y => (smax - smin) * c * Real.exp (-(c * y)))
      (-((smax - smin) * c * c) * Real.exp (-(c * N))) N := by
  have hcy : HasDerivAt (fun y => c * y) c N := by
    simpa using (hasDerivAt_id N).const_mul c
  have hin : HasDerivAt (fun y => -(c * y)) (-c) N := hcy.neg
  have he : HasDerivAt (fun y => Real.exp (-(c * y))) (Real.exp (-(c * N)) * -c) N := hin.exp
  have h2 := he.const_mul ((smax - smin) * c)
  have hval : -((smax - smin) * c * c) * Real.exp (-(c * N))
      = (smax - smin) * c * (Real.exp (-(c * N)) * -c) := by ring
  rw [hval]; exact h2

/-- Second derivative. -/
theorem deriv2_slpf (N : ℝ) :
    deriv^[2] (slpf smin smax c) N = -((smax - smin) * c * c) * Real.exp (-(c * N)) := by
  have hfun : deriv (slpf smin smax c) = fun y => (smax - smin) * c * Real.exp (-(c * y)) := by
    funext y; exact deriv_slpf smin smax c y
  change deriv (deriv (slpf smin smax c)) N = _
  rw [hfun]
  exact (hasDerivAt_deriv_slpf smin smax c N).deriv

/-- **Strictly concave** on all of ℝ. -/
theorem slpf_strictConcave (hlt : smin < smax) (hc : 0 < c) :
    StrictConcaveOn ℝ univ (slpf smin smax c) := by
  have hcont : Continuous (slpf smin smax c) := by unfold slpf; fun_prop
  refine strictConcaveOn_of_deriv2_neg convex_univ hcont.continuousOn ?_
  intro N _
  rw [deriv2_slpf]
  have hs : 0 < smax - smin := by linarith
  have hpos : 0 < (smax - smin) * c * c := mul_pos (mul_pos hs hc) hc
  nlinarith [hpos, Real.exp_pos (-(c * N))]

end Schlagblatt
