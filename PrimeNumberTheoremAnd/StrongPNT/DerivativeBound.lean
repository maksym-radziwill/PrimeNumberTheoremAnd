/-
Copyright (c) 2025 Maksym Radziwill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maksym Radziwill
-/

import Mathlib.Analysis.Analytic.Constructions
import Mathlib.NumberTheory.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Analytic.Within
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import «PrimeNumberTheoremAnd».StrongPNT.BorelCaratheodory
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.Deriv.Basic

theorem borelCaratheodory_deriv'' {R M r : ℝ} {f : ℂ → ℂ}
  (analytic_f : AnalyticOn ℂ f (Metric.closedBall 0 R))
  (f_zero_at_zero : f 0 = 0) (M_pos : 0 < M)
  (re_f_le_M : ∀ z ∈ Metric.closedBall 0 R, (f z).re ≤ M)
  (pos_r : 0 < r) (r_le_R : r < R) : ‖(deriv f) 0‖ ≤ 2 * M / (R - r) := by

  have borel : ∀ z ∈ Metric.closedBall 0 r, ‖f z‖ ≤ (2 * M * r) / (R - r) := by
    intro z hyp_z
    apply borelCaratheodory_closedBall
    · linarith
    · exact analytic_f
    · exact f_zero_at_zero
    · exact M_pos
    · exact re_f_le_M
    · exact r_le_R
    · exact hyp_z

  have hC : ∀ z ∈ Metric.sphere 0 r, ‖f z‖ ≤ 2 * M * r / (R - r) := by
    intro z hyp_z
    have U : z ∈ Metric.closedBall 0 r := by
      apply Set.mem_of_subset_of_mem (by apply Metric.sphere_subset_closedBall)
      · exact hyp_z

    exact borel z U

  have hf : DiffContOnCl ℂ f (Metric.ball 0 r) := by
    apply DifferentiableOn.diffContOnCl
    · apply DifferentiableOn.mono (t := Metric.closedBall 0 r)
      · apply DifferentiableOn.mono (t := Metric.closedBall 0 R)
        · exact AnalyticOn.differentiableOn analytic_f
        · apply Metric.closedBall_subset_closedBall
          · exact le_of_lt r_le_R
      · apply Metric.closure_ball_subset_closedBall

  have U := by apply Complex.norm_deriv_le_aux pos_r hf hC

  -- Have a series of bounds and can then squeeze r = 0 out of the bound
  -- so we get |f'(0)| ≤ 2 M / R.
  -- Now this should easily imply the other bound since at any point
  -- we have R - r of space at least, hence the bound 2 M / (R - r)

  have Z : r ≠ 0 := by grind
  rw [div_right_comm] at U
  rw [mul_div_cancel_right₀ (2 * M) Z] at U
  exact U

theorem borelCaratheodory_deriv' {R M : ℝ} {f : ℂ → ℂ}
  (analytic_f : AnalyticOn ℂ f (Metric.closedBall 0 R))
  (f_zero_at_zero : f 0 = 0) (M_pos : 0 < M) (R_pos : 0 < R)
  (re_f_le_M : ∀ z ∈ Metric.closedBall 0 R, (f z).re ≤ M)
  : ‖(deriv f) 0‖ ≤ 2 * M / R := by

  by_contra h
  push_neg at h

  let ε := R - 4 * M / ( ‖(deriv f) 0‖ + 2 * M / R )
  have ε_pos : 0 < ε := by
    unfold ε
    simp
    rw [div_lt_iff₀' (by positivity) ]
    calc 4 * M
      _ = (2 * M / R + 2 * M / R) * R := by ring_nf; field_simp
      _ < (‖deriv f 0‖ + 2 * M / R) * R := by gcongr

  have ε_le_R : ε < R := by
    unfold ε
    simp
    positivity

  have := borelCaratheodory_deriv'' analytic_f f_zero_at_zero M_pos re_f_le_M ε_pos ε_le_R

  unfold ε at this
  simp [div_div_eq_mul_div] at this
  ring_nf at this
  have : ‖deriv f 0‖ ≤ 2 * M / R := by
    have h1 : M * ‖deriv f 0‖ * M⁻¹ * (1 / 2) = ‖deriv f 0‖ / 2 := by field_simp
    have h2 : M ^ 2 * R⁻¹ * M⁻¹ = M / R := by field_simp
    rw [h1, h2] at this
    have h3 : ‖deriv f 0‖ - ‖deriv f 0‖ / 2 ≤ M / R := by linarith
    have h4 : ‖deriv f 0‖ / 2 ≤ M / R := by linarith
    grind

  linarith

/-- The correct formulation: need ‖z‖ ≤ r -/
theorem mapsTo_closedBall_translate_correct
    {z : ℂ} (r R : ℝ) (hz : ‖z‖ ≤ r) :
    Set.MapsTo (fun w ↦ w + z) (Metric.closedBall 0 (R - r)) (Metric.closedBall 0 R) := by
  intro w hw
  simp
  calc ‖w + z‖
      ≤ ‖w‖ + ‖z‖ := by apply norm_add_le
    _ ≤ (R - r) + r := by gcongr; simp at hw; exact hw
    _ = R := by ring


theorem borelCaratheodory_deriv {R M r : ℝ} {z : ℂ} {f : ℂ → ℂ}
  (analytic_f : AnalyticOn ℂ f (Metric.closedBall 0 R))
  (f_zero_at_zero : f 0 = 0) (M_pos : 0 < M) (R_pos : 0 < R)
  (re_f_le_M : ∀ z ∈ Metric.closedBall 0 R, (f z).re ≤ M)
  (r_le_R : r < R) (zInBall : z ∈ Metric.closedBall 0 r)
  : ‖(deriv f) z‖ ≤ 4 * M * R / (R - r)^2 := by

  have U4 : ∀ w ∈ Metric.closedBall 0 (R - r), (w + z) ∈ Metric.closedBall 0 R := by
    intro w hyp_w
    rw [mem_closedBall_iff_norm']
    rw [mem_closedBall_iff_norm'] at hyp_w
    rw [mem_closedBall_iff_norm'] at zInBall
    simp at hyp_w
    simp at zInBall
    have T : ‖0 - (w + z)‖ = ‖w + z‖ := by rw [zero_sub]; rw [norm_neg]
    rw [T]
    calc ‖w + z‖
      _ ≤ ‖w‖ + ‖z‖ := by apply norm_add_le
      _ ≤ R := by linarith

  have Y : z ∈ Metric.ball 0 R := by
    simp at zInBall
    simp
    grind
  have Y1 : z ∈ Metric.closedBall 0 R := by
    simp at Y
    simp
    grind

  let g := fun w ↦ f (w + z) - f z
  have : AnalyticOn ℂ g (Metric.closedBall 0 (R - r)) := by
    unfold g
    apply AnalyticOn.sub
    · intro w hw

      have : (fun w ↦ f (w + z)) = f ∘ (fun w ↦ w + z) := by
        funext w
        simp
      rw [this]
      apply AnalyticWithinAt.comp (t := Metric.closedBall 0 R)
      · exact analytic_f (w + z) (U4 w hw)
      · apply AnalyticWithinAt.add
        · apply analyticAt_id.analyticWithinAt
        · apply analyticAt_const.analyticWithinAt
      · apply mapsTo_closedBall_translate_correct
        · simp at zInBall
          exact zInBall
    · apply analyticOn_const

  have U : 0 < M + ‖f z‖ := by positivity

  have Z := by
    apply borelCaratheodory_deriv' this
    · unfold g; simp
    · exact U
    · linarith
    · unfold g
      intro w hyp_w

      have U0 : (f (w + z)).re ≤ M := re_f_le_M (w + z) (U4 w hyp_w)

      calc (f (w + z) - f z).re
        _ = (f (w + z)).re + (- f z).re := by simp; grind
        _ ≤ M + (- (f z)).re := by gcongr
        _ ≤ M + ‖- (f z)‖ := by gcongr; apply Complex.re_le_norm
        _ = M + ‖f z‖ := by rw [norm_neg]

  have S : ‖f z‖ ≤ 2 * M * r / (R - r) := by
    apply borelCaratheodory_closedBall
    · exact R_pos
    · exact analytic_f
    · exact f_zero_at_zero
    · exact M_pos
    · exact re_f_le_M
    · exact r_le_R
    · exact zInBall

  have U : deriv g 0 = deriv f z := by
    unfold g
    simp
    have : (fun w ↦ f (w + z)) = f ∘ (fun w ↦ w + z) := by
        funext w
        simp
    rw [this]
    rw [deriv.scomp]
    · simp
    · simp
      have := analytic_f z Y1
      apply DifferentiableOn.differentiableAt (s := Metric.ball z (R - r))
      · rw [← Complex.analyticOn_iff_differentiableOn]
        · apply AnalyticOn.mono (s := Metric.ball z (R - r)) (t := Metric.closedBall 0 R)
          · exact analytic_f
          · rw [Set.subset_def]
            intro x hyp_x
            simp at hyp_x
            simp
            have := calc ‖x‖
              _ = ‖x - z + z‖ := by simp
              _ ≤ ‖x - z‖ + ‖z‖ := by apply norm_add_le
              _ < R - r + ‖z‖ := by gcongr; rw [← Complex.dist_eq]; exact hyp_x
              _ ≤ R - r + r := by gcongr; simp at zInBall; exact zInBall
              _ = R := by simp
            linarith


        · apply Metric.isOpen_ball
      apply Metric.ball_mem_nhds
      · linarith

    · simp

  rw [U] at Z
  calc ‖deriv f z‖
    _ ≤ 2 * (M + ‖f z‖) / (R - r) := by exact Z
    _ ≤ 2 * (M + 2 * M * r / (R - r)) / (R - r) := by gcongr; linarith
    _ = 2 * (M * (R - r) / (R - r) + 2 * M * r / (R - r)) / (R - r) := by congr; field_simp; rw [eq_comm]; grind
    _ = 2 * M * (R + r) / (R - r)^2 := by grind
    _ ≤ 2 * M * (R + R) / (R - r)^2 := by gcongr
    _ = 4 * M * R / (R - r)^2 := by ring_nf





