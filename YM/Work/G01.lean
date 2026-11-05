import YM.Bid.Source

/-!
# G01: pulling the actual scaled holonomy

`pull s 0` evaluates the old configuration at the signed-permuted edge,
so the Taylor components of the connection on the new edge use `turn s.ortho⁻¹`.
For a flipped axis we solve the new ODE by reversing time on the corresponding
positive edge. Separately, **constant** gauge action on the radial variables is
implemented by conjugation, including on the projected curvature readout.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.G01

open Lattice Labels Source RG Wilson
open Source.Drops
open scoped Matrix.Norms.Frobenius BigOperators

variable {G : Gauge}

/-! ### Signed permutation on links -/

private def realSite (x : Cover) : E4 := WithLp.toLp 2 fun i => (x i : ℝ)

private theorem motion_site (s : Signed) (x : Cover) :
    Ortho.motion s.ortho (realSite x) = realSite (s.act x) := by
  rw [Ortho.motion_at, Signed.ortho_move]
  apply PiLp.ext
  intro k
  obtain ⟨i, rfl⟩ := s.perm.surjective k
  cases h : s.flip i <;> simp [realSite, h]

private theorem motion_axis (s : Signed) (i : Axis) :
    Ortho.motion s.ortho (basis i) = (if s.flip i then (-1 : ℝ) else 1) • basis (s.perm i) := by
  apply PiLp.ext
  intro k
  rw [Ortho.motion_at, Ortho.move, M4.move_basis]
  by_cases h : s.perm i = k
  · subst k
    cases hf : s.flip i <;> simp [Signed.ortho, Signed.matrix_at, hf]
  · cases hf : s.flip i <;> simp [Signed.ortho, Signed.matrix_at, h, Ne.symm h]

private theorem realSite_prev (x : Cover) (i : Axis) :
    realSite (x - step i) = realSite x - basis i := by
  apply PiLp.ext
  intro k
  by_cases hk : k = i <;> simp [realSite, hk]

private theorem potential_turn (s : Signed) (d : ℕ) (J : Jet G) (i : Axis) (z : E4) :
    potential d (changedJet (fun _ => Taylor.turn s.ortho⁻¹) J) i z =
      (if s.flip i then (-1 : ℝ) else 1) • potential d J (s.perm i) (Ortho.motion s.ortho z) := by
  unfold potential
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [changedJet, Taylor.turn_value, inv_inv, Ortho.motion_at]
  rw [Finset.sum_eq_single_of_mem (s.perm i) (Finset.mem_univ _)]
  · rw [show s.ortho⁻¹.val i (s.perm i) = star (s.matrix (s.perm i) i) from rfl]
    simp only [star_trivial, s.matrix_at, ↓reduceIte]
  · intro k _ hk
    rw [show s.ortho⁻¹.val i k = star (s.matrix k i) from rfl]
    simp [Signed.matrix_at, Ne.symm hk]

private theorem part_turn (s : Signed) (d : ℕ) (J : Jet G) (h t : ℝ) (x : Cover) (i : Axis) :
    partConnection d (changedJet (fun _ => Taylor.turn s.ortho⁻¹) J) h (x, i) t =
      h • ((if s.flip i then (-1 : ℝ) else 1) •
        potential d J (s.perm i)
          (h • (realSite (s.act x) + t • ((if s.flip i then (-1 : ℝ) else 1) • basis (s.perm i))))) := by
  change h • potential d _ i (h • (realSite x + t • basis i)) = _
  rw [potential_turn, map_smul, map_add, map_smul, motion_axis, motion_site]

/-- For `u'=u A` we multiply the reversed path on the *left* by its
(new) initial value's inverse. This realizes transport for the minus direction. -/
theorem solves_backward {A : ℝ → G.Color} {u : ℝ → G.El} (hu : SolvesLink u A) :
    SolvesLink (fun t => (u 1)⁻¹ * u (1-t)) (fun t => - A (1-t)) := by
  refine ⟨by simp, fun t => ?_⟩
  have hr : HasDerivAt (fun x : ℝ => G.mat (u (1-x)))
      (-(G.mat (u (1-t)) * G.colorMat (A (1-t)))) t :=
    (hu.2 (1-t)).comp_const_sub 1 t
  simpa only [G.mat_mul, mul_assoc, map_neg, mul_neg] using! (hr.const_mul (G.mat ((u 1)⁻¹)))

theorem swirls_of_flow (H : Hol G) : Bid.swirls H := by
  intro s d J h
  funext e
  rcases e with ⟨x, i⟩
  let Y := changedJet (fun _ => Taylor.turn s.ortho⁻¹) J
  change ((posDir i).rotate s).read (H.links d J h) (affine s 0 x) = H.flow d Y h (x,i) 1
  rw [affine, add_zero]
  cases hs : s.flip i with
  | false =>
    have he : partConnection d Y h (x,i) = partConnection d J h (s.act x,s.perm i) := by
      funext t
      unfold Y
      rw [part_turn]
      simp [hs, partConnection, realSite]
    have hu := H.solves d Y h (x,i)
    rw [he] at hu
    rw [show (posDir i).rotate s = posDir (s.perm i) by simp [Step.rotate, posDir, hs],
      Step.pos_read]
    exact congr_fun ((H.solves _ _ _ _).unique hu) 1
  | true =>
    let p : Edge Cover := (s.act x - step (s.perm i), s.perm i)
    have he : partConnection d Y h (x,i) = fun t => - partConnection d J h p (1-t) := by
      funext t
      unfold Y
      rw [part_turn]
      change h • ((if s.flip i then (-1 : ℝ) else 1) • _) =
        -(h • potential d J (s.perm i) (h • (realSite (s.act x - step (s.perm i)) +
          (1-t) • basis (s.perm i))))
      simp only [hs, ↓reduceIte, neg_one_smul, smul_neg, realSite_prev]
      rw [show realSite (s.act x) + -(t • basis (s.perm i)) =
        realSite (s.act x) - basis (s.perm i) + (1-t) • basis (s.perm i) by
          rw [sub_smul, one_smul]
          abel]
    have hu := H.solves d Y h (x,i)
    rw [he] at hu
    rw [show (posDir i).rotate s = negDir (s.perm i) by simp [Step.rotate, posDir, negDir, hs],
      Step.neg_read]
    change (H.flow d J h p 1)⁻¹ = _
    simpa only [sub_self, (H.solves d J h p).1, mul_one] using
      congr_fun ((solves_backward (H.solves d J h p)).unique hu) 1

/-! ### Gauge action -/

theorem solves_adjoint (q : G.El) {A : ℝ → G.Color} {u : ℝ → G.El} (hu : SolvesLink u A) :
    SolvesLink (fun t => q * u t * q⁻¹) (fun t => G.adjoint q (A t)) := by
  refine ⟨by simp [hu.1], fun t => ?_⟩
  simp only [G.mat_mul, G.mat_inv, G.mat_adjoint, Gauge.conjugate]
  have hd := ((hu.2 t).const_mul (G.mat q)).mul_const (star (G.mat q))
  apply hd.congr_deriv
  rw [show G.mat q * G.mat (u t) * star (G.mat q) * (G.mat q * G.colorMat (A t) * star (G.mat q)) =
      G.mat q * G.mat (u t) * (star (G.mat q) * G.mat q) * G.colorMat (A t) * star (G.mat q) by
        simp only [mul_assoc], G.mat_star_mul, mul_one]
  simp only [mul_assoc]

theorem links_colored (H : Hol G) (d : ℕ) (q : G.El) (J : Jet G) (h : ℝ) :
    H.links d (colored q J) h = gauge (fun _ => q) (H.links d J h) := by
  funext p
  have he : partConnection d (colored q J) h p = fun t => G.adjoint q (partConnection d J h p t) := by
    funext t
    simp only [partConnection, potential, colored, Taylor.paint_value, map_smul, map_sum]
  have hn := H.solves d (colored q J) h p
  rw [he] at hn
  exact congr_fun (hn.unique (solves_adjoint q (H.solves d J h p))) 1

/-- The based slot eval retains only the gauge action at the origin:
its curvature is *transported* and uses the actual real Lie projection. -/
theorem slot_eval_gauge (v : Slot) (U : CoverConfig G) (q : Cover → G.El) :
    v.eval (gauge q U) = G.adjoint (q 0) (v.eval U) := by
  simp only [Slot.eval, travel_gauge, face_gauge, Gauge.curvature_conjugate]
  rw [Slot.offset]
  rw [← G.adjoint_mul, ← G.adjoint_mul]
  rw [inv_mul_cancel_right]

theorem answer : YM.Bid.G01 := by
  intro G H
  refine ⟨swirls_of_flow H, fun d v u A => ?_⟩
  have he : expand d (Cast u A) = colored u (expand d A) := by
    funext i
    by_cases h : i < d-1 <;> simp [expand, h, Cast, colored]
  unfold takes
  rw [he, links_colored, slot_eval_gauge]

end YM.Work.G01
