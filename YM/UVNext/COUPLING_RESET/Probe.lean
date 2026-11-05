import Mathlib.Analysis.Complex.ExponentialBounds
import YM.Push.BETA_TRANSPORT.Comparisons
import YM.Push.BETA_TRANSPORT.Separation
import YM.Push.PRICE_COMPILER.Suppression



set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Uniform two-test separation with the true clipped action (eq:ved)

Strengthening the separation of BETA_TRANSPORT for reset *estimates*: at
some common unflagged finite amplitude the coefficient of beta has size at
least `sites * η * threshold^2` with η>0 already fixed stagewise, not
period-dependent. A transverse alternating line test works on EVERY even
side (as in the calendar). The signs/averages need not preserve this field,
only the summed direct plaquette charge. No small-field truncation of the
cubic & quartic coefficients and no assumption of contractibility on the
whole torus. This doesn't show that any loop/log or activity estimates at
the separating tests have the accuracy needed for a reset.
-/

set_option autoImplicit false
noncomputable section
namespace YM.UVNext.CouplingReset
open Push.BetaTransport Lattice Wilson RG Filter Function Set
open scoped Matrix.Norms.Frobenius Topology BigOperators ContDiff

variable {G : Gauge} {n : Side}

/-- Per-site normalization in `Rep.exponent`. -/
def sites (n : Side) : ℝ := Fintype.card (Site n)
lemma sites_pos (n : Side) : 0 < sites n := Nat.cast_pos.mpr Fintype.card_pos

lemma reachable_chord (G : Gauge) [Nontrivial G.Color] :
    ∃ ε : ℝ, 0 < ε ∧ ∀ h ∈ Icc (0:ℝ) ε, ∃ u : G.El, G.chord u = h := by
  obtain ⟨c,hc⟩ := exists_ne (0:G.Color)
  let γ (t : ℝ) := G.lieExp (t • c)
  obtain ⟨t,ht⟩ : ∃ t : ℝ, 0 < G.chord (γ t) := by
    by_contra! ha
    have hz : (fun t => G.curvature (γ t)) = fun _ => 0 := funext fun t => norm_le_zero_iff.mp <|
      (G.curvature_norm _).trans (ha t)
    have hd : HasDerivAt (fun t => G.curvature (γ t)) c 0 := G.leading_curvature c
    rw [hz] at hd
    exact hc (hd.unique (hasDerivAt_const _ _))
  have hg : Continuous (fun t => G.chord (γ t)) := G.continuous_chord.comp (G.lieExp_cont.comp (by fun_prop))
  refine ⟨_,ht,fun h hh => ?_⟩
  obtain ⟨x,hx⟩ := intermediate_value_univ 0 t hg (show h ∈ Icc (G.chord (γ 0)) _ by simpa [γ] using hh)
  exact ⟨γ x,hx⟩

private def stripe (u : G.El) (he : 2 ∣ n.val) : Config G n :=
  fun i => if i.2 = 0 ∧ ZMod.castHom he (ZMod 2) (i.1 1) = 0 then u else 1

private def plane : PlaqAxes := ⟨(0,1), by decide⟩

private lemma stripe_plane (u : G.El) (he : 2 ∣ n.val) (x : Site n) :
    G.chord (faceValue (stripe u he) (x,plane)) = G.chord u := by
  let v := ZMod.castHom he (ZMod 2) (x 1)
  have hy : ∀ v : ZMod 2, v ≠ 0 → v+1=0 := by decide
  have h1 : ZMod.cast (1:ZMod n.val) = (1:ZMod 2) := map_one (ZMod.castHom he _)
  by_cases hv : v = 0
  · simp [faceValue, square, plane, travel,stripe,map_add, h1, show (ZMod.cast (x 1) : ZMod 2) = 0 from hv]
  simp [faceValue, square, plane, travel,stripe,map_add,h1,show (ZMod.cast (x 1) : ZMod 2) ≠ 0 from hv, show ZMod.cast (x 1)+1 = (0:ZMod 2) from hy v hv,G.chord_inv]

private lemma direct_probe (D : PathData G) (A : Clip) (P : BudgetPoint) (u : G.El) (he : 2 ∣ n.val)
    (hf : ∀ p, G.chord (faceValue (stripe u he) p) ≤ P.threshold) (s : Signed) :
    sites n * (A.direct * G.chord u ^ 2 / 2) ≤ ∑ p, D.baseTerm A P (pull s 0 (stripe u he)) p := by
  let F (U : Config G n) p := A.direct * G.chord (faceValue U p) ^ 2 / 2
  let U := stripe u he
  let V := pull s 0 U
  let σ := Equiv.ofBijective (Face.send s (0:Site n)) ⟨Face.injective_send s _,
    Finite.injective_iff_surjective.mp (Face.injective_send s _)⟩
  have hp p : G.chord (faceValue V p) = G.chord (faceValue U (σ p)) :=
    Face.send_price U _ _ _ G.chord G.chord_inv (fun k g => G.chord_conj g k)
  have hA := A.quadratic_pos
  calc
    sites n * _ = ∑ x : Site n, F U (x,plane) := by simp [F,U,stripe_plane,sites]
    _ ≤ ∑ p, F U p := by
      rw [Fintype.sum_prod_type]; exact Finset.sum_le_sum fun x _ => Finset.single_le_sum
        (f := fun p => F U (x,p)) (fun p _ => by dsimp [F]; positivity) (Finset.mem_univ plane)
    _ = ∑ p, F V p := (Fintype.sum_equiv σ (F V) (F U) (fun p => by simp [F,hp])).symm
    _ ≤ _ := Finset.sum_le_sum fun p _ => base_lower (D:=D) A p ((hp p).trans_le (hf _))

/-- What a stage-wise separation constant buys. Depends on the
precommitted path caps, *not* their periodizations, beta or loop estimates.
The probe can be reused at all input/output couplings at this step. -/
def Sensor (G : Gauge) (A : Clip) (C η : ℝ) := 0 < η ∧
  ∀ (n : Side), 2 ∣ n.val → ∀ (D : PathData G) (P : BudgetPoint) (σ Λ : ℝ), D.Bounds A σ C Λ →
    ∃ U : Config G n, flags P.threshold U = ∅ ∧ sites n * (η*P.threshold^2) ≤ kinetic D A P U

theorem sensor (G : Gauge) [Nontrivial G.Color] (A : Clip) (C : ℝ) (hC : 0 ≤ C) : ∃ η, Sensor G A C η := by
  obtain ⟨ε,hε,hg⟩ := reachable_chord G
  let t := min (min ε (1/4)) (A.direct/(512*(1+C)))
  have hA := A.quadratic_pos
  have htp : 0 < t := lt_min (lt_min hε (by norm_num)) (by positivity)
  refine ⟨A.direct*t^2/4,by positivity,fun n he D P σ Λ hD => ?_⟩
  let h := t * P.threshold
  have hP := P.threshold_pos
  have hh : 0 ≤ h := (mul_pos htp hP).le
  have hh' : h ≤ t := mul_le_of_le_one_right htp.le P.threshold_le
  obtain ⟨u,hu⟩ := hg _ ⟨hh,hh'.trans ((min_le_left ..).trans (min_le_left ..))⟩
  let U := stripe u he
  have hf p : G.chord (faceValue U p) ≤ 4*h := by
    have hb (i) : G.chord (U i) ≤ h := by unfold U stripe; split <;> simp [*]
    simpa [faceValue,square] using Next.Fluctuations.travel_chord U (square p.2.val.1 p.2.val.2) p.1 h hb
  have hz : 4*h ≤ P.threshold := by
    have hle := mul_le_mul_of_nonneg_right (show t ≤ 1/4 from (min_le_left ..).trans (min_le_right ..)) hP.le
    dsimp [h]; linarith
  refine ⟨U, flags_empty (fun p => (hf p).trans hz), ?_⟩
  let T := A.direct * t^2 / 4 * P.threshold^2
  let N := sites n
  change N * T ≤ _
  rw [kinetic, le_inv_mul_iff₀ (by exact_mod_cast (Fintype.card_pos (α:=Signed)))]
  have H (s : Signed) : N*T ≤ (∑ p, D.baseTerm A P (pull s 0 U) p) + ∑ x : Site n,
      (PathData.atomSeries D.cubic P (pull s 0 U) x + PathData.atomSeries D.quartic P (pull s 0 U) x) := by
    have hm p : G.chord (faceValue (pull s 0 U) p) ≤ 4*h :=
      (Face.send_price U _ _ _ G.chord G.chord_inv (fun k g => G.chord_conj g k)).trans_le (hf _)
    have hx := direct_probe D A P u he (fun p => (hf p).trans hz) s
    rw [hu] at hx
    have h₄ : 0 ≤ 4*h := by positivity
    have hsmall : C*(4*h)^3+C*(4*h)^4 ≤ A.direct*h^2/4 := calc
      _ ≤ C*(4*h)^3 + C*(4*h)^3 := by
        exact add_le_add_right (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one h₄ (hz.trans P.threshold_le)
          (by decide : (3:ℕ) ≤ 4)) hC) _
      _ = ((512*C)*h)*h^2/4 := by ring
      _ ≤ _ := by
        have hb := (le_div_iff₀ (show (0:ℝ) < 512*(1+C) by positivity)).mp (show t ≤ A.direct / _ from min_le_right ..)
        have hcost : 512*C*h ≤ A.direct := by nlinarith
        gcongr
    have hterm (x : Site n) : -(A.direct*h^2/4) ≤ PathData.atomSeries D.cubic P (pull s 0 U) x +
          PathData.atomSeries D.quartic P (pull s 0 U) x := by
      have h1 := neg_le_of_abs_le (atomSeries_chord (P:=P) hD.width hD.three h₄ hm x)
      have h2 := neg_le_of_abs_le (atomSeries_chord (P:=P) hD.width hD.four h₄ hm x)
      linarith only [h1,h2,hsmall]
    have hb := add_le_add hx (Finset.sum_le_sum (s:=Finset.univ) fun x _ => hterm x)
    exact le_trans (le_of_eq (by simp [Finset.sum_const,N,sites,h,T]; ring)) hb
  simpa using Finset.sum_le_sum (s:=Finset.univ) (fun s _ => H s)

lemma flags_one (P : BudgetPoint) : flags P.threshold (1 : Config G n) = ∅ :=
  flags_empty fun p => by simp [faceValue,square,travel,P.threshold_pos.le]

lemma loop_one (D : PathData G) (A : Clip) (P : BudgetPoint) : D.inChannels A P 0 (1 : Config G n) = 0 := by
  have he (s : Signed) : pull s 0 (1:Config G n) = 1 := by funext e; unfold pull Step.read; split <;> simp
  have hu (b : Face (Per n)) : faceValue (1:Config G n) b = 1 := by simp [faceValue,travel,square]
  have ht (x : Site n) (l : Slot) : l.atSite (1:Config G n) x = 0 := by rw [Work.F03.atSite_path,hu,G.curvature_unit,map_zero]
  have ha (x : Site n) (i : ℕ) : (D.loop i).placed P (1:Config G n) x = 0 := by
    unfold Atom.placed
    by_cases hh : Healthy P.threshold ((D.loop i).footprint x) (1:Config G n)
    · rw [masked_eq _ _ _ _ hh]; simp [Atom.unmasked,Atom.poly,ht]
    exact masked_ne _ _ _ _ hh
  simp [PathData.inChannels,PathData.principal,PathData.atomSeries,he,ha]

open Activities
variable {S : Activities G n} {P : BudgetPoint}

lemma additive_one (h : ∀ i, S.E i 1 = 0) : S.additive P 1 = 0 := by
  have h₀ i : S.regularOccurrence P i 1 = 0 := by
    unfold regularOccurrence; by_cases hh : Healthy P.threshold (S.reg i).support (1:Config G n)
    · rw [masked_eq _ _ _ _ hh,h]
    rw [masked_ne _ _ _ _ hh]
  simp [additive,h₀]

end YM.UVNext.CouplingReset
