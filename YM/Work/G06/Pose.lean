import YM.Analysis.SmoothJets
import YM.Work.G06.Average

/-!
# G06: symmetrized section remains of high valuation

Substitute rotated curvature slots, encoding into another common family whose
length is finite. Multiplication by a sign doesn't change the slot count, and
the inverse tensor action respects the slot grade of the input coordinate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.G06
open Lattice Labels RG Wilson Source Drops Bid Function
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators

variable {G : Gauge} {d : ℕ} {H : Hol G} {F : Frame G d} {m n : ℕ}

private def high (G : Gauge) (m j : ℕ) : Submodule ℂ (Pose G m) :=
    MvPolynomial.restrictSupport ℂ {u | j ≤ u.sum fun _ t => t}

private lemma high_iff (P : Pose G m) (j : ℕ) : P ∈ high G m j ↔ lows P j :=
  ⟨fun h _ hu => (MvPolynomial.mem_restrictSupport_iff ℂ).1 h hu,
    fun h => (MvPolynomial.mem_restrictSupport_iff ℂ).2 (fun _ h' => h _ h')⟩

variable (e : Fin m → Fin n) (r : Fin m → ℝ)

/-- Embed (possibly repeat) slots in a larger common list and multiply each by a sign factor. -/
def redirect : Pose G m →ₐ[ℂ] Pose G n := MvPolynomial.aeval fun i =>
    MvPolynomial.C (r i.1 : ℂ) * MvPolynomial.X (e i.1,i.2)

private lemma redirect_monomial (u : Fin m × G.ColorIndex →₀ ℕ) (c : ℂ) :
    MvPolynomial.IsWeightedHomogeneous (fun _ => (1:ℕ))
      (redirect e r (MvPolynomial.monomial u c)) (Finsupp.weight (fun _ => (1:ℕ)) u) := by
  let w : Fin n × G.ColorIndex → ℕ := fun _ => 1
  have hx (i : Fin m × G.ColorIndex) : MvPolynomial.IsWeightedHomogeneous w
      (redirect (G:=G) e r (MvPolynomial.X i)) 1 := by
    rw [redirect,MvPolynomial.aeval_X]
    exact (MvPolynomial.isWeightedHomogeneous_X ℂ w _).C_mul _
  simp only [MvPolynomial.monomial_eq,map_mul,redirect,MvPolynomial.aeval_C,
    MvPolynomial.algebraMap_eq]
  rw [Finsupp.weight_apply]; unfold Finsupp.prod Finsupp.sum
  apply MvPolynomial.IsWeightedHomogeneous.C_mul
  rw [map_prod]; simp_rw [map_pow]
  exact MvPolynomial.IsWeightedHomogeneous.prod _ _ _ fun i _ => (hx i).pow _

theorem redirect_lows (P : Pose G m) (j : ℕ) (h : lows P j) : lows (redirect e r P) j := by
  apply (high_iff _ _).mp
  rw [← P.support_sum_monomial_coeff,map_sum]
  apply Submodule.sum_mem
  intro u hu
  apply (high_iff _ _).mpr
  intro v hv
  have he := redirect_monomial e r u (MvPolynomial.coeff u P) (MvPolynomial.mem_support_iff.mp hv)
  have hz : v.sum (fun _ t => t) = u.sum fun _ t => t := by
    simpa [Finsupp.weight_apply,Finsupp.sum] using he
  rw [hz]; exact h u hu

private def lamp (x : GaugePanel G m) : Pose G m →ₐ[ℂ] ℂ :=
  MvPolynomial.aeval fun i => (x i.1 i.2 : ℂ)

theorem redirect_lumin (q : GaugePanel G n) (P : Pose G m) :
    lumin (redirect e r P) q = lumin P (fun i => r i • q (e i)) := by
  have he : (lamp q).comp (redirect e r) = lamp (fun i => r i • q (e i)) := by
    ext i
    simp [redirect,lamp]
  exact DFunLike.congr_fun he P

variable (B : Fin m → Slot) (P : F.Index → Pose G m)

private lemma assemble_high (h : Cumuli H d F B P) (i : F.Index) (s : Ortho) :
    assemble P (F.act s (Pi.single i 1)) ∈ high G m (F.grades i).2 := by
  rw [← F.coords_basis,F.act_coords]
  let x := tensor s (F.basis i)
  have hx : x ∈ Grade (F.grades i) := by
    have he := gradePart_mem (F.grades i) (tensor s (F.basis i))
    rw [gradePart_turn,gradePart_self (F.basis i) _ (F.pure i)] at he
    exact he
  change (∑ j,F.coords x j • P j) ∈ high G m _
  apply Submodule.sum_mem
  intro j _
  rcases eq_or_ne (F.grades i) (F.grades j) with hg|hg
  · rw [hg]; apply Submodule.smul_mem; exact (high_iff _ _).mpr (h.2.2.2.2 j)
  rw [F.power_coefficient j hg hx,zero_smul]
  exact Submodule.zero_mem _

theorem common_pose (h : Cumuli H d F B P) :
    ∃ (n : ℕ) (B' : Fin n → Slot) (Q : F.Coeff →ₗ[ℂ] Pose G n),
      (∀ c, averaged B P c = lumin (Q c) ∘ mapped B') ∧
      ∀ i : F.Index, lows (Q (Pi.single i 1)) (F.grades i).2 := by
  choose v r hr hv using fun (s : Signed) (i : Fin m) => slot_pull (G:=G) s (B i)
  let E := Fintype.equivFin (Signed × Fin m)
  let n := Fintype.card (Signed × Fin m)
  let B' (i : Fin n) := v (E.symm i).1 (E.symm i).2
  let D (s : Signed) : Pose G m →ₐ[ℂ] Pose G n := redirect (fun j => E (s,j)) (r s)
  let R (s : Signed) : F.Coeff →ₗ[ℂ] Pose G n :=
      D s |>.toLinearMap.comp ((assemble P).comp (F.act s.ortho⁻¹))
  refine ⟨n,B',share • ∑ s,R s, ?_, ?_⟩
  · intro c
    funext U
    have he (s : Signed) : term B P c s U = lamp (mapped B' U) (R s c) := by
      let q := assemble (F:=F) P (F.act s.ortho⁻¹ c)
      change lumin q (mapped B (pull s 0 U)) = lumin (redirect (fun j => E (s,j)) (r s) q) (mapped B' U)
      rw [redirect_lumin]
      apply congr_arg (lumin q); funext i; simp [mapped,hv,B']
    change averaged B P c U = lamp (mapped B' U) ((share • ∑ s,R s) c)
    simp only [averaged,Pi.smul_apply,Finset.sum_apply,LinearMap.smul_apply,
      LinearMap.sum_apply,map_smul,map_sum,he]
  intro i
  simp only [LinearMap.smul_apply,LinearMap.sum_apply]
  apply (high_iff _ _).mp
  apply Submodule.smul_mem; apply Submodule.sum_mem; intro s _
  change redirect (fun j => E (s,j)) (r s) (assemble P (F.act s.ortho⁻¹ (Pi.single i 1))) ∈ _
  exact (high_iff _ _).mpr (redirect_lows (fun j => E (s,j)) (r s) _ _ ((high_iff _ _).mp (assemble_high B P h i _)))
end YM.Work.G06
