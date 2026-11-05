import YM.Extra.WEAK_SCALING_ACTLAW.Line
import YM.Extra.WEAK_SCALING_ACTLAW.Producer
import YM.Work.A05

/-!
# Orientation criterion and stress-side applications of the producer

A route given only Pre cannot just start with an arbitrary supplied Pre,
forget nontriviality and claim weak on those same components: there is a
concrete obstruction. Likewise the sign matters. For normalized translation
flux and fixed positive kappa on the Lighthouse one can keep the positive
orientation, by comparing FOUR-degree tests from both flux and derivative
at the common weak scale (answers A04,A05 with demands). Also offer an
adapter creating a centered J *before* using it in both Pre and ActLaw if
starting with uncentered data on the very same table.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.WeakScaling
open Filter Function Set Table Org Bid Climb Extraction Spec
open scoped Topology ContDiff
variable {G : Gauge} {L : Register G} {S : Table L} {V : DiffPlan S}





private lemma scale_limit {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    {X : ℕ → Z} {x : Z} (hx : Tendsto X atTop (𝓝 x)) {f : ℕ → ℝ} {c : ℝ}
    (ht : Tendsto (fun i => f i • X i) atTop (𝓝 (c • x))) (h : x≠0) : Tendsto f atTop (𝓝 c) := by
  obtain ⟨Y,hY⟩ := Module.Projective.exists_dual_ne_zero ℝ h
  have hc := Y.continuous_of_finiteDimensional
  have hz := hc.continuousAt.tendsto.comp hx
  have hp := (hc.continuousAt.tendsto.comp ht).div hz hY
  rw [map_smul,smul_eq_mul, mul_div_cancel_right₀ _ hY] at hp
  apply hp.congr'
  filter_upwards [hz.eventually (isOpen_compl_singleton.mem_nhds hY)] with i hi
  change Y (f i • X i)/Y (X i)= _
  rw [map_smul, smul_eq_mul,mul_div_cancel_right₀ _ (show Y (X i) ≠ 0 from hi)]

variable {C : Family G} {S : Table C.book} {f : Order} {V : DiffPlan S} (W : MaxwellData C) {I : IR (C:=C) S}

theorem tracks_ratio (H : S.Hierarchy) (hv : V.Inclusions S) (ht : V.Derivatives S) (hp : Pre H V I.J I.p I.Y)
    {c : ℝ} (hc : leaves I.p 4 = c • leaves V.deriv 4) :
    Watches I.J W.T H.spin W.hT.spin V (fun X => Tendsto (fun i => c / X.xi i) atTop (𝓝 W.T.κ)) := by
  obtain ⟨D,N,m,R,hR,h₁⟩ := (Work.A04.answer H V hv ht W I.J 4).ask
  obtain ⟨d,n,j,r,hr,h₂⟩ := (Work.A05.answer H V hv ht W I.J 4 I.p I.Y hp).ask
  refine ⟨max D d,max N n,max m j,max R r,hR.trans (le_max_left ..),fun X d' n' m' R' hd hn hm hr' hX => ?_⟩
  have he := h₁ X _ _ _ _ (by omega) (by omega) (by omega) ((le_max_left ..).trans hr') hX
  have h := (h₂ X _ _ _ _ (by omega) (by omega) (by omega) ((le_max_right ..).trans hr') hX).1
  have hh : leaves (W.T.κ • W.T.W.deriv) 4 = W.T.κ • leaves W.T.W.deriv 4 := by ext1 i; ext1 v; rfl
  unfold ConLap at he h; rw [hc, hh] at h
  refine scale_limit (X:=fun i => X.r i • X.aisle i 4 (leaves V.deriv 4)) he (h.congr ?_) W.lit.born
  intro i; rw [map_smul, smul_smul, smul_smul]; congr 1; ring

lemma kappa_sign (H : S.Hierarchy) (hv : V.Inclusions S) (ht : V.Derivatives S) (hp : Pre H V I.J I.p I.Y)
    {c : ℝ} (hc : leaves I.p 4 = c • leaves V.deriv 4) (hw : ActLaw V W.T I.J H.spin W.hT.spin) : 0 < c*W.T.κ := by
  obtain ⟨D,N,m,R,hR,hy⟩ := (tracks_ratio W H hv ht hp hc).ask
  obtain ⟨X,hX⟩ := hw.connects N D m R hR
  have he := hy X D N m R le_rfl le_rfl le_rfl le_rfl hX
  have h0 := W.T.hκ
  have h : c ≠ 0 := by
    rintro rfl
    simp only [zero_div] at he
    exact h0 (tendsto_nhds_unique he tendsto_const_nhds)
  rcases h.lt_or_gt with h|h
  · have hh := le_of_tendsto he (Eventually.of_forall (fun k => div_nonpos_of_nonpos_of_nonneg h.le (X.sign k).le))
    exact mul_pos_of_neg_of_neg h (lt_of_le_of_ne hh h0)
  have hh := ge_of_tendsto he (Eventually.of_forall (fun k => (div_pos h (X.sign k)).le))
  exact mul_pos h (lt_of_le_of_ne hh h0.symm)







/-- Use before RPrep, obtaining actual stress candidates on the one table
when the two indicated free type estimates are in hand. Doesn't provide flux
representations. Converse uniqueness clause is useful even if a different
centered physical stress has been provided from a concrete Wilson derivation
at these same S,V.
-/
theorem before_flux (s : Seed C f S) (he : Supply C f W.hT.spin) (hV : V.Inclusions S) (hV' : V.Derivatives S)
    (ht : Line W.T W.hT.spin) (hs : Module.finrank ℝ (polar W.hT.spin) < Module.finrank ℝ (meanFree W.hT.spin)) :
    ∃ J : S.Stress, J ≠ 0 ∧ Centered J ∧ Conserved V s.kernel.spin J ∧ RawTensor s.kernel.spin J ∧
      ∀ P : S.Stress, Centered P → Conserved V s.kernel.spin P → RawTensor s.kernel.spin P → ∃ c : ℝ, P=c • J := by
  obtain ⟨Q,hQ,⟨X⟩⟩ := weak_curve s W he 1 5 1 le_rfl hV hV'
  have ho := Work.D06.answer s.cutoff s.kernel.smooth s.kernel.laws.toSymmetric s.generic V hV' hV s.kernel.spin
  obtain ⟨J,hJ,h₁,h₂,h₃⟩ := stress_birth s.kernel W.hT X (by omega) ho hs
  exact ⟨J,hJ,h₁,h₂,h₃, fun P h₄ h₅ h₆ => X.only_line (by linarith) (by omega) le_rfl s.kernel hV' ht h₂ h₃ h₁ h₅ h₆ h₄ hJ⟩
end YM.Extra.WeakScaling
