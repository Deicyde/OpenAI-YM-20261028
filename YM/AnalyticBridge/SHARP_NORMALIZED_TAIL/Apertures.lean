import YM.AnalyticBridge.SHARP_NORMALIZED_TAIL.Accumulator
import YM.AnalyticBridge.SHARP_NORMALIZED_TAIL.Capacitor
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Chosen


/-!
# Post-L cap and projected covariances
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.Sharp.Aperture
open Filter Function Lattice RG Pressure Pressure.Stores Wilson Tree MeasureTheory Matrix
open YM.Push.SectorMeasure Next.SectorChange Next.SectorChange.Gaussian Next.SectorChange.Rows
open Schur LocalJet Wisps Tier Precision Capacitor
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius YM.Push.SectorMeasure

variable {I : Type} [Fintype I] [DecidableEq I]
  {c f : Side} {x W : ℝ} {S : StepData c f} {G : Gauge}

lemma billed {A C : Gaussian.Table I} {a b : ℝ} {p : I→Site c}
    (h : A.PosDef) (hr : Gapped A a) (hp : 0 < a) (hh : Pours (C-A⁻¹) p p 0 b) :
    Cap (a⁻¹+b) C := by
  intro v
  let x := A⁻¹ *ᵥ v
  have ht : A *ᵥ x = v := by
    unfold x; rw [mulVec_mulVec,A.mul_nonsing_inv (IsUnit.mk0 _ h.det_pos.ne'),one_mulVec]
  have hc := hr x; rw [ht,sumSq_dot,dotProduct_comm x v] at hc
  have hg := sumSq_nn (v-a • x)
  rw [sumSq_dot] at hg
  simp only [dotProduct_sub,sub_dotProduct,smul_dotProduct,dotProduct_smul,smul_eq_mul] at hg
  rw [dotProduct_comm x v] at hg
  have hu : v ⬝ᵥ x ≤ a⁻¹*(v ⬝ᵥ v) := by
    rw [mul_comm a⁻¹, ← div_eq_mul_inv, le_div_iff₀ hp]; nlinarith only [hg,mul_le_mul_of_nonneg_left hc hp.le]
  have hm := (le_abs_self _).trans (estimate hh v v)
  rw [sumSq_dot, sub_mulVec,dotProduct_sub] at hm
  change _ - v ⬝ᵥ x ≤ _ at hm
  linarith only [hu,hm]

/-- The Gaussian actually bought in Handoff. One cap at all keys, all
placements with correct flags. No estimating eigenvalues of a covariance
by bounding its trace with a volume bill. -/
lemma open_price (P : Teller G) (Q : Patch) (hQ : Q.Branches P.bind G) :
    ∃ K : ℝ, 0<K ∧ ∀ᶠ x : ℝ in atTop, ∀ {c f : Side} (S : StepData c f) (T : Tube G S),
      S.patch=Q → 100*(1+radiusB x) ≤ c.val → P.Funds S T → ∀ (A : Stores S) (F : Forest S.ratio) (k:S.Choices)
      (V : Config G c), A.flags=RG.flags (temp x) V →
      (fog A F T x V k).PosDef ∧ Cap K (fog A F T x V k) := by
  obtain ⟨v,K,r,b,E,hv,hK,hr,hb,hE,h⟩ := opaqueCost G Q P hQ
  refine ⟨r⁻¹+E,by positivity,?_⟩
  filter_upwards [h] with x hx
  intro c f S T hs hh hT A F k V hV
  obtain ⟨-,hG,hQ,hP,hC⟩ := hx S T hs hh hT A F k V hV
  refine ⟨hC,billed hQ hG hr (hP.weaker le_rfl ?_)⟩
  apply mul_le_of_le_one_right hE.le
  apply Real.exp_le_one_iff.mpr; exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb.le) (Nat.cast_nonneg _)

-- if using fog. halo suffices even on wrap. No claim here that
-- card and component applicability have been established.
lemma insulated {X Y : Support c} {F : Forest S.ratio} {r : Ribbon F X} {s : Ribbon F Y}
    {A : Stores S} (hx : Disjoint X Y) (hq : r.Placed x A) (hp : s.Placed x A)
    (T : Tube G S) (V : Config G c) (k : S.Choices)
    (h : ∀ i ∈ r.breeze, halo (radiusB x/20) {S.ratio.parent i.val.1} ⊆ X) :
    ∀ i j, fog A F T x V k (Ribbon.lighten hq i) (Ribbon.lighten hp j)=0 := by
  intro i j; apply fog_zero; intro he
  let a := S.ratio.parent i.1.val.val.1; let b := S.ratio.parent j.1.val.val.1
  have hz : separation a b ≤ radiusB x/20 := he a (Set.mem_insert ..) b (Set.mem_insert ..)
  exact Finset.disjoint_left.mp hx (h _ i.1.property (halo_spec.mpr ⟨a,Finset.mem_singleton_self _,hz⟩))
    (s.wind j.1.val j.1.property).1
end YM.AnalyticBridge.Sharp.Aperture
