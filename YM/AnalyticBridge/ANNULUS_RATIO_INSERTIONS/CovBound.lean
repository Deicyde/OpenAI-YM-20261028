import YM.Next.FREE_KERNELS.Signal
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Chosen
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Delay

/-!
# Both sides of the same-law fog covariance bound
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.AnalyticBridge.AnnulusRatioInsertions.Prism
open Function Filter Lattice Wilson RG RG.Patch Precision Exterior Tree MeasureTheory Metric Matrix
open Next.SectorChange Next.SectorChange.Motion Next.SectorChange.Rows Next.SectorChange.Gaussian
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure Push.SectorMeasure.Oriented 
open Tier Wisps Schur LocalJet 

open scoped Topology InnerProductSpace BigOperators Classical ContDiff Matrix.Norms.Frobenius Push.SectorMeasure

section form
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] {A : Gaussian.Table V} {η L : ℝ}

/-- Real counting convention. -/
lemma dot_nonneg (v : Vec V) : 0 ≤ v ⬝ᵥ v := sumSq_dot v ▸ sumSq_nn v

lemma dot_diff (z x : Vec V) (k : ℝ) : 2*k*(z ⬝ᵥ x) ≤ z ⬝ᵥ z + k^2*(x ⬝ᵥ x) := by
  have h := dot_nonneg (z - k • x)
  rw [sub_dotProduct,dotProduct_sub,dotProduct_sub,dotProduct_smul,smul_dotProduct,
    dotProduct_smul,smul_dotProduct,smul_eq_mul,smul_eq_mul,smul_eq_mul,dotProduct_comm x z] at h
  simp only [smul_eq_mul] at h
  nlinarith only [h]

/-- Sharp two-sided bound for the inverse in the genuine form norm.
Derive via variational inequality rather than inserting a mesh eigenbasis. -/
lemma reciprocal (hA : A.IsSymm) (hη : 0<η) (hL : 0<L) (h : Numeric A η L) : Numeric A⁻¹ L⁻¹ η⁻¹ := by
  have hu : A.PosDef := dissolves (fun i=>sumSq_dot i |>.symm ▸ (h i).1) hA hη
  intro z
  let v := A⁻¹ *ᵥ z
  have hv : A *ᵥ v = z := by unfold v; rw [mulVec_mulVec,A.mul_nonsing_inv ((A.isUnit_iff_isUnit_det).mp hu.isUnit),one_mulVec]
  change L⁻¹*(z ⬝ᵥ z) ≤ z ⬝ᵥ v ∧ z ⬝ᵥ v ≤ η⁻¹*(z ⬝ᵥ z)
  constructor
  · let t := L • v - z
    have h0 : 0 ≤ t ⬝ᵥ (A *ᵥ t) := le_trans (mul_nonneg hη.le (dot_nonneg t)) (h t).1
    have he : v ⬝ᵥ (A *ᵥ z) = z ⬝ᵥ z := by
      nth_rw 1 [← hA.eq]
      rw [Matrix.dotProduct_transpose_mulVec,hv]
    unfold t at h0; rw [mulVec_sub,mulVec_smul,hv,sub_dotProduct,
      dotProduct_sub,dotProduct_sub,smul_dotProduct,smul_dotProduct,dotProduct_smul,dotProduct_smul,
      he,smul_eq_mul,smul_eq_mul,smul_eq_mul,dotProduct_comm v z] at h0
    rw [inv_mul_eq_div, div_le_iff₀ hL]
    have hx := (h z).2
    exact le_of_sub_nonneg (by nlinarith)
  have hh := (h v).1
  rw [hv,dotProduct_comm v z] at hh
  have hr := dot_diff z v η
  rw [inv_mul_eq_div,le_div_iff₀ hη]
  nlinarith [mul_le_mul_of_nonneg_left hh hη.le]

/-- Embeddings (including arbitrary groupings / relabelings of a
position's color fiber) at counting price. -/
def scout (e : I → V) (x : Vec I) (j : V) := ∑ i, (Pi.single (e i) (x i) : Vec V) j

lemma scouting (e : I → V) (h : Function.Injective e) (x : Vec I) (u : Vec V) :
    scout e x ⬝ᵥ u = x ⬝ᵥ fun i=>u (e i) := by
  classical
  unfold dotProduct scout
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=>?_
  simp [Pi.single_apply,ite_mul]

lemma scouted (e : I → V) (h : Function.Injective e) (x : Vec I) (i : I) : scout e x (e i)=x i := by
  classical
  unfold scout
  simp [Pi.single_apply,h.eq_iff]

lemma nominated (e : I → V) (he : Injective e) (hA : Numeric A η L) : Numeric (A.submatrix e e) η L := by
  intro v
  have hs : (scout e v) ⬝ᵥ scout e v = v ⬝ᵥ v := by rw [scouting e he]; simp_rw [scouted e he]
  have hx : (scout e v) ⬝ᵥ (A *ᵥ scout e v) = v ⬝ᵥ (A.submatrix e e *ᵥ v) := by
    rw [scouting _ he]
    congr; funext i
    change A (e i) ⬝ᵥ scout e v = (fun j:I=> A (e i) (e j)) ⬝ᵥ v
    rw [dotProduct_comm,scouting _ he,dotProduct_comm]
  have hg := hA (scout e v)
  rw [hs,hx] at hg; exact hg



/-- Can buy *both* sides on a matrix that is only known close to A⁻¹,
with Pours cost. In applications F is the actual fog, not a mesh
prescription. Use L or η broadened further if desired. -/
theorem spells {c : Side} (p : V → Site c) (hA : A.PosDef) {F : Gaussian.Table V}
    {δ σ : ℝ} (hη : 0<η) (hL : 0<L) (hσ : 0<σ)
    (hp : Pours A p p σ L) (hG : Gapped A η)
    (h : Pours (F-A⁻¹) p p 0 δ)
    (hδ : δ ≤ L⁻¹/2) (hv : δ ≤ η⁻¹) : Numeric F (L⁻¹/2) (2*η⁻¹) := by
  have ht : Numeric A η L := by
    intro v
    have hx := (abs_le.mp (estimate (hp.weaker hσ.le le_rfl) v v)).2
    simp_rw [sumSq_dot] at hx
    exact ⟨sumSq_dot v ▸ hG v,by linarith⟩
  have hk := reciprocal (Matrix.isHermitian_iff_isSymm.mp hA.isHermitian) hη hL ht
  intro a
  have he := estimate h a a
  rw [sub_mulVec,dotProduct_sub,sumSq_dot,show δ * (a ⬝ᵥ a + a ⬝ᵥ a) / 2 = δ*(a ⬝ᵥ a) by ring] at he
  obtain ⟨hh,hb⟩:= abs_le.mp he
  obtain ⟨hl,hn⟩ := hk a
  have hu := mul_le_mul_of_nonneg_right hδ (dot_nonneg a)
  have hx := mul_le_mul_of_nonneg_right hv (dot_nonneg a)
  constructor <;> linarith
end form

section real
/-- Fixed-L uniform covariance prescription *also* uniform in the
flag list, the positions selected as arguments (can take ALL Z keys),
Forest and placement. Late x threshold independently fixed across periods.
-/
lemma visions (G : Gauge) (Q : Patch) (P : Teller G) (h : Q.Branches P.bind G) :
    ∃ η L : ℝ, 0<η ∧ η≤L ∧ ∀ᶠ x : ℝ in atTop, ∀ {c f : Side} (S : StepData c f) (T : Tube G S),
      S.patch=Q → 100*(1+radiusB x) ≤ c.val → P.Funds S T →
        ∀ (A : Stores S) (F : Forest S.ratio) (V : Config G c) (k : S.Choices), A.flags=RG.flags (temp x) V →
          let C := fog A F T x V k
          C.PosDef ∧ Numeric C η L ∧ Numeric C⁻¹ L⁻¹ η⁻¹ := by
  obtain ⟨v,K,e,b,M,hv,hK,he,hb,hM,H⟩ := opaqueCost G Q P h
  let L0 := max K 1
  have hL : 0<L0 := lt_of_lt_of_le zero_lt_one (le_max_right ..)
  let L := 2*e⁻¹; let g := L0⁻¹/2; let η := min g L
  have hu : 0<L := mul_pos (by norm_num) (inv_pos.mpr he)
  have hg : 0<g := half_pos (inv_pos.mpr hL)
  have hη : 0<η := lt_min hg hu
  refine ⟨η,L,hη,min_le_right ..,?_⟩
  have ht : Tendsto (fun x : ℝ => M*rate (-b) (radiusB x/60)) atTop (𝓝 0) := by
    have hB : Tendsto (fun x : ℝ => radiusB x/60) atTop atTop := Filter.tendsto_atTop.mpr (fun i => by
      filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop (60*i)] with x hx
      omega)
    have hi := tendsto_natCast_atTop_atTop (R:=ℝ)|>.comp hB
    have hz := Real.tendsto_exp_atBot.comp (hi.const_mul_atTop_of_neg (neg_lt_zero.mpr hb))
    simpa [rate,Function.comp_def] using hz.const_mul M
  filter_upwards [H,ht.eventually (ge_mem_nhds (lt_min hg (inv_pos.mpr he)))] with x hx h0
  intro c f S T hQ hs hP A F V k hV C
  obtain ⟨h1,h2,h3,h4,h5⟩ := hx S T hQ hs hP A F k V hV
  have hr := spells (front A F (G:=G)) h3 he hL hv (h1.weaker le_rfl (le_max_left K 1)) h2 h4 (le_trans h0 (min_le_left ..)) (le_trans h0 (min_le_right ..))
  have hk : Numeric C η L := by
    intro i
    exact ⟨le_trans (mul_le_mul_of_nonneg_right (min_le_left ..) (dot_nonneg _)) (hr i).1,(hr i).2⟩
  exact ⟨h5,hk,reciprocal (Matrix.isHermitian_iff_isSymm.mp h5.isHermitian) hη hu hk⟩
end real
end YM.AnalyticBridge.AnnulusRatioInsertions.Prism
