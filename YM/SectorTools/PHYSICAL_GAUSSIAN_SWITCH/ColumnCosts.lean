import YM.SectorTools.PHYSICAL_GAUSSIAN_SWITCH.TableCosts
import YM.SectorTools.PHYSICAL_GAUSSIAN_SWITCH.Weighted

/-!
# Switching finitely many columns of a window law

Prices both the ordered mean shift and symmetric cloud. The assumption
on U,V's discrepancy is a small Schur price as bought after delay.
Can spend two ways: exact RN *moment* cost on a halo of X in the
geometry of the window (see LocalLpWindows), or a trace-weighted
price via absolute table masses. The latter depends just on card X (not
even on card of the halo, and retains small δ), allowing ν component
columns for ν marks with a sub-Gaussian source cost. Neither gives the
means small in g-rescaled coordinates for free. -/
set_option autoImplicit false
noncomputable section
namespace YM.SectorTools.PhysicalGaussianSwitch.ColumnCosts
open Function Filter Matrix Lattice MeasureTheory
open Next.SectorChange Next.SectorChange.Gaussian Next.SectorChange.Wisps Next.SectorChange.Schur
open AnalyticBridge.GaussianFieldAlignment.Relative (symPart sym_of_sub sym_pours trade source)
open TableCosts
open scoped Topology BigOperators ENNReal
local notation "Covar" => Next.SectorChange.Gaussian.Table

variable {I : Type} [Fintype I] [DecidableEq I] {U V : Covar I} {X H : Finset I}
variable {c : Side} {o : I → Site c} {s K δ p : ℝ}

/-- U is the starting ORDERED window table (symmetrize later). Use columns
of V instead at X. Rank/trace costs below don't require these columns even
to have a halo. -/
def hybrid (U V : Covar I) (X : Finset I) := U+columns X (V-U)
omit [Fintype I] in
lemma column_cov (U V : Covar I) (X : Finset I) : symPart (hybrid U V X)-symPart U = symPart (columns X (V-U)) := by
  rw [← sym_of_sub,hybrid,add_sub_cancel_left]

/-- Earlier data only. No quantity costing the new law or new dimensional
space assumed given. -/
structure License (U V : Covar I) (o : I → Site c) (s K δ : ℝ) : Prop where
  coef : Pours (V-U) o o s δ
  pos : (symPart U).PosDef
  hi : Pours (symPart U) o o s K
  lo : Pours ((symPart U)⁻¹) o o s K
  large : 1 ≤ K
  rate_pos : 0 ≤ s
  afford : K*δ ≤ 1/2

namespace License
variable (h : License U V o s K δ)
include h
lemma pure : Elliptic K (symPart U) := from_pours h.pos h.hi h.lo h.rate_pos h.large
lemma change_cost (X : Finset I) : let x:=symPart (hybrid U V X)-symPart U
    Pours x o o s δ ∧ mass x ≤ X.card*δ := by
  simp_rw [column_cov]
  exact ⟨sym_pours (columns_pour _ h.coef), (mass_sym _).trans (mass_columns _ h.coef h.rate_pos)⟩

lemma positive (X : Finset I) : Elliptic (2*K) (symPart (hybrid U V X)) := by
  have he (x : Vec I) := abs_le.mp (quad_schur (h.change_cost X).1 h.rate_pos x)
  have hk := h.pure.positive; have ht := h.large
  have hd : δ ≤ (2*K)⁻¹ := by
    have hx := h.afford
    field_simp
    linarith
  have hz : δ ≤ K := by nlinarith only [ht,h.coef.pos,h.afford]
  have hp : K⁻¹=2*(2*K)⁻¹ := by field_simp
  let A:=symPart U; let M:=symPart (hybrid U V X)
  refine ⟨by linarith,symm_sym _,fun x => ?_⟩
  obtain ⟨h1,h2⟩ := he x
  let q:=x ⬝ᵥ x; have hq:0≤q:=sumsq_nonneg _
  obtain ⟨ha,hb⟩ := h.pure.numeric x
  change (2*K)⁻¹*q ≤ quad M _ ∧ quad M _ ≤ (2*K)*q
  rw [quad_diff] at h1 h2
  change -(δ*q) ≤ quad M x-quad A x at h1; change quad M x-quad A x ≤ δ*q at h2
  change K⁻¹*q ≤ quad A x at ha; change quad A x ≤ K*q at hb; rw [hp] at ha
  constructor <;> linarith only [h1,h2,ha,hb,mul_le_mul_of_nonneg_right hd hq,mul_le_mul_of_nonneg_right hz hq]
end License

def mean (U : Covar I) (b : Vec I) := -U.transpose *ᵥ b
lemma mean_diff (U V : Covar I) (X : Finset I) (b : Vec I) :
    mean (hybrid U V X) b - mean U b = -(columns X (V-U)).transpose *ᵥ b := by
  unfold mean hybrid; rw [Matrix.transpose_add,neg_add,add_mulVec,add_sub_cancel_left]

lemma mean_bound (hc : License U V o s K δ) (X : Finset I) (b : Vec I) :
    ‖mean (hybrid U V X) b - mean U b‖ ≤ δ*‖b‖ := by
  rw [mean_diff]; exact source hc.rate_pos (columns_pour X hc.coef) b
lemma mean_support {i : I} (hi : i ∉ X) (b : Vec I) :
    (mean (hybrid U V X) b - mean U b) i=0 := by
  rw [mean_diff]; simp [mulVec,dotProduct,columns,hi]

/-- Reference law is the fresh hybrid, so this is the displacement
in Relative's coordinates. -/
def delta (U V : Covar I) (X : Finset I) (g : ℝ) (b : Vec I) := g⁻¹ • (mean (hybrid U V X) b - mean U b)
lemma delta_cost (hc : License U V o s K δ) (X : Finset I) {g y : ℝ} (hg : 0<g) (b : Vec I) (hb : ‖b‖ ≤ y) :
    let h:=delta U V X g b
    (∀ i∉X,h i=0) ∧ ‖h‖ ≤ δ*y/g ∧ h ⬝ᵥ h ≤ X.card*(δ*y/g)^2 := by
  intro h; have hd := hc.coef.pos; have hy := (norm_nonneg b).trans hb
  have hi i (he : i ∉ X) : h i=0 := by unfold h delta; simp only [Pi.smul_apply,mean_support he,smul_zero]
  have ht : ‖h‖ ≤ δ*y/g := by
    unfold h delta; rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr hg).le,div_eq_mul_inv,mul_comm (δ*y)]
    exact mul_le_mul_of_nonneg_left ((mean_bound hc X _).trans (mul_le_mul_of_nonneg_left hb hd)) (inv_pos.mpr hg).le
  refine ⟨hi,ht,?_⟩
  calc
    _ = ∑ i∈X,(h i)^2 := by
      unfold dotProduct; simp_rw [sq]; exact (Finset.sum_subset (Finset.subset_univ X) fun i _ hx => by rw [hi i hx]; ring).symm
    _ ≤ ∑ _i∈X,(δ*y/g)^2 := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) ((norm_le_pi_norm h i).trans ht) _
    _ = _ := by simp

/-- Lp cost with NO halo factor via trace. Costs in addition a ratio of
coupling/shift retained. The `Mp.PosDef` conclusion (needed even if
wishing to use just relative comparison tools) is paid too. -/
def sumPrice (p K δ g y : ℝ) (n : ℕ) := Real.exp ((p+1)*Weighted.spend p (2*K) (2*K^2*(n*δ)) (K^2 * (n * (δ*y/g)^2)))

theorem paid (hc : License U V o s K δ) (hp : 1 ≤ p) (hδ : (2*K)*(2*p*(2*K^2*δ)) ≤ 1/4) (X : Finset I)
    {g y : ℝ} (hg : 0<g) (b : Vec I) (hb : ‖b‖ ≤ y) :
    let h:=delta U V X g b; let A:=symPart U; let D:=symPart (hybrid U V X)
    (mixed A D p).PosDef ∧ price A D p h ≤ sumPrice p K δ g y X.card := by
  intro h A D
  have he := hc.change_cost X; have ha := hc.pure
  have hd := hc.positive X; have hk := ha.positive
  obtain ⟨h1,h2⟩ := precision_costs hd.posDef ha.posDef hc.lo he.1 hc.rate_pos hc.afford he.2
  let B := A⁻¹-D⁻¹
  have hw : Pours B o o s (2*K^2*δ) := by dsimp only [B]; rw [← neg_sub]; exact pour_neg h1
  let w:=load B
  have hv := load_nonneg B; have hr : ∀ i, w i ≤ 2*K^2*δ := row_budget hw hc.rate_pos
  have hy : Weighted.Trace B w := Weighted.by_rows (by unfold B Matrix.IsSymm; rw [transpose_sub,(symm_pos ha.posDef.inv).eq,(symm_pos hd.posDef.inv).eq]) hv (fun i => by change w i ≤ 2*w i; have := hv i; unfold w; linarith)
  have hW : ∑ i, w i ≤ 2*K^2*(X.card*δ) := by
    change mass B ≤ _; dsimp only [B]; rw [← neg_sub,mass_neg]; exact h2
  have h3' := Weighted.weighted ha.posDef hd.posDef (show Weighted.Upper (2*K) D from hd.upper) (by positivity) hy hW hp
    (fun i => le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hr i) (by linarith)) (by positivity)) hδ) h
  have hl := (delta_cost hc X hg b hb).2.2
  have hh : (-(A⁻¹ *ᵥ h)) ⬝ᵥ (-(A⁻¹ *ᵥ h)) ≤ K^2*(X.card*(δ*y/g)^2) := by
    rw [neg_dotProduct,dotProduct_neg,neg_neg]; exact (ha.op h).trans (mul_le_mul_of_nonneg_left hl (sq_nonneg _))
  refine ⟨h3'.2.1,h3'.2.2.trans (Real.exp_monotone ?_)⟩
  unfold Weighted.spend; gcongr

/-- Now if the changed columns were also actually supported on H,
including their centers, can integrate just on that supported space
(Schur residual). -/
def confined (U V : Covar I) (X H : Finset I) := X ⊆ H ∧ ∀ i∈X, ∀ j∉H, V j i=0 ∧ U j i=0

lemma on_halo (h : confined U V X H) (g : ℝ) (b : Vec I) :
    ConfinedCovariance (Function.Embedding.subtype (· ∈ H)) (symPart U) (symPart (hybrid U V X)) (delta U V X g b) := by
  let e:=Function.Embedding.subtype (· ∈ H)
  have he {i} (hi : i∉ Set.range e) : i ∉ H := fun hh => hi ⟨⟨i,hh⟩,rfl⟩
  have ht (i j : I) (hm : i∉H ∨ j∉H) : columns X (V-U) i j=0 := by
    unfold columns; rw [Matrix.of_apply]; split
    next hp => obtain ⟨h1,h2⟩ := h.2 _ hp _ (hm.resolve_right (not_not.mpr (h.1 hp))); rw [Matrix.sub_apply,h1,h2]; ring
    rfl
  refine ⟨fun i j hq => ?_,fun i hi => ?_⟩
  · have hm := hq.imp he he
    rw [← neg_sub,column_cov]; change -((1/2:ℝ)*(columns X _ i j+columns X _ j i)) = _
    rw [ht i j hm,ht j i hm.symm]; ring
  have hm : i∉X:=fun h1=>he hi (h.1 h1); unfold delta
  rw [Pi.smul_apply,mean_support hm,smul_zero]



section use
-- normalize expectation after changing law (none of the multiplier
-- factors external to the normalized Gaussian are asserted to stay fixed).
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def shifted (b : Vec I) (g : ℝ) (f : Vec I → E) (U : Covar I) (z : Vec I) := f (mean U b + g • z)

theorem normalized (hc : License U V o s K δ) (hp : 1<p) (hδ : (2*K)*(2*p*(2*K^2*δ)) ≤ 1/4)
    (X : Finset I) {g y : ℝ} (hg : 0<g) (b : Vec I) (hb : ‖b‖ ≤ y) (f : Vec I → E) :
    let T := hybrid U V X; let q := Real.conjExponent p
    MemLp (shifted b g f T) (ENNReal.ofReal q) (cloud (symPart T)) →
    Integrable (shifted b g f U) (cloud (symPart U)) ∧
      ‖∫ z, shifted b g f U z ∂cloud (symPart U)‖ ≤ sumPrice p K δ g y X.card ^ (1/p) * (∫ z, ‖shifted b g f T z‖ ^ q ∂cloud (symPart T))^(1/q) := by
  intro T q hf; let d:=delta U V X g b
  have he z : shifted b g f U (d+z)= shifted b g f T z := by
    unfold shifted d delta; rw [smul_add,smul_smul,mul_inv_cancel₀ hg.ne', one_smul]; congr 1; unfold T; abel
  obtain ⟨ha,ht⟩ := paid hc hp.le hδ X hg b hb
  obtain ⟨hi,hu⟩ := trade_comparison hc.pos (hc.positive X).posDef hp ha (show MemLp (fun z => shifted b g f U (d+z)) _ _ by simp_rw [he]; exact hf)
  simp_rw [he] at hu
  have hy : 0 < p := zero_lt_one.trans hp
  refine ⟨hi,hu.trans (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ?_ ht (by positivity))
    (Real.rpow_nonneg (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _) _))⟩
  unfold price; positivity
end use
end YM.SectorTools.PhysicalGaussianSwitch.ColumnCosts
