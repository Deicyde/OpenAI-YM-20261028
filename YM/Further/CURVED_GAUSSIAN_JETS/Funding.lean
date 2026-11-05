import YM.Further.CURVED_GAUSSIAN_JETS.Cards
import YM.Further.CURVED_GAUSSIAN_JETS.HoleGap


/-!
# From compulsory rows and output-field flags to a uniform ledger budget

`Covers` retains the *physical tangent values* on the actual step, using
canonical direct/noise orientation and zero insertion on each inactive
a. Valid e.g. with omitted rows EXACTLY when they contribute nothing
to that test (true when the potential-a-stencil misses the regular
coordinates). Other rows need exponential bills. Need check both of
these input hypotheses when using the resulting scalar consumers!!
This doesn't supply a selected affine mapping or local species.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 1024
noncomputable section
namespace YM.Further.CurvedGaussianJets.Pockets
open Function Filter Set Metric Gauge Lattice Wilson Tree RG Precision Work Exterior Pressure Bid SectorNext.Vacuum Progress.StationaryScenes Matrix
open Rows (Bill)
open scoped Matrix.Norms.Frobenius Topology BigOperators ContDiff Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f}
variable {F : Forest S.ratio} (H : Finset F.Free)

def use (x : Vec (Bits H G)) (i : F.Free) := if h : i∈H then (0:G.Color) else linkBits H x ⟨i,h⟩
def test (x : Vec (Bits H G)) : Dir G f := FlatTree.blank F (use H x) ∘ (FlatTree.wheel f).symm
lemma test_eq (x : Vec (Bits H G)) (e : Bond f) : collect G (test (S:=S) H x) e = FlatTree.blank F (use H x) e := (congr_arg (FlatTree.blank F (use H x)) ((FlatTree.wheel f).symm_apply_apply e))
lemma test_norm (x : Vec (Bits H G)) : (∑ i, ‖test (S:=S) H x i‖^2) = dotProduct x x := by
  unfold dotProduct; conv_rhs => rw [Fintype.sum_prod_type];
  symm
  let e := fun i : Soft H=> FlatTree.wheel f i.val.val
  have he : Injective e := ((FlatTree.wheel f).injective.comp Subtype.val_injective).comp Subtype.val_injective
  apply Fintype.sum_of_injective e he
  · intro i hi; obtain ⟨p,rfl⟩ := (FlatTree.wheel f).surjective i
    suffices collect G (test (S:=S) H x) p=0 by
      change ‖collect G (test H x) p‖^2=0; simp [this]
    rw [test_eq,FlatTree.blank]; split; rfl
    rw [use,dif_pos]; by_contra h; exact hi ⟨⟨⟨_,‹_›⟩,h⟩,rfl⟩
  intro i
  have hh : use H x i.val = linkBits H x i := dif_neg i.property
  change _ = ‖collect G (test H x) (i.val.val)‖^2
  rw [test_eq,FlatTree.blank,dif_neg i.val.property,hh, EuclideanSpace.real_norm_sq_eq]; simp [linkBits,pow_two]

def Clean (V : Config G c) (t : ℝ) : Prop := ∀ i : Soft H, ∀ y ∈ RG.flags t V, extent S.patch < separation (S.ratio.parent i.val.val.1) y
lemma clean_core (V : Config G c) (x : Vec (Bits H G)) {t : ℝ} (h : Clean H V t) : Core (S:=S) V (test H x) t := by
  intro e he b hb
  rw [test_eq,FlatTree.blank] at he; split at he; contradiction
  rename_i he'
  let i : F.Free := ⟨e,he'⟩
  unfold use at he; split at he; contradiction
  rename_i hi
  let j : Soft H := ⟨i,hi⟩
  by_contra! hx
  have hf := (RG.flags_spec t V b.1).mpr ⟨b,(by simp [RG.touched,Lattice.visits,square]),hx⟩
  exact (h j b.1 hf).not_ge hb

variable {X : Type*} [Fintype X]
def Covers (V : Config G c) (k : S.Choices) (D : Matrix X (Bits H G) ℝ) (L : ℝ) := ∀ x : Vec (Bits H G),
    let U := replica S.ratio V; let v := test H x
    (∑ p, (curlPrice U v p)^2) + ∑ p, (noisePrice U v k p)^2 ≤ L*dotProduct (D *ᵥ x) (D*ᵥx)


private lemma injection {I : Type*} [Fintype I] {D : Matrix X I ℝ} (x : Vec I) {Y : Type*} [Fintype Y] (e : Y ↪ X) :
    ∑ i, ((D*ᵥx) (e i))^2 ≤ dotProduct (D*ᵥx) (D*ᵥx) := calc
  _ = ∑ i∈Finset.univ.map e, ((D*ᵥx) i)^2 := Eq.symm (Finset.sum_map ..)
  _ ≤ ∑ i, ((D *ᵥ x) i)^2 := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _=>sq_nonneg _
  _ = _ := by simp [pow_two,dotProduct]


end YM.Further.CurvedGaussianJets.Pockets

namespace YM.Further.CurvedGaussianJets
open Function Filter Matrix Lattice Wilson Tree RG Precision Bid Progress.StationaryScenes SectorNext.Vacuum
open Rows (Bill)
open scoped Matrix.Norms.Frobenius Topology BigOperators Classical
namespace Rates
variable {n : Side} {I J K : Type*} [Fintype I] [Fintype J] [Fintype K] [DecidableEq I] [DecidableEq J] [DecidableEq K] {a : K → Site n} {w L : ℝ}
lemma place_join {A : Table I} {B : Table J} (e : I⊕J ≃ K) (ha : Bill (a ∘ e ∘ Sum.inl) w A L) (hb : Bill (a ∘ e ∘ Sum.inr) w B L) :
    Bill a w (Joint.place e (Joint.join A B)) L := by
  have H {A : Table I} {B : Table J} (ha : Green.Rows (a ∘ e ∘ Sum.inl) (a ∘ e ∘ Sum.inl) A w L) (hb : Green.Rows (a ∘ e ∘ Sum.inr) (a ∘ e ∘ Sum.inr) B w L) : Green.Rows a a (Joint.place e (Joint.join A B)) w L := by
    intro i; obtain ⟨(x|x),rfl⟩ := e.surjective i <;> rw [← e.sum_comp,Fintype.sum_sum_type]
    · simpa [Joint.place,Joint.join] using! ha x
    simpa [Joint.place,Joint.join] using! hb x
  refine ⟨H ha.1 hb.1,?_⟩; convert H ha.2 hb.2 using 1; rw [Joint.place,Joint.join, transpose_submatrix, fromBlocks_transpose]; rfl

lemma extend_rate (v : Prices) (w η L : ℝ) (hw : 0<w) (hη : 0<η) : ∃ v' : Prices, v'.width≤min w v.width ∧ v'.gap≤min 1 (min η v.gap) ∧ max 1 (max L v.mass)≤v'.mass ∧ v'.tags = v.tags :=
    ⟨⟨min w v.width,min 1 (min η v.gap),max 1 (max L v.mass),v.tags, lt_min hw v.width_pos,lt_min zero_lt_one (lt_min hη v.gap_pos),zero_lt_one.trans_le (le_max_left ..)⟩,le_rfl,le_rfl,le_rfl,rfl⟩
lemma slide {v v' : Prices} (hw : v'.width ≤ v.width) (hg : v'.gap ≤ v.gap) (hm : v.mass ≤ v'.mass) (ht : v'.tags=v.tags) {A : Table K} (h : Fits a v A) : Fits a v' A :=
    ⟨h.symm,Rows.bigger (Rows.slower h.entries hw) hm,ht ▸ h.mult,fun x=> (mul_le_mul_of_nonneg_right hg (Joint.dot_nonneg _)).trans (h.floor x)⟩
lemma completes {A : Table I} (e : I⊕J ≃ K) {v : Prices} (h : Rows.Bill (a ∘ e ∘ Sum.inl) v.width A v.mass)
    (ha : A.IsHermitian) (hA : Green.Bottom A v.gap) (he : v.gap≤1) (hm : 1≤v.mass) (hx : Push.Uniform.Multiplicity a v.tags) :
    Fits a v (Joint.place e (Joint.join A 1)) := by
  refine ⟨(Joint.join_herm ha isHermitian_one).submatrix _, place_join e h (Rows.bigger Rows.one hm),hx, fun x=>?_⟩
  refine (Joint.place_numeric e (Joint.join_numeric ?h (Joint.one_numeric he hm)) x).1
  exact fun x=>⟨hA x,Rows.upper v.width_pos.le h x⟩
end Rates
open Pockets


/-- Uniform constructor for the numerical price part of `Stamped` on
these actual columns. Supply BOTH exponential absolute kernel bounds on
the whole affine Gram on the regular coordinates at some positive width
(post-L); not a log estimate. See e.g. Green.Rows.multiply to pass from
bounds on D at its correct row and column addresses. The charge of the
unrelated reference B can come from `Actual.receiving` at its own cutoff
sizes, time now to ALSO meet the output-window containment, t≤δ and
`Pockets.Paid`. This code doesn't authorize spending an ancestor budget on
these new coefficients; don't infer schedules or actual Stays.
-/
theorem issue (G : Gauge) (P : Patch) (K : KernelChoices) (v : Prices) {C w L : ℝ} (hw : 0<w) (hC : 0<C) : ∃ s : Prices, ∃ δ : ℝ, 0<δ ∧ ∀ {f c n : Side} (S : StepData c f), S.patch=P → S.kernel=K → Pockets.Paid S G → ∀ (F : Forest S.ratio) (V : Config G c) (k : S.Choices) (X : Type*) [Fintype X] (H : Finset F.Free)
    {t : ℝ}, 0≤t → t≤δ → Clean H V t → ∀ (a : Key F G → Site n) (B : Table (Key F G)), Fits a v B →
      ∀ A : Matrix X (Bits H G) ℝ, Covers H V k A C → Rows.Bill (a ∘ active H G) w (gram A) L →
      Fits a s B ∧ Fits a s (mount H (gram A)) := by
  obtain ⟨η,δ,hη,hδ,h⟩ := sector_gap G P K
  obtain ⟨s,h1,h2,h3,h4⟩ := Rates.extend_rate v w (η/C) L hw (div_pos hη hC)
  refine ⟨s,δ,hδ,fun {f c n} S hp hK hS F V k X _ H {t} ht hT hv a B hB A hC₁ hA=> ?_⟩
  have h := h S hp hK hS F V k t ht hT
  have hb : Green.Bottom (gram A) (η/C) := fun x=> by
    have hh := h (test H x) (fun e he => by rw [test_eq, FlatTree.blank,dif_pos he]) (clean_core H V x hv)
    rw [test_norm] at hh; have ht := hh.trans (hC₁ x)
    rwa [gram, ←mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, div_mul_eq_mul_div,div_le_iff₀ hC, mul_comm _ C]
  refine ⟨Rates.slide (h1.trans (min_le_right ..)) (h2.trans ((min_le_right ..).trans (min_le_right ..))) ((le_max_right ..).trans ((le_max_right ..).trans h3)) h4 hB,?_⟩
  have hbot : Green.Bottom (gram A) s.gap := fun x => (mul_le_mul_of_nonneg_right (h2.trans ((min_le_right ..).trans (min_le_left ..))) (Joint.dot_nonneg x)).trans (hb x)
  refine Rates.completes (a:=a) (A:=gram A) (tape H G) ?_ (Matrix.isHermitian_conjTranspose_mul_self A) hbot (h2.trans (min_le_left ..)) ((le_max_left ..).trans h3) (h4 ▸ hB.mult)
  change Rows.Bill (a ∘ active H G) s.width (gram A) s.mass
  exact Rows.bigger (Rows.slower hA (h1.trans (min_le_left ..))) ((le_max_left ..).trans ((le_max_right ..).trans h3))
end YM.Further.CurvedGaussianJets
