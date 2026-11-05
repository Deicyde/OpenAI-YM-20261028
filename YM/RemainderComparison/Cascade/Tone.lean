import YM.RemainderComparison.Cascade.Conduct
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lotus.Palette
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lotus
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
namespace Team
variable (M : Team R) (X : Coat T F) (k:Finset ℕ)
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Shield Eider Flux Hues Rotation
open Packets Art Silica Poll Pond
variable {X':Coat T F} {H: Support c} {I : Finset (Tubular f G)} {Z : Support c} {k k' : Finset ℕ} {l : ℕ}
    {u v : Air f G} (p:Molecule S)
open Hues Rotation Stained
lemma rotation_lens {ι : Type} [Fintype ι] [DecidableEq ι] {A H Z : Matrix ι ι ℝ} (hp : A*H=H*Z) (he : H*Hᵀ=1) :
    ∃ E : Body ι≃ₗᵢ[ℝ] Body ι, ∀ t, (E t).ofLp= H *ᵥ (WithLp.ofLp t) ∧ lens₀ A (E t)=lens₀ Z t := by
  let L := Matrix.toEuclideanLin H
  have hh w v : inner ℝ (L w) (L v)=inner ℝ w v := by
    simp_rw [PiLp.inner_apply,RCLike.inner_apply,starRingEnd_apply,star_trivial]; exact respects _ (mul_eq_one_comm.mp he) (WithLp.ofLp v) (WithLp.ofLp w)
  have ht : A.det= Z.det:= mul_right_cancel₀ (Matrix.isUnit_det_of_right_inverse he).ne_zero (by rw [mul_comm Z.det,← Matrix.det_mul,hp,Matrix.det_mul])
  have hz : Surjective (L.isometryOfInner hh) := by
    intro x; refine ⟨WithLp.toLp _ (Hᵀ *ᵥ x.ofLp),?_⟩
    change WithLp.toLp _ (H *ᵥ (Hᵀ *ᵥ x.ofLp))=x; rw [Matrix.mulVec_mulVec,he,Matrix.one_mulVec,WithLp.toLp_ofLp]
  let V:= LinearIsometryEquiv.ofSurjective _ hz
  refine ⟨V,fun t=> ⟨rfl,?_⟩⟩
  unfold lens₀; rw [ht,show (V t).ofLp= H *ᵥ t.ofLp from rfl,Matrix.mulVec_mulVec,reverses hp he, ← Matrix.mulVec_mulVec,
    respects _ (mul_eq_one_comm.mp he)]

open Hues Rotation Stained
variable (e : Intake P T X.x R) (h : ShellAccess S G X.x W X.width r)
include h e
lemma coastal  (i : Finset (Bond f)) (z : Site c→ G.El) (hÑ : LocalRatio Ñ) (ha : 0 < a*X.t) (hx : 4*a*X.t < Ñ.radius) (hp : Hue X) :
    M.cinema (rinse X z) p W a Ñ l (lensS i G)=M.cinema X p W a Ñ l (lensS i G) := by
  let B:=lensS i G; let Y:=rinse X z; let E:= Hues.sheen X z; let H:=Pond.circuit B E
  let A:=Pond.circuit B X.relating; let Z:=Pond.circuit B Y.relating
  have he : Y.relating*E=E*X.relating := relatesG X z e.ready
  have hB i j (hi:i∈ B) (hj:j∉ B) : E i j=0 ∧ E j i=0 := by
    have ht : i.1≠j.1 := by intro h; apply hj; refine mem_product.mpr ⟨h ▸ (mem_product.mp hi).1,mem_univ _⟩
    exact ⟨Rotation.off (z ∘ atEdge S) i j ht,Rotation.off (z ∘ atEdge S) _ _ ht.symm⟩
  have hs : Z*H=H*A := by
    change Batch.principal B _*Batch.principal B _= Batch.principal B _*Batch.principal B _
    rw [← Batch.localize_right (fun i hi j hj=> (hB j i hj hi).2), ← Batch.localize_left (fun i hi j hj=> (hB i j hi hj).1),he]
  have hh : H*Hᵀ=1 := by
    change Batch.principal B E*Batch.principal B Eᵀ=1
    rw [← Batch.localize_left (fun i hi j hj=> (hB i j hi hj).1),Rotation.upside, Batch.within_one]
  obtain ⟨V,hV⟩:= rotation_lens hs hh; let k:=Matter.own p
  have hg (t) : Pond.spill B (V t)=weep X z (Pond.spill B t) := by
    ext i; change (spill B (V t)) i= (E *ᵥ (spill B t).ofLp) i; simp only [Matrix.mulVec,dotProduct]
    classical
    rw [← Finset.sum_subset (subset_univ B) (f:=fun j => E i j*(spill B t).ofLp j) (fun j _ hj=> by simp [Pond.spill,hj])]
    by_cases h : i∈ B
    · have hh : (spill B (V t)) i=(V t).ofLp ⟨i,h⟩ := by simp [Pond.spill,h]
      rw [hh, (hV t).1, Matrix.mulVec, dotProduct, ← sum_attach B]; exact Finset.sum_congr rfl fun j _=> by simp [Pond.spill,j.2]; exact Or.inl rfl
    simp only [Pond.spill,WithLp.ofLp_toLp]
    rw [dif_neg h]; symm; apply sum_eq_zero; intro j hj; rw [(hB _ _ hj h).2,zero_mul]
  unfold cinema
  rw [← (drinking X z).integral_comp' (fun y=> ∫ t, lens₀ Z t*M.floret (Y.wrapY y) p W a Ñ k l (Pond.spill B t))]
  apply integral_congr_ae; filter_upwards with y
  rw [← V.measurePreserving.integral_comp V.toHomeomorph.measurableEmbedding (fun t=> lens₀ Z t*M.floret (Y.wrapY (pairs X z y)) p W a Ñ k l (Pond.spill B t))]
  apply integral_congr_ae; filter_upwards with u
  rw [(hV u).2,hg]; apply congr_arg₂ (·*·) rfl
  let X' := X.wrapY y; let w:=Pond.spill B u; let v:=worldZ X' R.beta w
  let Z':=sluice X' z; let u':=weep X z w
  have hE:spinRow S z v=worldZ Z' R.beta u':=(flight X' z e.ready h ..).symm
  unfold floret; split
  next hv =>
    change M.paidU Z' a (worldZ Z' R.beta u') * floating Z' a R W Ñ u' k l (p\M.signs S)= _
    refine congr_arg₂ (·*·) ?_ ?_
    · rw [← hE]; apply Finset.prod_congr rfl; intro i hi
      unfold Leaf.paidU Leaf.fond; rw [Hues.banks X' z v, i.glows]; exact congr_arg _ (show _=X'.enforce _ _ _ from Hues.mandate X' z (2*a) v (X'.plaza _))
    apply Finset.prod_congr rfl; intro i hi; have hh:= fights X' z (show ShellAccess S G X'.x W X'.width r from h) (show Intake P T X'.x R from e) l k hÑ (show 0<a*X'.t from ha) hx hp v w i
    change Polar.ember Z' a R W Ñ (spinRow S z v) (Z'.input (spinRow S z v)) u' k l i=_ at hh; rw [hE] at hh; exact hh
  rfl
end Team
end YM.PhysicalNext.Repeat.Lotus
