import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Pricing


/-!
# Geometric movement and actual unmarked terms

Paths priced at their actual lengths; in particular `kept` is shifted
rather than shortened and only the WHOLE channels sum is asserted
signed invariant. Move final flags using the actual site pull and tested
plaquettes. Use on the tagged Coefficient operations. Claims here about
functions at finite cutoff; no cover-to-limit claim for the charges.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Equivariance
open Function Filter Lattice Wilson RG Source Analysis MeasureTheory Next.Foundations
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {n : Side}

abbrev affinePerm (s : Signed) (b : Site n) := StepData.sendSites s b

lemma affine_injective (s : Signed) (b : Site n) : Injective (affine s b) :=
  (affinePerm s b).injective

lemma affine_surjective (s : Signed) (b : Site n) : Surjective (affine s b) :=
  (affinePerm s b).surjective

section Support
lemma wraps (s : Signed) (b o : Site n) (X : Support n) :
    Nonwrapping (X.image (affine s b)) (affine s b o) ↔ Nonwrapping X o := by
  unfold Nonwrapping; simp [affine]

lemma moves_halo (s : Signed) (b : Site n) (X : Support n) (M : ℕ) (x : Site n) :
    affine s b x ∈ halo M (X.image (affine s b)) ↔ x ∈ halo M X := by
  rw [halo_spec,halo_spec]; simp only [Finset.exists_mem_image]; simp [affine]

lemma moves_cover (s : Signed) (b : Site n) (X D : Support n) (M : ℕ) (he : covers M X D) :
    covers M (X.image (affine s b)) (D.image (affine s b)) := by
  constructor
  · intro x hx; obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact (moves_halo s b _ _ _).2 (he.1 hy)
  intro x hx y hy
  obtain ⟨x,rfl⟩ := affine_surjective s b x
  obtain ⟨y,rfl⟩ := affine_surjective s b y
  refine Relation.ReflTransGen.lift (affine s b) ?_ x y (he.2 x ((moves_halo s b D M x).1 hx) y
    ((moves_halo s b D M y).1 hy))
  intro u v hu
  exact ⟨(moves_halo ..).2 hu.1,(moves_halo ..).2 hu.2.1,by simpa [affine] using hu.2.2⟩

lemma moves_cost (s : Signed) (b : Site n) (X : Support n) (M : ℕ) :
    coverNumber M (X.image (affine s b)) = coverNumber M X := by
  classical
  have he (s : Signed) (b : Site n) (X : Support n) : coverNumber M (X.image (affine s b)) ≤ coverNumber M X := by
    obtain ⟨D,hD,hh⟩ := coverNumber_realized M X
    unfold coverNumber
    refine Nat.find_min' (H := covers_some M (X.image (affine s b))) ⟨_,moves_cover s b X D M hD,?_⟩
    rw [Finset.card_image_of_injective D (affine_injective s b)]; exact hh
  apply le_antisymm (he ..)
  have hx : (X.image (affine s b)).image (affine s⁻¹ (- s⁻¹.act b)) = X := by
    rw [Finset.image_image]; simp only [Function.comp_def,affine,Signed.act_add,Signed.inv_act,add_neg_cancel_right]
    simp
  have hi := he s⁻¹ (- s⁻¹.act b) (X.image (affine s b))
  rwa [hx] at hi

lemma final_pull {X : Sort*} (s : Signed) (b : Site n) (B : Support n) {F : Config G n → X} {t : ℝ}
    (h : UsesFinal t B F) : UsesFinal t (B.image (affine s b)) (F ∘ pull s b) := by
  intro U V huv he
  apply h _ _ (agrees_pull s b B huv)
  apply Finset.image_injective (affine_injective s b)
  rw [Finset.image_inter _ _ (affine_injective s b), Finset.image_inter _ _ (affine_injective s b),
    Work.H03.flags_send,Work.H03.flags_send]; exact he

lemma pull_constant (s : Signed) (b : Site n) : pull s b (1 : Config G n) = 1 := by
  ext1 e; simp [pull,Step.read]

lemma pull_gauge (s : Signed) (b : Site n) (k : Site n → G.El) (U : Config G n) :
    pull s b (Lattice.gauge k U) = Lattice.gauge (k ∘ affine s b) (pull s b U) := by
  funext e
  unfold pull; rw [Step.gauge_read]
  unfold Lattice.gauge; rw [Function.comp_apply,Function.comp_apply,affine_end]
end Support

lemma mask_pull {X : Type*} [Zero X] (s : Signed) (b : Site n) (B : Support n) (F : Config G n → X) (t : ℝ) (U : Config G n) :
    masked t (B.image (affine s b)) (F ∘ pull s b) U = masked t B F (pull s b U) := by
  by_cases he : Healthy t B (pull s b U)
  · rw [masked_eq _ _ _ _ he,masked_eq _ _ _ _ ((healthy_pull ..).1 he)]; rfl
  rw [masked_ne _ _ _ _ he,masked_ne _ _ _ _ (fun h => he ((healthy_pull ..).2 h))]

section Vacuum
private lemma face_shift (U : Config G n) (b : Site n) (p : Face (Per n)) :
    faceValue (translate b U) p = faceValue U (p.1+b,p.2) := by
  rw [← pull_one,faceValue,travel_pull]
  simp only [Step.rotate_one, affine,Signed.act_one]; rfl

private lemma spread_shift (U : Config G n) (b x : Site n) :
    expandAt x (translate b U) = expandAt (x+b) U := by
  funext e; simp [expandAt,translate,add_assoc]

lemma principal_shift (R : PathData G) (c : Clip) (p : BudgetPoint) (β : ℝ) (U : Config G n) (b : Site n) :
    R.principal c p β (translate b U) = R.principal c p β U := by
  let L := Equiv.addRight b
  let M := Equiv.prodCongr L (Equiv.refl PlaqAxes)
  have hm (q : Face (Per n)) : M q = (q.1+b,q.2) := rfl
  have he (q : Face (Per n)) : R.baseTerm c p (translate b U) q = R.baseTerm c p U (M q) := by
    have ht (x : Site n) : PathData.kept c p.threshold x (translate b U) ↔ PathData.kept c p.threshold (x+b) U := by
      unfold PathData.kept; conv_rhs => rw [M.surjective.forall]
      simp only [hm, face_shift, separation_translate]
    classical
    unfold PathData.baseTerm; rw [ht,hm,face_shift]
    suffices hh : R.ell (translate b U) q = R.ell U (q.1+b,q.2) by rw [hh]
    unfold PathData.ell PathData.ellTerms Slot.atSite; simp_rw [spread_shift]
  have hx (k : ℕ) (r : ℕ → Atom G k) (x : Site n) :
      PathData.atomSeries r p (translate b U) x = PathData.atomSeries r p U (x+b) := by
    refine tsum_congr fun i => ?_
    have hX : (r i).footprint (x+b) = ((r i).footprint x).image (affine 1 b) := by
      unfold Atom.footprint; simp only [Function.comp_def,affine,Signed.act_one,Finset.image_image,add_assoc]
    have hh : (fun V => (r i).unmasked V (x+b)) = (fun V => (r i).unmasked V x) ∘ pull 1 b := by
      funext V; unfold Atom.unmasked Slot.atSite; rw [Function.comp_apply,pull_one]; simp_rw [spread_shift]
    change (r i).placed p (translate b U) x = (r i).placed p U (x+b)
    unfold Atom.placed; rw [hX,hh,mask_pull,pull_one]
  unfold PathData.principal
  simp_rw [he,hx]; rw [M.sum_comp (R.baseTerm c p U)]; congr 1
  · congr 2; exact Equiv.sum_comp L (fun x => PathData.atomSeries R.cubic p U x + PathData.atomSeries R.quartic p U x)
  exact Equiv.sum_comp L (PathData.atomSeries R.loop p U)

lemma channels_pull (R : PathData G) (c : Clip) (p : BudgetPoint) (β : ℝ) (U : Config G n)
    (s : Signed) (b : Site n) : R.inChannels c p β (pull s b U) = R.inChannels c p β U := by
  have ht (k : Signed) : R.principal c p β (pull k 0 (pull s b U)) =
      R.principal c p β (pull (s*k) 0 U) := by
    rw [pull_pull]
    let q : Signed := s*k
    have hh : pull q (affine s b 0) U = translate (q⁻¹.act b) (pull q 0 U) := by
      rw [← pull_one, pull_pull]; simp [affine]
    rw [hh,principal_shift]
  unfold PathData.inChannels; simp_rw [ht]
  exact congr_arg _ (Equiv.sum_comp (Equiv.mulLeft s) (fun k : Signed => R.principal c p β (pull k 0 U)))

/-- The *unmarked* label actions are available in `Activities.Valid`. -/
lemma additive_pull {A : Activities G n} (p : BudgetPoint) (U : Config G n)
    {s : Signed} {b : Site n} (h : A.Moves s b) : A.additive p (pull s b U) = A.additive p U := by
  unfold Activities.additive; rw [← h.ep.tsum_eq (fun i : ℕ => A.regularOccurrence p i U)]
  refine tsum_congr fun i => ?_
  unfold Activities.regularOccurrence; rw [h.reg_support,show A.E (h.ep i) = A.E i ∘ pull s b from funext (h.valuesE i),mask_pull]

lemma exponent_pull {R : Rep G n} (U : Config G n) {s : Signed} {b : Site n} (h : R.activities.Moves s b) :
    R.exponent (pull s b U) = R.exponent U := by
  unfold Rep.exponent; rw [channels_pull,additive_pull R.p U h]
end Vacuum
end YM.ProjectorNext.Equivariance
