import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Reprice
import YM.Push.BETA_TRANSPORT.Margins
import YM.Push.PRICE_COMPILER.Continuity
import YM.UVNext.COUPLING_RESET.Reset

/-!
# Assemble the path pairs on their actual channels.

Use absolute summability from the same estimates. This final step on fields is
volume-dependent. No reimposition of an indicator on the sum across
orientations. Includes the all-good reading in the Prereset currency.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.CouplingShape
open Function Filter Lattice RG Wilson Next.Scheduling.Wages UVNext.CouplingReset Work Precision PathData Push.BetaTransport
open scoped BigOperators Matrix.Norms.Frobenius ContDiff InnerProductSpace Classical
variable {G : Gauge} {n : Side} (P : PathData G) (p : Clip) (b : BudgetPoint)

def quadraticMask (U : Config G n) := ∑' i, framed P p b i U
def hub (U : Config G n) := weight * ∑ s : Signed,∑ i,P.baseTerm p b (pull s 0 U) i

section
variable {ι α β : Type}
lemma criss (f : α⊕β→ℝ) (h : Summable f) : ∑' i,f i = (∑' i,f (Sum.inl i))+∑' j,f (Sum.inr j) :=
  Summable.tsum_sum (f:=f) (h.comp_injective Sum.inl_injective) (h.comp_injective Sum.inr_injective)
lemma tally {f : Around n ι → ℝ} (h : Summable f) : ∑' i, f i = ∑ x : Site n, ∑ s : Signed, ∑' i, f (x,s,i) := by
  rw [h.tsum_prod,tsum_fintype]; refine Finset.sum_congr rfl fun i _ => ?_; rw [(h.prod_factor i).tsum_prod,tsum_fintype]
lemma together {x y : ι → G.Color} (hx : Summable x) (hy : Summable y) : (∑' i,∑' j, ⟪x i,y j⟫_ℝ)= ⟪∑' i,x i,∑' j,y j⟫_ℝ := by
  let L:= innerSL ℝ (E:=G.Color)
  have hi i : (∑' j, ⟪x i,y j⟫_ℝ)= L (x i) (∑' j, y j) := ((L (x i)).map_tsum hy).symm
  simp_rw [hi]; exact ((L.flip (∑' j, y j)).map_tsum hx).symm

lemma fixedStep (f : Sequence → ℝ) (h : Summable f) : ∑' i, f i= ∑ i : PlaqAxes,
    (f (i,Sum.inl ()) + ∑' x : ℕ, ∑' y : ℕ,f (i,Sum.inr (x,y))) := by
  rw [h.tsum_prod,tsum_fintype]; refine Finset.sum_congr rfl fun i _ => ?_
  have H:= h.prod_factor i; rw [criss _ H]
  simp only [tsum_fintype (β:=Unit), Fintype.sum_unique]
  exact congr_arg (f (i,Sum.inl ()) + ·) (H.comp_injective Sum.inr_injective).tsum_prod
end

section converge
variable {P p b} {σ C Λ : ℝ}
lemma purchaseY (hd : P.Bounds p σ C Λ) (hg : Grace p b σ) :
    Summable (fun i : Card n => priceY P p b i.token) := (totalBooked (fun i => (young_local P p b i).2.1) (shelfY hd hg)).2.1
lemma purchaseT (hd : P.Bounds p σ C Λ) (hg : Grace p b σ) :
    Summable (fun i : Card n => priceT P p b i.token) := (totalBooked (fun i => (tuned_local P p b i).2.1) (shelfT hd hg)).2.1
lemma purchaseC (hd : P.Bounds p σ C Λ) (hg : Grace p b σ) :
    Summable (fun i : Card n => priceClip P p b i.token) := (totalBooked (ι:=Card n) (f:=fun i=>priceClip P p b i.token) (fun i => price_clip_pos P p b i.token) (shelfClip hd hg)).2.1
lemma frame_cost (hd : P.Bounds p σ C Λ) (hg : Grace p b σ) : Dominated (ι:=Card n) (framed P p b) :=
  ⟨_,purchaseY hd hg,fun i U => mask_cost (young_local P p b i).2 U⟩
lemma summable_attached (hd : P.Bounds p σ C Λ) (hg : Grace p b σ) : Dominated (ι:=Card n) (attachedClip P p b) :=
  ⟨_,purchaseC hd hg,fun i U => clip_claim P p b i.token (pull _ _ U)⟩
lemma broad_cost (hd : P.Bounds p σ C Λ) (hg : Grace p b σ) : Dominated (ι:=Card n) (broad P p b) :=
  ⟨_,purchaseT hd hg,fun i U => mask_cost (sup_extend (tuned_local P p b i).2 (petal P b i)) U⟩
lemma narrow_cost (hd : P.Bounds p σ C Λ) (hg : Grace p b σ) : Dominated (ι:=Card n) (narrow P p b) :=
  ⟨_,purchaseT hd hg,fun i U => mask_cost (tuned_local P p b i).2 U⟩
end converge

private lemma fuse_literal (i : PlaqAxes) {σ C Λ : ℝ} (hd : P.Bounds p σ C Λ) (U : Config G n) : let w := fun k => literal P p b (i,k) U
    w (Sum.inl ()) + (∑' x : ℕ, ∑' y : ℕ, w (Sum.inr (x,y)))=weight*P.baseTerm p b U (directWord i) := by
  intro w; unfold baseTerm
  by_cases hh : PathData.kept p b.threshold (0:Site n) U
  · rw [if_pos (show kept p b.threshold (directWord (n:=n) i).1 U from hh),mul_add]
    refine congr_arg₂ (·+·) rfl ?_
    let f (j : ℕ) := P.ellTerms (directWord i) j U
    have hf := (P.ell_dominated hd (directWord i)).summable U
    have hg (x y : ℕ) : w (Sum.inr (x,y)) = weight/2 * ⟪f x,f y⟫_ℝ := by
      simp only [w,literal,Sum.elim_inr, hh,↓reduceIte,raw]; unfold f ellTerms
      simp only [real_inner_smul_left,real_inner_smul_right]; unfold directWord copper earnCoeff first; ring
    simp_rw [hg]; rw [← real_inner_self_eq_norm_sq]; simp_rw [tsum_mul_left]
    rw [together (x:=f) (y:=f) hf hf]; unfold f ell; ring
  simp [w,literal, directWord,hh]

lemma recenter (s : Signed) (t : Site n) (U : Config G n) : pull s (s.act t) U = translate t (pull s 0 U) := by
  rw [← pull_one, pull_pull,mul_one]; simp [affine]

lemma movedBase (t x : Site n) (i : PlaqAxes) (U : Config G n) :
    P.baseTerm p b (translate t U) (x,i)=P.baseTerm p b U (x+t,i) := by
  let S := (Equiv.addRight t).prodCongr (Equiv.refl PlaqAxes)
  have he (i : Face (Per n)) : faceValue (translate t U) i = faceValue U (S i) := by rw [← pull_one]; simp [faceValue, S,affine, travel_pull]
  have hK : kept p b.threshold x (translate t U) ↔ kept p b.threshold (x+t) U := by
    unfold kept
    symm; rw [← S.forall_congr_right]; simp_rw [he,show ∀ p : Face (Per n), (S p).1=p.1+t from fun _ => rfl,separation_translate]
  have hx (T : Slot) : T.atSite (translate t U) x=T.atSite U (x+t) := by
    unfold Slot.atSite; congr 1; funext; simp [expandAt,Lattice.translate,add_assoc]
  unfold baseTerm; simp_rw [he]; simp only [show S (x,i)=(x+t,i) from rfl,hK, ell,ellTerms,hx]

variable {P p b} {σ C Λ : ℝ}
lemma sums_hub (hd : P.Bounds p σ C Λ) (hg : Grace p b σ) (U : Config G n) : (∑' i, attachedClip P p b i U)=hub P p b U := by
  let f (i : Card n) := attachedClip P p b i U
  have hh : Summable f := (summable_attached hd hg).summable U
  rw [tally (f:=f) hh,Finset.sum_comm,hub,Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => ?_
  rw [Fintype.sum_prod_type, Finset.mul_sum, ← Equiv.sum_comp (s.actEquiv (R:=Per n)).toEquiv (fun x => ∑' i, f (x,s,i))]
  refine Finset.sum_congr rfl fun x _ => ?_
  change (∑' i, f (s.act x,s,i))=_; rw [fixedStep _ ((hh.prod_factor _).prod_factor _),Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  trans weight * P.baseTerm p b (pull s (s.act x) U) (directWord i)
  · exact fuse_literal P p b i hd ..
  rw [recenter,directWord,movedBase P p b x 0,zero_add]


end YM.AnalyticBridge.CouplingShape
