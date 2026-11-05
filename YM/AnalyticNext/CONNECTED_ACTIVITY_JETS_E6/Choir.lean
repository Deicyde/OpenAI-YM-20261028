import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.AirG

/-!
# Stamp symmetry -- intermediate positions really kept

Important: within-letter color sums traced before use. Entry-wise expression
in rotated gauge. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Hues
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented  Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll  
open Gas Ursell Trees    Rotation
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Tree.Forest S.ratio}
variable {a α W μ C η r Q Y : ℝ} {R : Rep G f} {L : Side} {B : ℕ}
variable (X : Coat T F) (z : Site c→ G.El) {A H A' : Mat f G}

-- generic pure matrix rotation on link blocks. Avoid forgetting finite norm after formula.
lemma cross_left (he : ∀ i j:Tubular f G,i.1≠j.1 → H i j=0) (A : Mat f G) (p q : Bond f) :
    Itinerary.restrict (H*A) p q= restrict H p p*restrict A p q := by
  ext i j; change (H*A) _ _=_; rw [Matrix.mul_apply,Fintype.sum_prod_type]
  rw [Finset.sum_eq_single p]
  · rw [Matrix.mul_apply]; rfl
  · intro b _ h; apply sum_eq_zero; intro l _; rw [he (p,i) (b,l) (Ne.symm h),zero_mul]
  simp
lemma cross_right (he : ∀ i j:Tubular f G,i.1≠j.1 → H i j=0) (A : Mat f G) (p q : Bond f) :
    Itinerary.restrict (A*H) p q= restrict A p q*restrict H q q := by
  ext i j; change (A*H) _ _=_; rw [Matrix.mul_apply,Fintype.sum_prod_type]
  rw [Finset.sum_eq_single q]
  · rw [Matrix.mul_apply]; rfl
  · intro b _ h; apply sum_eq_zero; intro l _; rw [he (b,l) (q,j) h,mul_zero]
  simp
lemma combo_respects {n : ℕ} (s : Bond f) (p : Itinerary f n) (he : ∀ i j:Tubular f G,i.1≠j.1 → H i j=0)
    (A Z : ℕ→Mat f G) (h : ∀ i,n>i→ A i*H=H*Z i) :
      combo s p A*restrict H (arrive s p) (arrive s p)=restrict H s s*combo s p Z := by
  induction n generalizing s A Z with
  | zero => simp [combo,arrive]
  | succ k ih =>
    let i:= Itinerary.next p
    have hh : restrict (A 0) s i*restrict H i i=restrict H s s*restrict (Z 0) s i := by
      rw [← cross_right he,← cross_left he,h 0 (by omega)]
    rw [combo, arrive, mul_assoc, ih i (Itinerary.after p) (fun i=>A (i+1)) (fun i=>Z (i+1)) (fun j hj => h (j+1) (by omega)),
      combo,← mul_assoc, hh, mul_assoc]
lemma pools (p : Bond f) (he : ∀ i j:Tubular f G,i.1≠j.1→H i j=0) (hv : Hᵀ*H=1) :
    (restrict H p p)ᵀ*restrict H p p=1 := by
  rw [show (restrict H p p)ᵀ=restrict Hᵀ p p from rfl,← cross_right he,hv]
  ext i j; change (1:Mat f G) (p,i) (p,j)=_; simp [Matrix.one_apply]
lemma stamps_turn {n : ℕ} (s : Bond f) (p : Itinerary f n) (he : ∀ i j:Tubular f G,i.1≠j.1→ H i j=0)
    (A Z : ℝ→ℕ→Mat f G) (h : ∀ t i, i<n→ A t i*H=H*Z t i) (hq : Hᵀ*H=1)
    (hx : ∀ i,i<n→ ContinuousOn (fun t=> A t i) (Set.uIcc 0 1)) (hz : ∀ i,i<n→ ContinuousOn (fun t=> Z t i) (Set.uIcc 0 1)) :
    stamp A s p=stamp Z s p := by
  by_cases hp : arrive s p=s
  swap; · simp [stamp,checkIn,hp]
  have hv (A : ℝ→ℕ→Mat f G) (h : ∀ i,i<n→ ContinuousOn (fun t=>A t i) (Set.uIcc 0 1)) :
      stamp A s p=∫ t in (0:ℝ)..1, trace (combo s p (A t)) := by
    unfold stamp checkIn; simp_rw [if_pos hp]
    have ht (i) : IntervalIntegrable (fun t=> combo s p (A t) i i) volume 0 1 :=
      (continuousOn_pi.mp (continuousOn_pi.mp (combo_continuous s p A _ h) i) i).intervalIntegrable
    exact (intervalIntegral.integral_finsetSum (fun j _=> ht j)).symm
  let C:=restrict H s s
  have hc : Cᵀ*C=1 := pools s he hq
  have hy (t) : trace (combo s p (A t))=trace (combo s p (Z t)) := by
    have ht := combo_respects s p he (A t) (Z t) (h t); rw [hp] at ht
    have hh : C*Cᵀ=1 := mul_eq_one_comm.mp hc
    rw [← Matrix.mul_one (combo _ _ (A _)),← hh,← Matrix.mul_assoc,ht, Matrix.trace_mul_comm, ← mul_assoc, hc, Matrix.one_mul]
  rw [hv A hx,hv Z hz]; simp_rw [hy]

section colors
variable (hp : Room P S T X.x) (h : P.Funds S T)
variable (hP : Rotator P L η r Q Y X) (hr : Rotator P L η r Q Y (sluice X z))
include h
lemma commutes (s : ℝ) :
    let D:= X.shutter; let Y:=sluice X z; let E:= sheen X z
    (∀ i,aSeq D Y.plate s i*E= E*aSeq D X.plate s i) ∧ ∀ i,sSeq D Y.plate s i*E= E*sSeq D X.plate s i := by
  intro D Y E
  have hg := plate_con X z h
  have he : glide Y.plate s* E=E*glide X.plate s := by
    unfold glide; rw [mul_add,add_mul,one_mul,mul_one, Matrix.mul_smul, smul_mul_assoc,sub_mul,mul_sub,hg,one_mul,mul_one]
  have hv := pad_rotates X z he; constructor
  · intro i; match i with
    | 0 => change (Y.plate-1)*_= E*(X.plate-1); rw [sub_mul,mul_sub,hg,one_mul,mul_one]
    | 1 => exact hv
    | k+2 =>
      simp only [aSeq,error,neg_mul,mul_neg]; rw [sub_mul,mul_sub,one_mul,mul_one,mul_assoc,hv,←mul_assoc,he,mul_assoc]
  intro i; cases i
  · exact shredsG X z h
  next i =>
    have hX : D.flawed Y.plate * E=E*D.flawed X.plate := shredsG X z h; simp only [sSeq,neg_mul,mul_neg, Matrix.mul_smul, smul_mul_assoc,hX]

include hP hr
lemma porous : (∀ i : Ledger f 3, ArmA X.shutter (sluice X z).plate i=ArmA X.shutter X.plate i) ∧
    ∀ i : Ledger f 1, ArmS X.shutter (sluice X z).plate i=ArmS X.shutter X.plate i := by
  let D:=X.shutter; let F:=X.plate; let E := sheen X z
  have he i j (h : Prod.fst i≠ Prod.fst j) : E i j=0 := Rotation.off (z ∘ atEdge S) i j h
  have hy (A: Mat f G) (H : Allow A (along S) (tubularPrice G L) η r Q) (s : ℕ) : ContinuousOn
      (fun t=> aSeq D A t s) (Set.uIcc 0 1) := by
    match s with
    | 0 => exact continuousOn_const
    | 1=> exact vibrate D A H hP.full
    | _+2=> exact ContinuousOn.neg (ContinuousOn.sub ((strung A).continuousOn.mul (vibrate D A H hP.full)) continuousOn_const)
  have hg (A : Mat f G) (s : ℕ) : ContinuousOn (fun t=> sSeq D A t s) (Set.uIcc 0 1) := by
    cases s
    · exact continuousOn_const
    · exact ContinuousOn.neg (continuousOn_id.smul continuousOn_const)
  exact ⟨fun i=> stamps_turn _ _ he (aSeq D (sluice X z).plate) (aSeq D X.plate) (fun t i _=> (commutes X z h t).1 i)
    (inverse_up _) (fun i _ => hy _ hr.scale i) (fun i _=> hy _ hP.scale i), fun i=> stamps_turn _ _ he (sSeq D (sluice X z).plate)
      (sSeq D X.plate) (fun t i _=> (commutes X z h t).2 i) (inverse_up _) (fun i _=>hg _ i) (fun i _=>hg _ i)⟩
lemma drip (i : Bond f) : (sluice X z).condensation i=X.condensation i := by
  let D:=X.shutter; let Y:= sluice X z; let A:=Y.plate
  have hb : Y.blank.plate=X.blank.plate := ConnectedActivityE6.neutral Y X rfl
  have he : Batch.joint A D i= Batch.joint X.plate D i := by
    rw [Batch.joint_coil _ D hr.scale hr.full, Batch.joint_coil _ D hP.scale hP.full]
    refine intervalIntegral.integral_congr fun s hs=> ?_
    rw [Set.uIcc_of_le zero_le_one] at hs
    exact Batch.rinse_at i s D (plate_con X z h) (inverse_up _) (hP.scale.glide hP.full.hv hP.full.hQ s hs)
      (hr.scale.glide hP.full.hv hP.full.hQ s hs) (Rotation.off (z ∘ atEdge S)) rfl
  unfold condensation; change (Batch.joint Y.blank.plate D i-Batch.joint A D i)/_= _; rw [he,hb]
end colors
end YM.ConnectedActivityE6.Hues
