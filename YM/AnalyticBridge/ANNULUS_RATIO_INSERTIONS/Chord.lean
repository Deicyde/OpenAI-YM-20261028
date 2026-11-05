import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.CovBound
import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.PriceLine
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.ResidualPrice


/-!
# Uniform Schur comparisons for the quantities occurring in the Gaussian bills

Retains a positive rate even for PER and for the (uncut) C inverse.
Needed for square root envelope bookkeeping. Also return mean-window
and residual errors at unweighted Schur cost. Applies *independently*
of the choice of LFR packet but needs same flags. No derivatives evaluated.
Units completed as in call to FS (here only active coords).
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.AnalyticBridge.AnnulusRatioInsertions.Prism
open Function Filter Lattice Wilson RG RG.Patch Precision Exterior Tree MeasureTheory Metric Matrix
open Next.SectorChange Next.SectorChange.Motion Next.SectorChange.Rows Next.SectorChange.Gaussian
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure Push.SectorMeasure.Oriented 
open Tier Wisps Schur LocalJet Completion
   
open scoped Topology InnerProductSpace BigOperators Classical ContDiff Matrix.Norms.Frobenius Push.SectorMeasure

section healing
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
  {A : Gaussian.Table V} {c : Side} {p : V → Site c} {W : V → Set V} (r : ℕ)
  {L η δ v : ℝ}

private lemma snows (p : V → Site c) (v : ℝ) : Pours (-1 : Gaussian.Table V) p p v 1 := by
  constructor
  · norm_num
  · intro i; simp [Matrix.one_apply,rate,apply_ite abs,mul_ite]
  intro i; simp [Matrix.one_apply,rate,apply_ite abs,mul_ite]

private lemma emptyInside {E : Gaussian.Table V} (h : Pours E p p v δ) (hv : 0 ≤ v)
    (he : ∀ i j, separation (p j) (p i) ≤ r → E i j=0) : Pours E p p 0 (δ*rate (-v) r) := by
  have hh i j : rate 0 (separation (p i) (p j))*|E i j| ≤ rate (-v) r*(rate v (separation (p i) (p j))*|E i j|) := by
    by_cases h : separation (p j) (p i) ≤ r
    · simp [he _ _ h]
    simp only [rate, zero_mul,Real.exp_zero, one_mul]
    nth_rw 1 [← one_mul |E i j|]; rw [← mul_assoc (Real.exp _)]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [← Real.exp_add]; refine Real.one_le_exp ?_
    have hp : (r:ℝ) ≤ separation (p i) (p j) := Nat.cast_le.mpr ((le_of_not_ge h).trans_eq (separation_comm ..))
    nlinarith
  refine ⟨mul_nonneg h.pos (rate_pos ..).le, fun i => ((Finset.sum_le_sum (fun j _=>hh i j)).trans ?_),fun j => ((Finset.sum_le_sum (fun i _=>hh i j)).trans ?_)⟩
  · rw [← Finset.mul_sum,mul_comm δ]; exact mul_le_mul_of_nonneg_left (h.row _) (rate_pos ..).le
  rw [← Finset.mul_sum,mul_comm δ]; exact mul_le_mul_of_nonneg_left (h.col _) (rate_pos ..).le

lemma ripple {a}{B : Matrix V I ℝ} {q : I → Site c} (h : Pours B p q v a) (i j) : rate v (separation (p i) (q j))*|B i j|≤a :=
  (Finset.single_le_sum (f:=fun j=> rate v (separation (p i) (q j))*|B i j|) (fun j _=>mul_nonneg (rate_pos ..).le (abs_nonneg _)) (Finset.mem_univ j)).trans (h.row i)

lemma pours_minus {a b} {D : Gaussian.Table V} (h : Pours A p p v a) (hx : Pours D p p v b) : Pours (A-D) p p v (a+b) := by
  have he := h.bind (hx.scale (-1))
  simpa only [neg_one_smul, sub_eq_add_neg,abs_neg,abs_one,one_mul] using he

lemma fading {x : ℕ} {D : Gaussian.Table V} (hv : 0 < v) (he : 0 < η) (hA : A.PosDef) (hG : Gapped A η)
    (h : Pours A p p v L) {E : ℝ} (hi : Pours A⁻¹ p p v E) (hW : Bars W p x)
    (hL : Pours (Schur.per W A) p p v δ) :
    Pours ((per W A)-A⁻¹) p p 0 (E*(L*δ+1)*rate (-v) x) := by
  let M := per W A
  have hx : Pours (A*M-1) p p v (L*δ+1) := by
    rw [sub_eq_add_neg]; exact (h.fuse hL hv.le).bind (snows p v)
  have hn i j (hg : separation (p j) (p i) ≤ x) : (A*M-1) i j = 0 := by
    rw [Matrix.sub_apply]
    dsimp only [M]; rw [Schur.per_check hW (Matrix.isHermitian_iff_isSymm.mp hA.isHermitian) hG he j (hW _ _ hg),sub_self]
  have hl := (hi.weaker (t:=0) hv.le le_rfl).fuse (emptyInside x hx hv.le hn) le_rfl
  rw [Matrix.mul_sub,← Matrix.mul_assoc,A.nonsing_inv_mul ((A.isUnit_iff_isUnit_det).mp hA.isUnit), Matrix.one_mul,Matrix.mul_one,← mul_assoc E] at hl
  exact hl

/-- Also uniform in x, numerical mu residual norm (before applying to b).
Keep two rates. Last buys have ZERO displacement. -/
lemma heal {σ η K g : ℝ} (hs : 0<σ) (hη : 0<η) (hK : 0≤K) (hg : 0<g) (B : ℝ → ℝ) (hB : ∀ v,0≤B v) :
    ∃ v u M : ℝ, 0<v ∧ 0<u ∧ 0<M ∧ ∀ {V : Type} [Fintype V] [DecidableEq V] {c : Side} (p : V → Site c)
    (W : V → Set V) (A : Gaussian.Table V) (r : ℕ), Revenue p B → Pours A p p σ K → Gapped A η → A.PosDef →
      Bars W p r → Gapped (clouded W A) g →
      Pours A p p v M ∧ Pours A⁻¹ p p v M ∧ Pours (per W A) p p v M ∧ Pours (clouded W A) p p v M ∧
        Pours (clouded W A)⁻¹ p p v M ∧ Pours (per W A - A⁻¹) p p 0 (M*rate (-u) r) := by
  obtain ⟨v,m,hv,hv',hm,H⟩ := Schur.provides hs hη hK
  let t := v/2
  have ht : 0<t := half_pos hv
  let F:=B t*m
  have hF : 0≤F := mul_nonneg (hB _) hm.le
  obtain ⟨w,M',hw,hW,hM',H₂⟩:= Schur.provides ht hg hF
  let u:=w/2
  have hu : 0<u := half_pos hw
  let E := B u*M'
  have hE : 0≤E:=mul_nonneg (hB _) hM'.le
  let P := F*(K*F+1)
  have hP : 0≤P := by unfold P; positivity
  let D := 1+K+F+E+P
  have hD : 0<D := by unfold D; positivity
  refine ⟨u,t,D,hu,ht,hD,?_⟩
  intro V _ _ c p W A r hx ha hG hA hr hZ
  let L := per W A
  let Z := clouded W A
  have hL := H p W A ha (Matrix.isHermitian_iff_isSymm.mp hA.isHermitian) hG
  have hi : Pours L p p t F := Revenue.per _ hx hv hm.le (fun i j=> (hL j i).1)
  have hg : Pours A⁻¹ p p t F := Revenue.per _ hx hv hm.le (fun i j=> (hL j i).2)
  have he : Pours Z p p t F := by
    unfold Z clouded
    simpa only [abs_of_nonneg (by norm_num : (0:ℝ)≤1/2), show (1/2:ℝ)*(F+F)=F by ring] using ((hi.bind hi.turn).scale (1/2))
  have ho : Pours Z⁻¹ p p u E := by
    have hZ' : Z.IsSymm := by
      ext i j; change (1/2:ℝ)*(L j i + L i j)=(1/2:ℝ)*(L i j+L j i); rw [add_comm]
    have hi := H₂ p W Z he hZ' hZ
    exact Revenue.per _ hx hw hM'.le (fun i j=> (hi j i).2)
  have h0 : u≤t := (half_le_self hw.le).trans hW
  have h2 : t≤σ := (half_le_self hv.le).trans hv'
  have h1 : u≤σ := h0.trans h2
  refine ⟨ha.weaker h1 (by unfold D; linarith),hg.weaker h0 (by unfold D; linarith),
    hi.weaker h0 (by unfold D; linarith),he.weaker h0 (by unfold D; linarith),ho.weaker le_rfl (by unfold D; linarith),?_⟩
  exact (fading (D:=A) ht hη hA hG (ha.weaker h2 le_rfl) hg hr hi).weaker le_rfl (mul_le_mul_of_nonneg_right (by
    change P≤D; unfold D; linarith) (rate_pos ..).le)
end healing

structure Specs {G : Gauge} {c f : Side} {S : StepData c f} (x : ℝ) (v u a M : ℝ) (T : Tube G S)
    (A : Stores S) (F : Forest S.ratio) (k : S.Choices) (V : Config G c) : Prop where
  tables :
    let p := front A F (G:=G) (x:=x)
    let L := Rows.gram T x V k (shots S x) A F
    let W := panels A F (G:=G) (x:=x); let C:=fog A F T x V k
    L.PosDef ∧ C.PosDef ∧
      Pours L p p v M ∧ Pours L⁻¹ p p v M ∧ Pours (per W L) p p v M ∧ Pours C p p v M ∧ Pours C⁻¹ p p v M ∧
        Pours (per W L-L⁻¹) p p 0 (M*rate (-u) (radiusB x/60)) ∧ Pours (C⁻¹-L) p p 0 (M*rate (-a) (radiusB x))

/-- Uniform (in all A-sector uses at height) procurement for
size + decay incl genuine A,C^-1, mean-window correction. Other two
days use with exponential height delay. -/
theorem holds (G : Gauge) (Q : Patch) (T : Teller G) (h : Q.Branches T.bind G) :
    ∃ v u a M : ℝ, 0<v ∧ 0<u ∧ 0<a ∧ 0<M ∧ ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f) (U : Tube G S), S.patch=Q → 100*(1+radiusB x) ≤ c.val →
    T.Funds S U → ∀ (A : Stores S) (F : Forest S.ratio) (k : S.Choices) (V : Config G c), A.flags=RG.flags (temp x) V →
      Specs x v u a M U A F k V := by
  obtain ⟨e,L,he,hL,H⟩ := visions G Q T h
  obtain ⟨σ,K,η,b,M,hσ,hK,hη,hb,hM,H'⟩ := opaqueCost G Q T h
  let key (v:ℝ):= ((Fintype.card G.ColorIndex:ℝ)*(Fintype.card (Site Q.L)*Fintype.card Axis))*Tier.wealth v
  have hk (v:ℝ):0≤key v:= by unfold key; have := Tier.wealth_nn v; positivity
  obtain ⟨v,u,D,hv,hu,hD,H₂⟩ := heal hσ hη hK he key hk
  obtain ⟨a,Y,ha,hY,H₃⟩ := ResidualPrice.paid_kernel G Q T h
  refine ⟨v,u,a,max D Y,hv,hu,ha,lt_of_lt_of_le hY (le_max_right ..),?_⟩
  filter_upwards [H,H',H₃,Work.E01.radiusB_tendsto.eventually_ge_atTop 120] with x hx ht hs h0
  intro c f S U hS hR hT A F k V hV
  let p := front A F (x:=x) (G:=G); let L := Rows.gram U x V k (shots S x) A F
  let W := panels A F (x:=x) (G:=G)
  obtain ⟨hp,hG,hA,-,-⟩:=ht S U hS hR hT A F k V hV
  obtain ⟨hC,hN,-⟩:=hx S U hS hR hT A F V k hV
  obtain ⟨-,hc,-⟩:=hs S U hS hR hT A F k V hV
  have hj : Fintype.card (Site S.patch.L)=Fintype.card (Site Q.L) := congr_arg (fun t : Patch => Fintype.card (Site t.L)) hS
  have hi (v : ℝ) : Tier.keyFee S G v=key v := by unfold keyFee key; rw [hj]
  have hh : Revenue p key := fun y hy i => (hi y) ▸ Tier.front_price y hy A F G i
  obtain ⟨h1,h2,h3,h4,h5,h6⟩ := H₂ p W L _ hh hp hG hA (boards A F G h0) (fun i=>sumSq_dot i|>.symm ▸ (hN i).1)
  have hl : D ≤ max D Y := le_max_left ..; have hg : Y ≤ max D Y := le_max_right ..
  exact ⟨hA,hC,h1.weaker le_rfl hl,h2.weaker le_rfl hl,h3.weaker le_rfl hl,h4.weaker le_rfl hl,h5.weaker le_rfl hl,h6.weaker le_rfl
    (mul_le_mul_of_nonneg_right hl (rate_pos ..).le),hc.weaker le_rfl (mul_le_mul_of_nonneg_right hg (rate_pos ..).le)⟩
end YM.AnalyticBridge.AnnulusRatioInsertions.Prism
