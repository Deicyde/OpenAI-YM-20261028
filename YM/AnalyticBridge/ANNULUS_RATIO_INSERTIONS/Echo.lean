import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.Origin
import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.Voucher
import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.Weather
import YM.Next.FREE_KERNELS.Amend
import YM.Next.SCHEDULE.GridCost
import YM.Next.SCHEDULE.Stadium

/-!
# Adding the true linear ratio to the r4 invoice

Per *physical link* letter. Same limitations as in Weather (support
not isolated, and not enough for derivative/complex arguments). Calls
μ on same common Y and tag. In  terms: root costs independent of
which bowl at entrance. This work doesn't price η with any positive
argument orders, nor ζ for a low-order regrading.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.AnalyticBridge.AnnulusRatioInsertions.Prism.Breeze
open Function Filter Lattice Wilson RG RG.Patch Precision Exterior Tree MeasureTheory Metric Matrix
open Next.Fluctuations Next.SectorChange Next.SectorChange.Motion Next.SectorChange.Rows Next.SectorChange.Gaussian
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure Push.SectorMeasure.Oriented Presented
open Tier Wisps Schur LocalJet Completion
open SectorNext.Remainder SectorNext.Remainder.Affine Harvest Dress
open Arc
open scoped Topology InnerProductSpace BigOperators Classical ContDiff Matrix.Norms.Frobenius Push.SectorMeasure

/- avoid conflict hits -/
variable {I N : Type} [Fintype I] [DecidableEq I] {G : Gauge}

def plume {c f : Side} (S : StepData c f) (T : Tube G S) (A : Stores S) (F : Forest S.ratio)
    (k:S.Choices) (V:Config G c) (q:Chi) (x d g:ℝ) (Y : LinkArray G (Frozen A x F)) :=
  Rows.eta T x V k (shots S x) A F q d Y (meanLog A F T x V k q d Y) g

@[fun_prop] lemma measurable_plume {c f : Side} (S : StepData c f) (T : Tube G S) (A : Stores S) (F : Forest S.ratio)
    (k:S.Choices) (V:Config G c) (q:Chi) (x d g:ℝ) {P : Teller G} (h : P.Funds S T) (hd : 0<d) (h1 : 2*d<firstRadius G) :
    Measurable (plume S T A F k V q x d g) := by
  obtain ⟨l₁,l₂,hA,-⟩:=h.feeds
  have he := (meanLog_cont A F T x V k q d h hd h1).measurable
  have hz := (source_continuous T x V k (shots S x) A F q d hA hd h1).measurable
  unfold plume Rows.eta blame; fun_prop (disch:=first|assumption|rfl)

lemma eta_price {c f : Side} (S : StepData c f) (T : Tube G S) (A : Stores S) (F : Forest S.ratio)
    (k:S.Choices) (V:Config G c) (q:Chi) (x d g : ℝ) (Y : LinkArray G (Frozen A x F)) {v u a M H : ℝ}
    (hv : 0≤v) (hg:0<g) (hM:0≤M) (hH:0≤H)
    (h : Specs x v u a M T A F k V) (hY : ∀ i:In x A F (G:=G), |blame T x V k (shots S x) A F q d Y i| ≤ H) (i) :
    |plume S T A F k V q x d g Y i| ≤ g⁻¹*M^2*H*rate (-u) (radiusB x/60) := by
  obtain ⟨ht,-,hg',-,hp,-,-,he,-⟩:=h.tables
  let W:=shots S x; let L:=Rows.gram T x V k W A F
  let s:=rate (-u) (radiusB x/60); let U:= per (panels A F) L
  let b:= blame T x V k W A F q d Y
  have hz : 0≤s := (rate_pos ..).le
  have h := diary hv (mul_nonneg (mul_nonneg hM hz) hH) hg' _ (diary (v:=0) (by norm_num)
    hH he.turn b hY) i -- s isn't a binder
  have hL : L.IsSymm := Matrix.isHermitian_iff_isSymm.mp ht.isHermitian
  have ha : L *ᵥ ((L⁻¹).transpose *ᵥ b)=b := by rw [hL.inv.eq,mulVec_mulVec,L.mul_nonsing_inv
    ((L.isUnit_iff_isUnit_det).mp ht.isUnit),one_mulVec]
  have hx : Rows.gram T x V k W A F *ᵥ meanLog A F T x V k q d Y + b =
      -(L *ᵥ ((U-L⁻¹).transpose *ᵥ b)) := by
    unfold meanLog
    change L*ᵥ ((-Uᵀ) *ᵥ b) + b=-(L*ᵥ ((U-L⁻¹)ᵀ *ᵥ b))
    rw [Matrix.neg_mulVec,Matrix.mulVec_neg,transpose_sub,sub_mulVec,mulVec_sub,ha]; abel
  change |((-g⁻¹) * (L *ᵥ meanLog A F T x V k q d Y+b) i)| ≤ _
  rw [hx,Pi.neg_apply,abs_mul,abs_neg,abs_neg,abs_of_nonneg (inv_nonneg.mpr hg.le)]
  apply le_trans (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hg.le))
  unfold s; ring_nf; rfl

def ray (u x : ℝ) := rate (-(u/480)) (radiusB x)

lemma ray_pos (u x) : 0 < ray u x := rate_pos ..
lemma ray_goes {u} (h : 0<u) : Tendsto (ray u) atTop (𝓝 0) := Real.tendsto_exp_atBot.comp
  ((tendsto_natCast_atTop_atTop (R:=ℝ)|>.comp Work.E01.radiusB_tendsto) |>.const_mul_atTop_of_neg (neg_lt_zero.mpr (by linarith : 0<u/480)))

private lemma bring {r : ℕ} (h : 120 ≤ r) {u : ℝ} (he : 0≤u) :
    rate (-u) (r/60) ≤ rate (-(u/480)) r^2 * rate (-(u/240)) r := by
  unfold rate; rw [sq,← Real.exp_add,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh : (r:ℝ) ≤ 120 * ((r/60:ℕ):ℝ) := by exact_mod_cast (show r ≤ 120*(r/60) by omega)
  nlinarith only [mul_le_mul_of_nonneg_left hh he]

private lemma burned (J : Patch) (u : ℝ) (hu:0<u) : ∀ᶠ x : ℝ in atTop, ∀ β∈ Set.Icc (Scales.y G J.L x/2) (2*Scales.y G J.L x),
    (coupling β)⁻¹*rate (-(u/240)) (radiusB x) ≤ 2 := by
  let y x:= Scales.y G J.L x
  filter_upwards [tail_delay G J.L (u/240) (by linarith), (Scales.year G J.L).eventually_ge_atTop 1] with x hx hL
  intro β hβ
  have hz : Real.exp (-(u/240)*(till x:ℝ)) ≤ (y x)⁻¹ := hx
  apply le_trans (b:=Real.sqrt β*(y x)⁻¹)
  · rw [coupling,inv_inv]; refine mul_le_mul_of_nonneg_left (le_trans ?_ hz) (Real.sqrt_nonneg _)
    unfold rate; apply Real.exp_le_exp.mpr; apply mul_le_mul_of_nonpos_left _ (by linarith)
    exact Nat.cast_le.mpr (Nat.div_le_self ..)
  have hl : 0< y x := by change 1≤y x at hL; linarith
  rw [← div_eq_mul_inv,div_le_iff₀ hl]
  have hh := hβ.2
  change β≤2*y x at hh; change 1≤y x at hL
  refine Real.sqrt_le_iff.mpr ⟨mul_nonneg (by norm_num) hl.le,?_⟩
  nlinarith only [hh,hL]

lemma eta_rays (G : Gauge) (J : Patch) (P : Teller G) (v u a M : ℝ) (hv:0<v) (hu:0<u) (hM:0<M) :
    ∃ H : ℝ, 0<H ∧ ∀ᶠ x : ℝ in atTop, ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=J →
    100*(1+radiusB x) ≤ c.val → P.Funds S T → ∀ β∈ Set.Icc (Scales.y G J.L x/2) (2*Scales.y G J.L x),
    ∀ (A : Stores S) (F : Forest S.ratio) (k:S.Choices) (V:Config G c) (q:Chi) (d : ℝ), A.flags=RG.flags (temp x) V →
      0<d → d≤1 → Specs x v u a M T A F k V →
        ∀ (Y : LinkArray G (Frozen A x F)) (i), |plume S T A F k V q x d (coupling β) Y i| ≤ H*ray u x^2 := by
  by_cases h : J.Branches P.bind G
  swap
  · exact ⟨1,zero_lt_one,Eventually.of_forall (fun x c f S T hS hs hT=> (h (hS ▸ hT.kernel)).elim)⟩ -- implicit
  obtain ⟨D,hD,H⟩:=root_pay G J P h
  refine ⟨1+2*M^2*D,by positivity,?_⟩
  filter_upwards [H,(Scales.year G J.L).eventually_gt_atTop 0, burned (G:=G) J u hu, Work.E01.radiusB_tendsto.eventually_ge_atTop 120] with x hx h0 hc hR
  intro c f S T hS hI hT β hβ A F k V q d hV hd ht h' Y i
  have he := hx S T hS hI hT F A k V hV q d hd ht Y
  have hp : 0<coupling β := coupling_pos ((half_pos h0).trans_le hβ.1)
  apply (eta_price S T A F k V q x d (coupling β) Y hv.le hp hM.le hD h' he i).trans
  apply le_trans (mul_le_mul_of_nonneg_left (bring hR hu.le) (show 0 ≤ (coupling β)⁻¹*M^2*D by positivity))
  let X:=rate (-(u/240)) (radiusB x)
  change _*(ray u x^2 * X) ≤ _
  calc
    _ = M^2*D*((coupling β)⁻¹*X)*ray u x^2 := by ring
    _ ≤ M^2*D*2*ray u x^2 := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hc β hβ) (by positivity)) (sq_nonneg _)
    _ ≤ _ := by gcongr; linarith

-- finite exponents, holding actual flag bits
abbrev Pick (I : Type) := I ⊕ (I × I)

def bottom (u : Prices G I) (A : Gaussian.Table (I × G.ColorIndex)) (z : Prices G I) (i : Pick I) := i.elim
  (fun x=> ∑ l:G.ColorIndex,u (x,l)*z (x,l)) (fun i=>shade A i z)

def legs (i : Pick I) := i.elim (fun x=>(x,x)) id

def soaked {c f : Side} (S : StepData c f) (T : Tube G S) (A : Stores S) (F : Forest S.ratio)
    (k:S.Choices) (V:Config G c) (q:Chi) (x d g:ℝ) (i:Pick (Active A x F)) (y : GaussArgs (G:=G) A x F) :=
  bottom (plume S T A F k V q x d g y.1) ( (fog A F T x V k)⁻¹ - Rows.gram T x V k (shots S x) A F) y.2 i

@[fun_prop] lemma measurable_soaked {c f : Side} (S : StepData c f) (T : Tube G S) (A : Stores S) (F : Forest S.ratio)
    (k:S.Choices) (V:Config G c) (q:Chi) (x d g:ℝ) (i : Pick (Active A x F)) {P : Teller G} (h : P.Funds S T)
    (hd : 0<d) (hi : 2*d<firstRadius G) : Measurable (soaked S T A F k V q x d g i) := by
  cases i <;> unfold soaked bottom <;> simp only [Sum.elim_inr, Sum.elim_inl] <;> fun_prop (disch:=assumption)



private lemma brush (u : Prices G I) {D : ℝ} (hu : ∀ i, |u i| ≤ D) (i : I) (z : Prices G I) :
    |∑ j:G.ColorIndex, u (i,j)*z (i,j)| ≤ (Fintype.card G.ColorIndex:ℝ) * (D*mast legs (Sum.inl i) z) := by
  apply (Finset.abs_sum_le_sum_abs ..).trans
  have ht : 0 ≤ mast legs (Sum.inl i) z := zero_le_one.trans (mast_one ..)
  calc
    _ ≤ ∑ j:G.ColorIndex,D*mast legs (Sum.inl i) z := Finset.sum_le_sum fun j _=> by
      rw [abs_mul]; apply (mul_le_mul (hu _) ?_ (abs_nonneg _) ((abs_nonneg _).trans (hu (i,j))))
      have hr : |z (i,j)|^2 ≤ load z i := by
        unfold load; rw [EuclideanSpace.real_norm_sq_eq,sq_abs]
        exact Finset.single_le_sum (f:=fun k:G.ColorIndex=>z (i,k)^2) (fun k _=>sq_nonneg _) (Finset.mem_univ j)
      change _ ≤ 1+load z i+load z i
      nlinarith only [sq_nonneg (|z (i,j)|-1),hr,load_nonneg z i]
    _ = _ := by simp

def fares {c f : Side} (S : StepData c f) (G : Gauge) (A : Stores S) (F : Forest S.ratio) (x v u a M D : ℝ)
    (i : Pick (Active A x F)) : ℝ := i.elim
  (fun _=> D*ray u x) (salt S A F x G a v M)

private lemma solo {c f : Side} (S : StepData c f) (J : Patch) (h : S.patch=J) (F : Forest S.ratio)
    (x : ℝ) (A : Stores S) (v u a M D L : ℝ)
    (E : Finset (Pick (Active A x F))) (j : Active A x F)
    (hM : 0 < M) (hD : 0 ≤ D) (hL : 0<L)
    (h0 : 8*(D*ray u x) ≤ pinch L/2)
    (hw : Arc.hits id (Finset.univ : Finset (Active A x F × Active A x F)) (fun i=>8*salt S A F x G a v M i) j ≤ pinch L/2) :
    Arc.hits legs E (fun i=>8*fares S G A F x v u a M D i) j ≤ pinch L := by
  let I:= Active A x F
  let t:= fares S G A F x v u a M D
  have hp (i:Pick I) : 0≤t i := by cases i <;> unfold t fares <;> first | exact mul_nonneg hD (ray_pos ..).le | exact salt_nn _ _ _ _ _ _ _ _ hM.le _
  unfold Arc.hits; apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E) (f:=fun i=>if Arc.meets legs i j then 8*t i else 0) fun i _ _=>by
    split; exact mul_nonneg (by norm_num) (hp i); rfl)
  rw [Fintype.sum_sum_type]; unfold t fares legs meets; simp only [Sum.elim_inl,Sum.elim_inr,id_eq,or_self]
  unfold Arc.hits meets at hw; simp only [id_eq] at hw; simp only [Finset.sum_ite_eq',Finset.mem_univ, ↓reduceIte]; linarith

structure Cradled {c f : Side} (S : StepData c f) (T : Tube G S) (A : Stores S) (F : Forest S.ratio)
    (k:S.Choices) (V:Config G c) (q:Chi) (x r u a M D g d L:ℝ) (Y:Finset (Pick (Active A x F))) : Prop where
  bounded :
    let f:=fares S G A F x r u a M D
    (∀ i∈Y, 0≤f i ∧ f i≤1) ∧ (∀ j, Arc.hits legs Y (fun i=>4*(2*f i)) j ≤ pinch L)
  glaze : ∀ i∈Y, Measurable (soaked S T A F k V q x d g i)
  signed : ∀ i∈Y, ∀ y,|soaked S T A F k V q x d g i y| ≤ (fares S G A F x r u a M D i)^2*mast legs i y.2

/-- Uniform signed exponent receipts for *this pre-expansion address
convention*. These are proven on the genuine law, including the actual
blame term, as used in every portfolio and sector invocation on correct flags,
even when z visits a rare domain. Does not require price after L for other
branch/world calls, nor assert small *L¹* on whole exponential (these
are MAYer intake receipts with product constants). -/
lemma oasis {G : Gauge} (J : Patch) (P : Teller G) (h : J.Branches P.bind G) :
    ∃ r u a M D, 0 < r ∧ 0 < u ∧ 0 < a ∧ 0 < M ∧ 0 < D ∧ ∀ L : ℝ, 0<L → ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=J →
      100*(1+radiusB x) ≤ c.val → P.Funds S T →
      ∀ β∈ Set.Icc (Scales.y G J.L x/2) (2*Scales.y G J.L x),
      ∀ (A : Stores S) (F : Forest S.ratio) (k:S.Choices) (V:Config G c) (q:Chi) (d : ℝ), A.flags=RG.flags (temp x) V →
      0<d → d≤1 → 2*d<firstRadius G → ∀ Y,Cradled S T A F k V q x r u a M D (coupling β) d L Y := by
  obtain ⟨r,u,a,M,hr,hu,ha,hM,H⟩ := holds G J P h
  obtain ⟨H0,hH,H'⟩:=eta_rays G J P r u a M hr hu hM
  let D := 1 + (Fintype.card G.ColorIndex : ℝ)*H0
  have hD : 0<D := by unfold D; positivity
  refine ⟨r,u,a,M,D,hr,hu,ha,hM,hD,fun L hL=>?_⟩
  have hp : Tendsto (fun x=>D*ray u x) atTop (𝓝 0) := by simpa using (ray_goes hu).const_mul D
  filter_upwards [H,H', charges (G:=G) J r a M 8 hM (by norm_num) (half_pos (pinch_pos hL)) hr ha,
    hp.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1)),(hp.const_mul 8).eventually (ge_mem_nhds (by rw [mul_zero]; exact half_pos (pinch_pos hL)))] with x hx ht hw he hf
  intro c f S T hS hI hT β hβ A F k V q d hV hd h0 h1 Y
  obtain ⟨hR,hc⟩:= hw S hS A F
  have h:= hx S T hS hI hT A F k V hV
  have hl:= ht S T hS hI hT β hβ A F k V q d hV hd h0 h
  refine ⟨⟨fun i hi=>?_,fun j=>?_⟩, (fun i _=> measurable_soaked _ _ _ _ _ _ _ _ _ _ _ hT hd h1),fun i hi y=>?_⟩
  · cases i <;> unfold fares <;> simp only [Sum.elim_inl,Sum.elim_inr]
    · exact ⟨mul_nonneg hD.le (ray_pos ..).le,he⟩
    exact ⟨salt_nn _ _ _ _ _ _ _ _ hM.le _,hR _⟩
  · simp_rw [← mul_assoc (4:ℝ), show (4:ℝ)*2=8 by norm_num]; exact solo S J hS F x A r u a M D L Y j hM hD.le hL hf (hc _ j)
  cases i with
  | inr i => exact greet S A F k V hM.le h i y.2
  | inl i =>
    apply (brush _ (hl y.1) i y.2).trans
    unfold fares; simp only [Sum.elim_inl]; rw [mul_pow]
    have hd : (Fintype.card G.ColorIndex:ℝ) * H0 ≤ D^2 := by
      unfold D; have hz : 0 ≤ (Fintype.card G.ColorIndex:ℝ)*H0 := by positivity
      nlinarith
    rw [← mul_assoc,← mul_assoc]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd (sq_nonneg _)) (zero_le_one.trans (mast_one ..))
end YM.AnalyticBridge.AnnulusRatioInsertions.Prism.Breeze
