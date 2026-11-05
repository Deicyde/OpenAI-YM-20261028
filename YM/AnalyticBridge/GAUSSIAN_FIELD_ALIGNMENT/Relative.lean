import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Windows
import YM.Next.FREE_KERNELS.Lifts
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.ResidualPrice


set_option warningAsError false

/-!
# Quantitative price for changing a Gaussian window law

Supply same-Gram and/or two known Grams at possibly different windows. Pay
for both nonsymmetric ordered inverses (also the ones which supply the mean
shift), then the ACTUAL symmetric covariances. Keep determinant ratio and
force difference; there is no Jacobian outside the finite counting metric in
this comparison. For different precisions the cost includes their weighted
difference (need not be small). No derivative assertion. Applies even on
empty lists. Use on positive branches only, after delay for symmetrized
matrices, not as a formal density quotient if a window failed its checks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.GaussianFieldAlignment.Relative
open Function Filter Set Matrix MeasureTheory Lattice
open Next.SectorChange Next.SectorChange.Gaussian Next.SectorChange.Schur
open FreeResolvent (native normSum_nn resolve safeRate)
open scoped Topology BigOperators Classical ENNReal

variable {α : Type} [Fintype α] [DecidableEq α] {c : Side} {p : α → Site c} {σ M η δ : ℝ}

local notation "Mat" α => Gaussian.Table α
variable {A D : Mat α}

omit [DecidableEq α] in
lemma of_pours (h : Pours A p p σ M) : (native c).Schur p p σ M A := by
  refine ⟨⟨h.row⟩,⟨fun j => ?_⟩⟩
  simpa only [native, FreeResolvent.Cost.weight, transpose_apply,separation_comm (p j)] using! h.col j

omit [DecidableEq α] in
lemma to_pours (h : (native c).Schur p p σ M A) (hm : 0 ≤ M) : Pours A p p σ M := by
  refine ⟨hm,h.rows.bound,fun j => ?_⟩
  simpa only [native,FreeResolvent.Cost.weight,transpose_apply,separation_comm (p j)] using! h.cols.bound j

omit [DecidableEq α] in
lemma gap_iff : Gapped A η ↔ FreeResolvent.Gap A η := by simp only [Gapped,sumSq_dot]; exact ⟨(⟨·⟩), (·.lower)⟩

lemma view_near {W : α → Set α} {r : ℕ} (h : Bars W p r) : (view W (per_self h)).Near (native c) p r := by
  intro i j he
  have hx : ¬ separation (p i) (p j) ≤ r := fun ht => he ⟨⟨j,h i j ht⟩,rfl⟩
  change _ ≤ ((separation (p i) (p j)):ℝ)
  exact_mod_cast (Nat.le_of_lt (lt_of_not_ge hx))

def symPart (A : Mat α) : Mat α := (1/2:ℝ) • (A + A.transpose)

omit [Fintype α] [DecidableEq α] in
lemma sym_of_sub : symPart (A-D) = symPart A-symPart D := by unfold symPart; rw [transpose_sub]; module

omit [DecidableEq α] in
lemma sym_pours (h : Pours A p p σ M) : Pours (symPart A) p p σ M :=
  ((h.bind h.turn).scale _).weaker le_rfl (le_of_eq (by rw [abs_of_pos (by norm_num)]; ring))

structure Supported (A : Mat α) (W : α → Set α) (p : α → Site c) (r s M : ℝ) : Prop where
  source_pos : A.PosDef
  pos : (symPart (per W A)).PosDef
  prec : Pours A p p s M
  exactInv : Pours A⁻¹ p p s M
  order : Pours (per W A) p p s M
  tail : Pours (per W A-A⁻¹) p p s (M*Real.exp (-s*r))
  charges : Pours ((symPart (per W A))⁻¹) p p s M

/-- Consequence of the two accepted window estimates, now uniform also on
*differences at positive rate* and including costs of symmetric inverses. -/
theorem same_purchase (hσ : 0 < σ) (hM : 0 ≤ M) (he : 0 < η) (B : ℝ → ℝ) (hB : ∀ s, 0 ≤ B s) :
    ∃ s K : ℝ, 0 < s ∧ s ≤ σ ∧ 0 < K ∧ ∀ᶠ r : ℕ in atTop,
      ∀ {α : Type} [Fintype α] [DecidableEq α] {c : Side} (A : Mat α) (p : α → Site c) (W : α → Set α),
        Revenue p B → Pours A p p σ M → A.IsSymm → Gapped A η → Bars W p r → Supported A W p r s K := by
  obtain ⟨_,_,g,_,_,hg,hw⟩ := windows hσ he hM B hB
  let t := safeRate σ M η
  have ht : 0 < t := FreeResolvent.rate_pos hσ hM he
  have hv : t < σ := FreeResolvent.rate_lt hσ
  let v := t/2
  let D := B (t-v) * (η/2)⁻¹
  have hy : 0<v := half_pos ht
  have hd : 0≤D := mul_nonneg (hB _) (by positivity)
  let s := min (v/2) (safeRate v D g/2)
  have hh := FreeResolvent.rate_pos hy hd hg
  have hs : 0 < s := lt_min (half_pos hy) (half_pos hh)
  have hu : s ≤ v/2 := min_le_left ..
  have hz : s ≤ v := hu.trans (half_le_self hy.le)
  let k := B (safeRate v D g-s)*(g/2)⁻¹
  have hk : 0 ≤ k := mul_nonneg (hB _) (by positivity)
  let K := 1+M+D+(D*M*D)+k
  refine ⟨s,K,hs,by linarith [show v=t/2 from rfl],by unfold K; positivity,?_⟩
  filter_upwards [hw] with r hr
  intro α _ _ c A p W hp hA hx hq hW
  let P := per W A
  have h := of_pours hA; have hG := gap_iff.mp hq
  have HB (a : ℝ) (ha : 0 < a) : (native c).Volume p a (B a) := ⟨hp _ ha⟩
  have HB' := HB (safeRate σ M η-v) (by change 0<t-v; unfold v; linarith)
  have hP : Pours P p p v D := to_pours (by
    have hL := (view W (per_self hW)).prices (show 0 ≤ (0:ℝ) by rfl) he hσ hM h hG HB'
    rw [per_view,add_zero] at hL; exact hL) hd
  have hI : Pours A⁻¹ p p v D := to_pours (by simpa only [add_zero,resolve,zero_smul] using!
      (FreeResolvent.resolve_schur hM hσ h hG he (show 0 ≤ (0:ℝ) by rfl) HB')) hd
  have hE := to_pours (FreeResolvent.Window.Survey.difference (view_near hW) (show 0 ≤ (0:ℝ) by rfl) he hσ hM hs.le hz (show v ≤ σ by linarith [show v=t/2 from rfl]) (hB _) h hG HB') (by have := hB (t-v); change 0 ≤ (B (t-v)*_)*(Real.exp _*(M*(B (t-v)*_))); positivity)
  rw [per_view,resolve,zero_smul,add_zero,add_zero] at hE
  have h₀ := (hr p A W hp hA hx hq hW).2
  have hn : 0 < safeRate v D g - s := by have hi : s ≤ safeRate v D g/2 := min_le_right ..; linarith
  have ha := to_pours (FreeResolvent.resolve_schur hd hy (of_pours (sym_pours hP)) (gap_iff.mp h₀.1) hg (show 0 ≤ (0:ℝ) by rfl) (HB _ hn))
  rw [resolve,zero_smul,add_zero,add_zero] at ha
  have h1 : D ≤ K := by unfold K; nlinarith [mul_nonneg (mul_nonneg hd hM) hd]
  have h2 : k ≤ K := by unfold K; nlinarith [mul_nonneg (mul_nonneg hd hM) hd]
  have h3 : M ≤ K := by unfold K; nlinarith [mul_nonneg (mul_nonneg hd hM) hd]
  refine ⟨dissolves hq hx he,h₀.2,hA.weaker (hz.trans (show v ≤ σ by unfold v; linarith)) h3,hI.weaker hz h1,hP.weaker hz h1,hE.weaker le_rfl ?_,(ha hk).weaker le_rfl h2⟩
  change D*(Real.exp _ *(M*D)) ≤ _
  rw [show D*(Real.exp (-(v-s)*r)*(M*D))=D*M*D*Real.exp (-(v-s)*r) by ring]
  have hi : D*M*D ≤ K := by unfold K; linarith
  gcongr
  linarith only [hu]

section Log

lemma log_upper (A : Mat α) (h : 0 < det A) (hδ : 0 ≤ δ) (he : ResidualPrice.flared (1+δ) A) :
    Real.log (det A) ≤ Fintype.card α * δ := calc
  _ ≤ Real.log ((1+δ)^Fintype.card α) := Real.log_le_log h ((le_abs_self _).trans (ResidualPrice.det_pay he))
  _ ≤ _ := by rw [Real.log_pow]; gcongr; linarith [Real.log_le_sub_one_of_pos (by positivity : 0<1+δ)]

lemma log_one (h : 0 < det A) (he : Pours (A-1) p p σ δ) (hσ : 0 ≤ σ) : Real.log (det A) ≤ Fintype.card α * δ := by
  apply log_upper _ h he.pos
  intro j
  have hx := of_pours (he.weaker hσ le_rfl)
  have hp := hx.cols.bound j
  calc
    _ = ∑ i, |(1:Mat α) i j + (A-1) i j| := by simp
    _ ≤ (∑ i, |(1:Mat α) i j|) + ∑ i, |(A-1) i j| := by rw [← Finset.sum_add_distrib]; exact Finset.sum_le_sum fun i _ => abs_add_le ..
    _ ≤ _ := by simpa [Matrix.one_apply, apply_ite abs] using hp

lemma det_ratio (hA : A.PosDef) (hD : D.PosDef) (ha : Pours A⁻¹ p p σ M) (hd : Pours D⁻¹ p p σ M)
    (he : Pours (A-D) p p σ δ) (hs : 0 ≤ σ) : |Real.log (det A) - Real.log (det D)| ≤ Fintype.card α * (δ*M) := by
  have H {A D : Mat α} (h : A.PosDef) (h' : D.PosDef) (he : Pours (A-D) p p σ δ) (hd : Pours D⁻¹ p p σ M) :
      Real.log (det A)-Real.log (det D) ≤ Fintype.card α*(δ*M) := by
    have hu := he.fuse hd hs
    rw [Matrix.sub_mul, Matrix.mul_nonsing_inv _ (IsUnit.mk0 _ h'.det_pos.ne')] at hu
    have hl := log_one (show 0 < det (A*D⁻¹) by rw [det_mul,det_nonsing_inv,Ring.inverse_eq_inv]; have := h.det_pos; have := h'.det_pos; positivity) hu hs
    rw [det_mul,det_nonsing_inv,Ring.inverse_eq_inv,Real.log_mul h.det_pos.ne' (inv_ne_zero h'.det_pos.ne'),Real.log_inv] at hl
    exact hl
  have hh : Pours (D-A) p p σ δ := to_pours (by rw [← neg_sub]; exact (of_pours he).neg) he.pos
  exact abs_le.mpr ⟨by linarith only [H hD hA hh ha],H hA hD he hd⟩
end Log

/-- Data at fixed centers. Keep the ordered and symmetric errors separate;
log term doesn't include its factor 1/2 yet. -/
structure Difference (U V : Mat α) (p : α → Site c) (s δ : ℝ) : Prop where
  left_pos : (symPart U).PosDef
  right_pos : (symPart V).PosDef
  ordered : Pours (U-V) p p s δ
  force : Pours ((symPart U)⁻¹ - (symPart V)⁻¹) p p s δ
  logs : |Real.log (det (symPart U)) - Real.log (det (symPart V))| ≤ Fintype.card α * δ

def error (M s r δ : ℝ) := ((M+1)^2) * (2*M*Real.exp (-s*r)+M*δ*M)

theorem compare {W W' : α → Set α} {r : ℝ} (hA : Supported A W p r σ M) (hD : Supported D W' p r σ M)
    (he : Pours (A-D) p p σ δ) (hs : 0 ≤ σ) : Difference (per W A) (per W' D) p σ (error M σ r δ) := by
  let U := per W A; let V := per W' D
  let E := 2*M*Real.exp (-σ*r)+M*δ*M
  have hM := hA.prec.pos; have hδ := he.pos
  have hE : 0 ≤ E := by unfold E; positivity
  have h₁ : ∀ {A B : Mat α} {e : ℝ}, A.PosDef → B.PosDef → Pours A⁻¹ p p σ M → Pours B⁻¹ p p σ M →
      Pours (A-B) p p σ e → Pours (A⁻¹-B⁻¹) p p σ (M*e*M) := by
    intro A B e ha hb hp hq he
    have hf := FreeResolvent.resolve_diff (A:=A) (B:=B) (u:=0) (by simp [ha.det_pos.ne']) (by simp [hb.det_pos.ne'])
    simp only [resolve,zero_smul,add_zero] at hf
    rw [← neg_sub,hf]; simpa using (((hq.fuse he hs).fuse hp hs).scale (-1))
  have hu : Pours (U-V) p p σ E := by
    rw [show U-V=U-A⁻¹+(A⁻¹-D⁻¹) + -(V-D⁻¹) by abel]
    have hx := (hA.tail.bind (h₁ hA.source_pos hD.source_pos hA.exactInv hD.exactInv he)).bind (hD.tail.scale (-1:ℝ))
    simp only [neg_one_smul] at hx; exact hx.weaker le_rfl (le_of_eq (by unfold E; rw [abs_neg,abs_one]; ring))
  have hw : Pours (symPart U-symPart V) p p σ E := sym_of_sub (A:=U) (D:=V) ▸ sym_pours hu
  have hv := h₁ hA.pos hD.pos hA.charges hD.charges hw
  have hl := det_ratio hA.pos hD.pos hA.charges hD.charges hw hs
  have hp : E ≤ error M σ r δ := le_mul_of_one_le_left hE (by nlinarith)
  refine ⟨hA.pos,hD.pos,hu.weaker le_rfl hp,hv.weaker le_rfl ?_,hl.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))⟩
  · calc
      _ = M^2*E := by ring
      _ ≤ (M+1)^2*E := by gcongr; linarith
  calc
    E*M = M*E := mul_comm ..
    _ ≤ (M+1)^2*E := mul_le_mul_of_nonneg_right (by nlinarith) hE



/-- Density of the centered covariance A with respect to D, in the latter
coordinates z, with an optional translation h (e.g. `(μ_D - μ_A)/g`). -/
def trade (A D : Mat α) (h z : Vec α) : ℝ :=
    Real.sqrt D.det / Real.sqrt A.det * Real.exp ((Gaussian.force D z-Gaussian.force A (h+z))/2)

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma change (hA : A.PosDef) (hD : D.PosDef) (h : Vec α) (f : Vec α → X) :
    (Integrable f (cloud A) ↔ Integrable (fun z => trade A D h z • f (h+z)) (cloud D)) ∧
      (∫ z, f z ∂cloud A) = ∫ z, trade A D h z • f (h+z) ∂cloud D := by
  let u (A : Mat α) (f : Vec α → X) (z : Vec α) := ratio A z • f z
  have H {A : Mat α} (ha : A.PosDef) (f : Vec α → X) : (Integrable f (cloud A) ↔ Integrable (u A f)) ∧
      (∫ z,f z ∂cloud A) = ∫ z, u A f z := by
    rw [cloud_formula ha,integrable_withDensity_iff_integrable_smul' (measurable_ratio A |>.ennreal_ofReal)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), integral_withDensity_eq_integral_toReal_smul
      (measurable_ratio A |>.ennreal_ofReal) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp_rw [ENNReal.toReal_ofReal (ratio_pos ha _).le]; exact ⟨Iff.rfl,rfl⟩
  rw [(H hA f).1,(H hA f).2,(H hD _).1,(H hD _).2]
  let e := MeasurableEquiv.addLeft h
  have he : MeasurePreserving e volume volume := measurePreserving_add_left ..
  have ht : u D (fun z => trade A D h z • f (h+z)) = u A f ∘ e := by
    funext z
    unfold u; rw [smul_smul]; change _ = ratio A (h+z) • f (h+z)
    congr 1
    unfold ratio trade coat
    have h₁ : 0 < dome α := dome_pos
    have h₂ := Real.sqrt_pos.mpr hD.det_pos; have h₃ := Real.sqrt_pos.mpr hA.det_pos
    have hi : (-Gaussian.force A (h+z))/2=(-Gaussian.force D z)/2 + (Gaussian.force D z-Gaussian.force A (h+z))/2 := by ring
    rw [hi,Real.exp_add]; field_simp
  rw [ht]; exact ⟨(he.integrable_comp_emb e.measurableEmbedding).symm,(he.integral_comp' _).symm⟩

lemma Difference.change {U V : Mat α} (H : Difference U V p σ δ) (h : Vec α) (f : Vec α → X) :
    let A := symPart U; let B := symPart V
    (Integrable f (cloud A) ↔ Integrable (fun z => trade A B h z • f (h+z)) (cloud B)) ∧
      (∫ z,f z ∂cloud A) = ∫ z, trade A B h z • f (h+z) ∂cloud B := Relative.change H.left_pos H.right_pos h f

lemma Difference.price {U V : Mat α} (H : Difference U V p σ δ) (hs : 0 ≤ σ) (z : Vec α) :
    |Real.log (trade (symPart U) (symPart V) 0 z)| ≤ (Fintype.card α + sumSq z)*(δ/2) := by
  let A := symPart U; let B := symPart V
  have ha := H.left_pos.det_pos; have hb := H.right_pos.det_pos
  rw [trade,zero_add, Real.log_mul (div_pos (Real.sqrt_pos.mpr hb) (Real.sqrt_pos.mpr ha)).ne' (Real.exp_pos _).ne',Real.log_exp,Real.log_div (Real.sqrt_pos.mpr hb).ne' (Real.sqrt_pos.mpr ha).ne',Real.log_sqrt ha.le,Real.log_sqrt hb.le]
  change |Real.log B.det /2 - Real.log A.det/2 + _| ≤ _
  have ht : |Gaussian.force B z - Gaussian.force A z| ≤ δ * sumSq z := by
    have hL := estimate (H.force.weaker hs le_rfl) z z
    rw [Matrix.sub_mulVec,dotProduct_sub] at hL; rw [abs_sub_comm]; unfold Gaussian.force
    linarith
  have hi := H.logs
  rw [abs_sub_comm] at hi
  apply (abs_add_le ..).trans; rw [← sub_div,abs_div,abs_div,abs_of_pos (zero_lt_two (α:=ℝ))]
  linarith

/-- Optional cost of the shift as `d*u` in the *normalized* z variables (so may
include an inverse coupling!). Kept separate because no small shift of actual
origins follows just by identifying linear covariance data. -/
lemma Difference.priceShift {U V : Mat α} (H : Difference U V p σ δ) (ha : Pours (symPart U)⁻¹ p p σ M)
    (hs : 0 ≤ σ) (d : ℝ) (u z : Vec α) :
    |Real.log (trade (symPart U) (symPart V) (d • u) z)| ≤ (Fintype.card α + sumSq z)*(δ/2) +
      (d^2*M*sumSq u + |d| *M*(sumSq u + sumSq z))/2 := by
  let A := symPart U; let B := symPart V
  have he := estimate (ha.weaker hs le_rfl)
  let suff := d^2*M*sumSq u + |d| *M*(sumSq u + sumSq z)
  have hf : |Gaussian.force A (d • u+z) - Gaussian.force A z| ≤ suff := by
    let q (v w : Vec α) := v ⬝ᵥ (A⁻¹ *ᵥ w)
    have hu : Gaussian.force A (d • u+z) - Gaussian.force A z = d^2*q u u + d*q z u + d*q u z := by
      unfold Gaussian.force q; rw [mulVec_add,add_dotProduct,dotProduct_add,dotProduct_add,mulVec_smul,smul_dotProduct,smul_dotProduct,dotProduct_smul,dotProduct_smul]; simp only [smul_eq_mul]; ring
    have ht v w : |q v w| ≤ _ := he v w
    rw [hu]; apply (abs_add_le ..).trans ((add_le_add_left (abs_add_le ..) _).trans ?_)
    rw [abs_mul,abs_mul,abs_mul,abs_of_nonneg (sq_nonneg _)]
    unfold suff; linarith only [mul_le_mul_of_nonneg_left (ht u u) (sq_nonneg d),mul_le_mul_of_nonneg_left (ht z u) (abs_nonneg d),mul_le_mul_of_nonneg_left (ht u z) (abs_nonneg d)]
  have hi := H.price hs z
  simp only [trade,zero_add] at hi ⊢
  have hτ := (div_pos (Real.sqrt_pos.mpr H.right_pos.det_pos) (Real.sqrt_pos.mpr H.left_pos.det_pos)).ne'
  rw [Real.log_mul hτ (Real.exp_pos _).ne',Real.log_exp] at hi ⊢
  rw [abs_le] at hi hf ⊢
  change -suff ≤ Gaussian.force (symPart U) _ - _ ∧ _ ≤ suff at hf
  constructor <;> unfold suff at hf <;> linarith

omit [DecidableEq α] in
/-- Sup-cost for nonsymmetric mean operators and changes of ordered mean. Caller
supplies actual source(s); nothing small about wrong-branch linear terms is
assumed. -/
lemma source (hs : 0 ≤ σ) (ha : Pours A p p σ M) (b : Vec α) : ‖-A.transpose *ᵥ b‖ ≤ M*‖b‖ := by
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg ha.pos (norm_nonneg b))]; intro i
  have hi := (of_pours ha).mono hs le_rfl |>.cols.bound i
  rw [Real.norm_eq_abs]
  change |∑ j, -A j i * b j| ≤ _
  calc
    _ ≤ ∑ j, |-(A j i) * b j| := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ j, |A j i| * ‖b‖ := Finset.sum_le_sum fun j _ => by rw [abs_mul,abs_neg]; exact mul_le_mul_of_nonneg_left (norm_le_pi_norm b j) (abs_nonneg _)
    _ ≤ M*‖b‖ := by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (by simpa using hi) (norm_nonneg _)

omit [DecidableEq α] in
lemma source_difference {b e : Vec α} (hs : 0 ≤ σ) (hD : Pours D p p σ M) (he : Pours (A-D) p p σ δ) :
    ‖(-A.transpose *ᵥ b) - (-D.transpose *ᵥ e)‖ ≤ δ*‖b‖ + M*‖b-e‖ := by
  have hi := add_le_add (source hs he b) (source hs hD (b-e))
  apply le_trans _ hi; refine le_trans (le_of_eq (congr_arg Norm.norm ?_)) (norm_add_le ..)
  rw [Matrix.transpose_sub,neg_sub,Matrix.sub_mulVec, Matrix.mulVec_sub]; simp_rw [Matrix.neg_mulVec]; abel

end YM.AnalyticBridge.GaussianFieldAlignment.Relative
