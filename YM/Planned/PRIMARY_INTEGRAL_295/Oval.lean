import YM.Planned.PRIMARY_INTEGRAL_295.Tones

/-!
# Chain rule cost through order k on normalized primary comparisons

Actual affine/log-link contact map on one marginal of centered output,
including k=0. Inputs measured by moment error `e` (nonnegative, absolute
bounds on every actual motion); predict all b-orders separately by
polynomial/affine rules. Score derivatives also spend their own moment
allowance later. Assumes only C^k real germs (r not needed beyond over T).
Doesn't commute integration. Deterministic math.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Oval
open Function Filter Set Metric Labels Tones
open scoped Topology ContDiff BigOperators

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {x : E} {f q : E → F} {h : F → G} {t : ℝ} {n l k : ℕ}

-- derivatives AT contact including value, PEANO order not radius uniform.
def Envelope (x : E) (k : ℕ) (q : E → F) (u : ℝ) : Prop :=
    0≤u ∧ ∀ b ≤ k, ‖iteratedFDeriv ℝ b q x‖ ≤ u

def Fuzz (x : E) (k : ℕ) (f q : E → F) (e : ℝ) : Prop :=
    0≤e ∧ ∀ b ≤ k, ‖iteratedFDeriv ℝ b f x - iteratedFDeriv ℝ b q x‖ ≤ e
lemma Envelope.value {u : ℝ} (h : Envelope x k q u) : ‖q x‖≤u := by simpa using h.2 0 (Nat.zero_le _)
lemma Fuzz.value {e : ℝ} (h : Fuzz x k f q e) : ‖f x-q x‖≤e := by
  classical
  let u := iteratedFDeriv ℝ 0 f x - iteratedFDeriv ℝ 0 q x
  have he := u.le_opNorm (fun _ => 0)
  apply le_trans _ (h.2 0 (Nat.zero_le _)); simpa [u] using he
lemma Fuzz.toward {e u : ℝ} (h : Fuzz x k f q e) (hc : Envelope x k q u) : Envelope x k f (u+e) := by
  refine ⟨add_nonneg hc.1 h.1,fun i hi=>?_⟩; rw [add_comm u];
  exact (norm_le_norm_sub_add _ (iteratedFDeriv ℝ i q x)).trans (add_le_add (h.2 i hi) (hc.2 i hi))

private lemma disc (H : Tensor.T E F n) (M : ℝ) (hM : 0≤M) (h : ∀ v : Fin n → E, (∀ i, ‖v i‖≤1) → ‖H v‖≤M) : ‖H‖≤M := by
  refine ContinuousMultilinearMap.opNorm_le_bound hM fun v=>?_;
  let w i := ‖v i‖⁻¹ • v i
  have he (i) : ‖w i‖≤1 := by
    by_cases he : v i=0
    · simp [w,he]
    simp [w,norm_smul,he]
  have hu : NormedDivisionRing ℝ := inferInstance
  let u (i : Fin n) := ‖v i‖
  have ht i : u i • w i=v i := by by_cases he:v i=0 <;> simp [u,w,he]
  have hh : H v=(∏ i, u i) • H w := by conv_lhs => rw [← funext ht]; exact H.map_smul_univ u w
  have hv : 0≤∏ i,u i := by unfold u; positivity
  rw [hh,norm_smul,Real.norm_of_nonneg hv,mul_comm]; exact mul_le_mul_of_nonneg_right (h _ he) hv

private lemma at_disc (H : Tensor.T E F n) (v : Fin n → E) (h : ∀ i, ‖v i‖≤1) : ‖H v‖≤‖H‖ := H.unit_le_opNorm
    ((pi_norm_le_iff_of_nonneg zero_le_one).mpr h)

-- precise *separate* Q and fq endpoint costs at each parameter tensor.
-- Account C(1+q+e)^(l+n)*(e) from any composition case.
section
variable {e u R C : ℝ} (ht : t∈Ioc 0 1) (hB : Width h (k+1) l R C)
include hB ht

private lemma size_one (hn : n≤k) (b : OrderedFinpartition n) (hp : Envelope x k q u)
    (hq : ‖t • q x‖≤R) (v : Fin n → E) (hv : ∀ i, ‖v i‖≤1) :
    ‖Cases.caseRead b (coat h l t) q x v‖ ≤ C*(1+u)^(l+n) := by
  classical
  let U:=1+u
  let Z:=iteratedFDeriv ℝ b.length (coat h l t) (q x)
  let y (i : Fin b.length):=iteratedFDeriv ℝ (b.partSize i) q x (v ∘ b.emb i)
  have hu:=hp.1; have hc := hB.1; have hx : 1≤U := by unfold U; linarith
  have hy i : ‖y i‖≤U := (at_disc (iteratedFDeriv ℝ (b.partSize i) q x) (v ∘ b.emb i) (fun i=> hv _)).trans
      ((hp.2 _ ((b.partSize_le i).trans hn)).trans (le_add_of_nonneg_left zero_le_one))
  have he : ‖Z‖ ≤ C*U^l := (hB.2 _ (b.length_le.trans (hn.trans k.le_succ)) t _ ht hq).trans (mul_le_mul_of_nonneg_left
       (pow_le_pow_left₀ (by positivity) (add_le_add_right hp.value _) l) hc)
  apply (Z.le_opNorm y).trans; apply (mul_le_mul he (Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun i _=> hy i)) (by positivity)
    (by positivity)).trans
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [pow_add,←mul_assoc]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx b.length_le) (by positivity)

private lemma sub_one (hh : ContDiff ℝ ω h) (hn : n≤k) (b : OrderedFinpartition n)
    (he : Fuzz x k f q e) (hu : Envelope x k q u) (hf : ‖t • f x‖≤R) (hq : ‖t • q x‖≤R)
    (v : Fin n → E) (hv : ∀ i, ‖v i‖ ≤ 1) :
    ‖Cases.caseRead b (coat h l t) f x v - Cases.caseRead b (coat h l t) q x v‖ ≤
        C*((n+1:ℕ):ℝ)*(1+(u+e))^(l+n)*e := by
  classical
  let r:=b.length; let U:=u+e; let p:=1+U
  let H z := iteratedFDeriv ℝ r (coat h l t) z
  let A (j : E→F) (i : Fin b.length) := iteratedFDeriv ℝ (b.partSize i) j x (v ∘ b.emb i)
  have hu' := hu.1; have hc := hB.1; have he':=he.1
  have hU : 0≤U := add_nonneg hu' he'; have hp : 1≤p := le_add_of_nonneg_right hU
  have hv' i : ‖A f i-A q i‖≤e := (at_disc (iteratedFDeriv ℝ _ f x - iteratedFDeriv ℝ _ q x) (v ∘ b.emb i)
    (fun i=>hv _)).trans (he.2 _ ((b.partSize_le i).trans hn))
  have hc' := he.toward hu
  have hw : Envelope x k q U := ⟨hU,fun i h => (hu.2 i h).trans (le_add_of_nonneg_right he')⟩
  have ht' (j:E→F) (hj:Envelope x k j U) (i:Fin b.length) : ‖A j i‖≤p := (at_disc _ (v ∘ b.emb i) (fun i=>hv _)).trans
    ((hj.2 _ ((b.partSize_le i).trans hn)).trans (le_add_of_nonneg_left zero_le_one))
  have hs j (hj : Envelope x k j U) : ‖A j‖≤p := (pi_norm_le_iff_of_nonneg (by positivity)).2 (ht' _ hj)
  let Z:=C*p^l; have hZ : 0≤Z:= by unfold Z; positivity
  have hx : ‖H (f x)‖ ≤ Z := (hB.2 _ (b.length_le.trans (hn.trans k.le_succ)) t _ ht hf).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (add_le_add_right hc'.value _) l) hc)
  have hL : ‖H (f x)-H (q x)‖≤Z*e := (Width.diff hh hB (lt_of_le_of_lt (b.length_le.trans hn) (by simp)) ht hc'.value hw.value hf hq).trans
    (mul_le_mul_of_nonneg_left he.value hZ)
  have hH : ‖(H (f x) - H (q x)) (A q)‖ ≤ Z*e*p^n := calc
    _ ≤ _ := (H (f x)-H (q x)).le_opNorm (A q)
    _ ≤ (Z*e)*∏ i : Fin r,p := mul_le_mul hL (Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun i _=> ht' _ hw i)) (by positivity) (by positivity)
    _ ≤ _ := by simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]; exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hp b.length_le) (by positivity)
  have ha : ‖H (f x) (A f)-H (f x) (A q)‖ ≤ Z*r*p^n*e := by
    apply ((H (f x)).norm_image_sub_le (A f) (A q)).trans
    rw [Fintype.card_fin]
    have hm : max ‖A f‖ ‖A q‖ ≤ p:= max_le (hs _ hc') (hs _ hw)
    have ht2 : ‖A f - A q‖ ≤ e := (pi_norm_le_iff_of_nonneg he').2 hv'
    apply mul_le_mul _ ht2 (norm_nonneg _) (by positivity); apply mul_le_mul
      (mul_le_mul_of_nonneg_right hx (by positivity)) _ (by positivity) (by positivity)
    exact (pow_le_pow_left₀ (by positivity) hm _).trans (pow_le_pow_right₀ hp ((Nat.sub_le ..).trans b.length_le))
  change ‖H (f x) (A f)- H (q x) (A q)‖ ≤ _
  apply ((norm_sub_le_norm_sub_add_norm_sub _ (H (f x) (A q)) _).trans (add_le_add ha hH)).trans
  have hx' : Z*r ≤ Z*n := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr b.length_le) hZ
  refine (add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hx' (show 0 ≤ p^n by positivity)) he')
     (Eq.le (rfl : Z*e*p^n = _))).trans_eq ?_
  unfold Z p U; push_cast; rw [pow_add]; ring

def allot (n l : ℕ) (u C : ℝ) := (Fintype.card (OrderedFinpartition n):ℝ)*C*(1+u)^(l+n)

lemma remit (hq' : ContDiffAt ℝ k q x) (hn : n≤k) (hu : Envelope x k q u) (hh : ContDiff ℝ ω h)
    (hq : ‖t • q x‖≤R) : ‖iteratedFDeriv ℝ n (coat h l t ∘ q) x‖ ≤ allot n l u C := by
  have hu':=hu.1; have hC:=hB.1
  apply disc _ _ (by unfold allot; positivity); intro v hv
  rw [Cases.compReads ((coat_smooth hh l t).contDiffAt.of_le le_top) hq' (Nat.cast_le.mpr hn)]
  refine (norm_sum_le ..).trans ((Finset.sum_le_sum (fun i _ => size_one ht hB hn i hu hq v hv)).trans_eq ?_)
  simp [allot,mul_assoc]

lemma due (hq' : ContDiffAt ℝ k q x) (hf' : ContDiffAt ℝ k f x) (hn : n≤k) (he : Fuzz x k f q e)
    (hu : Envelope x k q u) (hh : ContDiff ℝ ω h) (hq : ‖t • q x‖≤R) (hf : ‖t • f x‖≤R) :
    ‖iteratedFDeriv ℝ n (coat h l t ∘ f) x - iteratedFDeriv ℝ n (coat h l t ∘ q) x‖ ≤
        ((n+1:ℕ):ℝ)*allot n l (u+e) C*e := by
  have hu':=hu.1; have he':=he.1; have hC:=hB.1; have Hn := (show (n:WithTop ℕ∞)≤(k:WithTop ℕ∞) from Nat.cast_le.mpr hn)
  apply disc _ _ (by unfold allot; positivity); intro v hv
  have hc z : ContDiffAt ℝ k (coat h l t) z := (coat_smooth hh l t).contDiffAt.of_le le_top
  change ‖iteratedFDeriv ℝ n (coat h l t ∘ f) x v - iteratedFDeriv ℝ n (coat h l t ∘ q) x v‖ ≤ _
  classical
  rw [Cases.compReads (hc _) hf' Hn,Cases.compReads (hc _) hq' Hn, ← Finset.sum_sub_distrib];
  refine (norm_sum_le ..).trans ((Finset.sum_le_sum (fun i _=> sub_one ht hB hh hn i he hu hf hq v hv)).trans_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ,nsmul_eq_mul]; unfold allot; ring
end

def league (k l : ℕ) (u C : ℝ) := (k+1:ℕ)*∑ i∈Finset.range (k+1), allot i l u C
lemma prize {u C : ℝ} (hu : 0≤u) (hC : 0≤C) (k l : ℕ) : 0≤league k l u C := by
  unfold league; exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _=> by unfold allot; positivity))
private lemma allotBound {u e C : ℝ} (hu : 0≤u) (hC : 0≤C) (he : 0≤e) (hn : n≤k) (l : ℕ) :
    (n+1:ℕ)*allot n l (u+e) C ≤ league k l u C * (1+e)^(l+k) := by
  classical
  let M:=∑ i∈Finset.range (k+1),allot i l u C
  have hp (i) : 0 ≤ allot i l u C := by unfold allot; positivity
  have hM := show 0≤M from Finset.sum_nonneg fun i _=>hp i
  have hK := show allot n l u C ≤ M from Finset.single_le_sum (fun i _=>hp i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
  have he' : allot n l (u+e) C≤ allot n l u C*(1+e)^(l+k) := by
    unfold allot; rw [mul_assoc (_*C)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply (pow_le_pow_left₀ (by positivity) (show 1+(u+e) ≤ (1+u)*(1+e) by nlinarith) (l+n)).trans
    rw [mul_pow]; gcongr; linarith
  unfold league; rw [mul_assoc (Nat.cast _ : ℝ)]
  exact mul_le_mul (Nat.cast_le.mpr (Nat.add_le_add_right hn 1)) (he'.trans (mul_le_mul_of_nonneg_right hK (by positivity)))
    (by unfold allot; positivity) (by positivity)

/-- Pointwise normalized jets for genuine and predicted paths.
Uniform prices paid *without* dependence on e or t>0. -/
theorem sticker {e u C R : ℝ} (hq' : ContDiffAt ℝ k q x) (hf' : ContDiffAt ℝ k f x) (he : Fuzz x k f q e)
    (hu : Envelope x k q u) (hh : ContDiff ℝ ω h) (ht : t∈Ioc 0 1) (hB : Width h (k+1) l R C)
    (hq : ‖t • q x‖≤R) (hf : ‖t • f x‖≤R) :
    let K := league k l u C; let m:=l+k; let H:=coat h l t
    Envelope x k (H ∘ q) K ∧ Envelope x k (H ∘ f) (K*(1+e)^m) ∧ Fuzz x k (H ∘ f) (H ∘ q) (K*(1+e)^m * e) := by
  intro K m H; have hv:=hu.1; have hp:=he.1; have hK: 0≤K:=prize hv hB.1 ..
  have hC:=hB.1
  have he' i (hi : i≤k) (e' : ℝ) (h : 0≤e') : allot i l (u+e') C ≤ K*(1+e')^m := (show allot i l _ _ ≤ (i+1:ℕ)*allot i l (u+e') C from
    le_mul_of_one_le_left (by unfold allot; positivity) (by simp)).trans (allotBound hv hC h hi l)
  refine ⟨⟨hK,fun n hn=>?_⟩,⟨by positivity,fun n hn=>?_⟩,by positivity,fun n hn=>?_⟩
  · apply (remit ht hB hq' hn hu hh hq).trans; simpa using he' n hn 0 le_rfl
  · exact (remit ht hB hf' hn (he.toward hu) hh hf).trans (he' n hn e hp)
  exact (due ht hB hq' hf' hn he hu hh hq hf).trans (mul_le_mul_of_nonneg_right (allotBound hv hC hp hn l) hp)
end YM.Planned.PrimaryIntegral295.Oval
