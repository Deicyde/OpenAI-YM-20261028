import YM.Next.ROTATIONS.Pivot
/-!
# The low-energy estimate actually used (dyads integrated in one bound).
-/
noncomputable section
namespace YM.Outer
open Set Function Filter MeasureTheory Measure Complex Table Row Boundary Probe OS Word Ward
open scoped Topology ContDiff BigOperators NNReal ENNReal InnerProductSpace
variable {G : Gauge} {L : Register G} {S : Table L}

private lemma centroid_drop (i) (f : Grouping) (d k) (h : Centred (d+k) (f i)) : Centred d (pump k (f i)) :=
    (by simpa only [stepAt,update_self] using disappear_add i f k d h)

/-- head sign positive. Constrain actual A. -/
private lemma concentrated (K : S.Hierarchy) {i : Axis} (V : Chamber S i) {J : S.Stress}
    (A : Weight L) (H : equalRead S A (pick (J i i))) (hh : Own A i false) (hp : Pressed i A)
    (hr : S.conj K.spin _ (J i i)=J i i) {D R} (hR : Portrait J D R) :
    ∃ M : ℕ, D≤M ∧ ∀ (g : Grouping), Centred M (g i) →
      Integrable (fun p => Reel i (g i) p * crop (other i) g p) (ν V A) ∧
      sent (R i i i i) g=(toll:ℂ) * ↑(∫ p,Reel i (g i) p * crop (other i) g p ∂ν V A) := by
  obtain ⟨m,hm⟩ := runs_point V K A hp
  let T := R i i i i
  refine ⟨max D m,le_max_left ..,fun g he => ?_⟩
  have hw : flat D (polar g i) := polar_flat g i _ (fun l hl => he l (by omega))
  let f : Panels := fun j => stamp (g j)
  have hx : Runs (ν V A) i 1 (f i) := hm (stamp (g i)) (centred_hollow _ m (fun l hl => he l (by omega))) 1 (by simp)
  have hv := auto_slice V K A hh f (allows_all A A i _ hp hp) hx
  refine ⟨crop_int (reel_int _ hx) _ _,?_⟩
  have heq := hv.2.2
  rw [show signValue false=1 by rfl,one_mul] at heq
  rw [sent_at,hR.agrees i i i i _ i hw, ← integral_complex_ofReal]
  apply Eq.trans ?_ (heq.trans ?_)
  · refine integral_congr_ae ?_
    have hx : ∀ᵐ p : E4,p≠0 := by simp only [ae_iff]; simp
    filter_upwards [hx] with x hg
    change Ward.pair _ _ x * _ = readsCluster S A A x* _
    rw [pair_reply K A A _ _ H H x hg,hr]; rfl
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [before V A] with p hp
  change Lap 1 _ _ * _ = _
  rw [ofReal_mul, Reel_real _ _ _ hp]
  exact congr_arg _ (crop_read ..)

private lemma intersects (H : S.Hierarchy) (P : DiffPlan S) (i : Axis) (K : Chamber S i) (hp : P.Derivatives S)
    (J : Stress S) (C : Conserved P H.spin J) (A : Weight L) (ha : equalRead S A (pick (J i i))) (hA : Own A i false) (ht : Pressed i A)
    {R D} (hR : Portrait J D R) (he : Strong J P D) (x : ℝ) (hx : x ≤ 0) (w : Axis→ℝ) (f : Grouping)
    (hl : ∀ j, Plus (f j)) : ∃ m : ℕ,
      let y (n) (p : E4) := fee m (fuel x n) 0 (p i)*crop (other i) (mails w f n) p
      (∀ n,
        Integrable (y n) (ν K A) ∧ hole (SelfB R i) m 0 x w f i n = toll*(∫ p, y n p ∂ν K A) ∧
        0 ≤ hole (SelfB R i) m 0 x w f i n ∧ hole (BL R i) m 1 x w f i n ≤ 0 ∧ 0≤hole (CL R i) m 2 x w f i n) := by
  obtain ⟨M,hM,h⟩ := concentrated H K A ha hA ht (C.real ..) hR
  obtain ⟨h₁,h₂⟩ := accounts_sink hR P hp H C he i
  let m := M+D+10
  refine ⟨m,?_⟩; intro y n
  let W := fuel x n
  let X (k) := gap m W k
  let F := mails w f n
  have hw : 0<W := fuel_pos ..
  have hW : W≤1 := (fuel_le hx n).trans_eq (fuel0 n)
  let g (k j) := tube w f n i (pump (2*j) (X k))
  have heq k j (a : ℕ) (hh : a+2*j ≤ 2*m) : Centred a (g k j i) := by
    unfold g tube; rw [update_self]
    let p := update F i (X k)
    have h : p i=X k := update_self ..
    rw [← h]; apply centroid_drop i p; rw [h]; exact fun v hv => gap_moment m W k hw _ (hv.trans_le hh)
  let Z (k j) (p : E4) := (-(p i)^2)^j*fee m W k (p i)*crop (other i) F p
  have hy (k j : ℕ) (hq : j ≤ 2) : Integrable (Z k j) (ν K A) ∧
      (SelfB R i (g k j)).re=toll*(∫ p, Z k j p ∂ν K A) := by
    obtain ⟨ht,hv⟩ := h (g k j) (heq k j M (by unfold m; omega))
    have he' : (fun p => Reel i (g k j i) p * crop (other i) (g k j) p)=ᵐ[ν K A] Z k j := by
      filter_upwards [before K A] with p hp
      rw [show g k j i=_ from update_self .., Reel,lamp_more _ j hp (gap_far m W k).1 (fun v hv => gap_moment m W k hw _ (by unfold m; omega)), fee_at m W k _ hp]
      change (_:ℂ).re*crop (other i) (update F i _) p=_
      rw [crop_up _ _ _ _ (by simp [other])]; unfold Z; rw [← ofReal_pow,← ofReal_neg,← ofReal_pow,← ofReal_mul,ofReal_re]
    refine ⟨ht.congr he',?_⟩
    rw [show SelfB R i _= _ from hv, re_ofReal_mul, ofReal_re]; congr 1; exact integral_congr_ae he'
  have hl' k p (hp : 0 ≤ p i) : 0 ≤ fee m W k (p i)*crop (other i) F p :=
    mul_nonneg (fee_pos m W k _ hw hW hp) (crop_nonneg _ _ (fun j _ => bill_plus (hl j) _ _) _)
  have hz := hy 0 0 (by norm_num)
  have hg k : g k 0=tube w f n i (X k) := by
    unfold g tube; congr; ext; simp [pump_at]
  have hv : Z 0 0=y n := by ext1 p; simp only [Z,pow_zero,one_mul]; rfl
  rw [hv,hg] at hz
  have vX : hole (SelfB R i) m 0 x w f i n=toll*(∫ p, y n p ∂ν K A) := by simp only [hole,Zframe,mul_zero,pow_zero,one_mul]; exact hz.2
  refine ⟨hz.1,vX,vX.trans_ge (mul_nonneg toll_pos.le (integral_nonneg_of_ae ((before K A).mono fun p hu => hl' 0 p hu))),?_,?_⟩
  · apply mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (inv_pos.mpr hw |>.le) _)
    have hr : BL R i (tube w f n i (X 1))=SelfB R i (g 1 1) := by
      rw [BL_law hR,_root_.add_apply,h₁ _ (hg .. ▸ heq 1 0 _ (by unfold m;omega)),add_zero,Pmul_at,stepAt,tube]; simp only [update_self, update_idem]; rfl
    change (BL R i _).re≤0; rw [hr,(hy 1 1 (by norm_num)).2]
    apply mul_nonpos_of_nonneg_of_nonpos toll_pos.le (integral_nonpos_of_ae _)
    filter_upwards [before K A] with p hp
    change Z 1 1 p ≤ 0; unfold Z; rw [pow_one,mul_assoc]; exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (p i)]) (hl' 1 p hp)
  apply mul_nonneg (pow_nonneg (inv_pos.mpr hw |>.le) _)
  have hr : CL R i (tube w f n i (X 2))=SelfB R i (g 2 2) := by
    rw [CL_law hR,_root_.add_apply,h₂ _ (hg .. ▸ heq 2 0 _ (by unfold m; omega)),add_zero,Pmul_at]
    rw [show stepAt _ _ _ = g 2 1 by unfold g stepAt tube; simp, BL_law hR,_root_.add_apply,h₁ _ (heq 2 1 _ (by unfold m; omega)),add_zero,Pmul_at]
    congr 1; unfold g stepAt tube; simp only [update_self,update_idem,pump_pump]
  change 0 ≤ (CL R i _).re; rw [hr,(hy 2 2 le_rfl).2]
  apply mul_nonneg toll_pos.le (integral_nonneg_of_ae _); filter_upwards [before K A] with p hp
  change 0≤Z 2 2 p; unfold Z; rw [mul_assoc]; exact mul_nonneg (sq_nonneg _) (hl' 2 p hp)

def coneWeight (i : Axis) (w : ℝ) (f : Grouping) (p : E4) := if p i≤1 then
    p i*w^4/(p i+w)^4 * crop (other i) f p else 0
lemma cone_meas (i : Axis) (w f) : Measurable (coneWeight i w f) := by
  have hm : Measurable fun p : E4 => p i := by fun_prop
  have he := crop_meas (other i) f
  unfold coneWeight; exact Measurable.ite (measurableSet_le hm (measurable_const (a:=1))) (by fun_prop) measurable_const
lemma cone_nn (i : Axis) (w : ℝ) (f : Grouping) (h : ∀ i, Plus (f i)) (p : E4) (hw : 0<w) (he : 0≤p i) :
    0 ≤ coneWeight i w f p := by
  unfold coneWeight; split_ifs; swap; · exact le_rfl
  exact mul_nonneg (by positivity) (crop_nonneg _ _ (fun i _ => h i) _)

lemma mass (V : ∀ i, Chamber S i) (H : S.Hierarchy) (J : Stress S) (P : DiffPlan S) (hp : P.Derivatives S) (ho : P.Orientation H.spin)
    (hr : RawTensor H.spin J) (C : Conserved P H.spin J) (i : Axis) (A : Weight L) (hA : equalRead S A (pick (J i i)))
    (ha : Own A i false) (hx : Pressed i A) (w : Axis→ℝ) (a : ℝ) (ht : a≤0) (hw : ∀ j,j≠i → w j≤a)
    (f : Grouping) (hf : Colors Finset.univ f) (δ : ℝ) (hd : 0<δ) :
    (∀ n, Integrable (coneWeight i (fuel a n) (mails w f n)) (ν (V i) A)) ∧
    Budget (δ+a*4) (fun n => ∫ p, coneWeight i (fuel a n) (mails w f n) p ∂ν (V i) A) := by
  obtain ⟨D,hD,he⟩ := stronger H J P
  obtain ⟨R,hR⟩ := portrays H J hr (fun i j => C.symmetric i j) D he.bound
  let F := joint R
  have hI : Portrait J D F := joined hR hD
  obtain ⟨B,Y,Z⟩ := accounts_fixed V H P hp ho J C hr hI δ hd i (update w i 0) (update_self ..) a ht (fun j hj => by rw [update_of_ne hj ..]; exact hw _ hj)
  obtain ⟨hE,hL⟩ := accounts_cost hR hD P hp H C he a ht (update w i a) (fun j => by
    by_cases h : j=i; · simp [h]
    simpa [h] using hw _ h) i
  have hwQ l := hf l (Finset.mem_univ _)
  have hG l := (hwQ l).1; have hH l := (hwQ l).2.1; have hT l := (hwQ l).2.2
  obtain ⟨m,h⟩ := intersects H P i (V i) hp J C A hA ha hx hI he a ht w f hH
  let μ := ν (V i) A
  let g := fun n p => fee m (fuel a n) 0 (p i)* crop (other i) (mails w f n) p
  have py n := (h n).2.1
  let M := SelfB F i
  let N := BL F i; let L := CL F i
  -- solve prices at a retained order m. Never take m->infty holding adaptive inputs undefined.
  have hCash : Budget (δ+a*2) (hole M m 0 a w f i) := by
    have hp p : Budget (δ+a*2) (fun n => cabin N 1 a w f i p n - p^2 * cabin M 0 a w f i p n) :=
      (heights i w a M (DB F i) N (BL_law hI i) 0 p f _ hE).rise (by push_cast; linarith)
    have ht' p : Budget (δ+a*2) (fun n => cabin L 2 a w f i p n - p^2 * cabin N 1 a w f i p n) :=
      (heights i w a N (DC F i) L (CL_law hI i) 1 p f _ hL).rise (by push_cast; linarith)
    apply budget_lock (δ+a*2) (cabin M 0 a w f i 1) (cabin M 0 a w f i 2) (cabin N 1 a w f i 1) (cabin N 1 a w f i 2)
      (cabin L 2 a w f i 1) (cabin L 2 a w f i 2) (hole M m 0 a w f i) (hole N m 1 a w f i) (hole L m 2 a w f i)
    · simpa using hp 1
    · convert hp 2 using 1; norm_num
    · simpa using ht' 1
    · convert ht' 2 using 1; norm_num
    · exact Eventually.of_forall fun n => (h n).2.2
    · exact (rift i w _ δ a 0 ht B f hG (fun j _ => hT j) m).rise (by push_cast; linarith)
    · exact (rift i w _ (δ+a+a) a 1 ht Y f hG (fun j _ => hT j) m).rise (by push_cast; linarith)
    · exact (rift i w _ (δ+a+a+a+a) a 2 ht Z f hG (fun j _ => hT j) m).rise (by push_cast; linarith)
  obtain ⟨c,hc,hp⟩ := grant m
  have hh : Budget (δ+a*2) (fun n => ∫ p,g n p ∂μ) := by
    refine (hCash.times toll⁻¹).same (Eventually.of_forall fun i => ?_)
    change toll⁻¹*(hole M m 0 _ _ _ _ i)= _
    rw [py i,← mul_assoc, inv_mul_cancel₀ toll_pos.ne',one_mul]
  have hw' n := fuel_pos a n
  have hw1 n : fuel a n ≤ 1 := (fuel_le ht n).trans_eq (fuel0 n)
  let A' n := c⁻¹*fuel a n^2
  let W n := coneWeight i (fuel a n) (mails w f n)
  have hr n : ∀ᵐ p ∂μ,0 ≤ W n p := (before (V i) A).mono fun p hp => cone_nn i _ _ (fun i => bill_plus (hH i) _ _) p (hw' _) hp
  have hs n : ∀ᵐ p ∂μ,W n p ≤ A' n*g n p := by
    filter_upwards [before (V i) A] with p he
    have hz : 0 ≤ crop (other i) (mails w f n) p := crop_nonneg _ _ (fun i _ => bill_plus (hH i) _ _) p
    unfold W coneWeight; split_ifs with hx
    · have ht := hp _ _ (hw' n) (hw1 n) he hx
      unfold A' g; rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ hz
      refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left ht (show 0 ≤ c⁻¹*fuel a n^2 by positivity))
      field_simp
    exact mul_nonneg (show 0 ≤ c⁻¹*fuel a n^2 by positivity) (mul_nonneg (fee_pos m _ _ _ (hw' n) (hw1 n) he) hz)
  have HV n : Integrable (W n) μ := ((h n).1.const_mul (A' n)).mono' (cone_meas i _ _).aestronglyMeasurable (by
    filter_upwards [hs n,hr n] with p ht hp; rw [Real.norm_of_nonneg hp]; exact ht)
  refine ⟨HV,?_⟩
  apply (((((budget_fuel a).pow 2).times c⁻¹).prod hh).rise ?_).signed
  · exact Eventually.of_forall fun n => integral_nonneg_of_ae (hr n)
  · refine Eventually.of_forall fun n => ?_
    change _ ≤ A' n * integral μ (g n)
    rw [← integral_const_mul]; exact integral_mono_ae (HV n) ((h n).1.const_mul _) (hs n)
  push_cast; linarith
end YM.Outer
