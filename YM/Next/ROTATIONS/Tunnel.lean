import YM.Next.ROTATIONS.GapTest
import YM.Next.ROTATIONS.Walk
/-! # Weighted estimates for a collinear word, paying for a genuine gap and all scales.

Here we use the same family of spectral measures throughout.
-/
noncomputable section
namespace YM.Outer
open MeasureTheory Measure Function Set Filter Row OS Boundary Probe
open scoped Topology ContDiff BigOperators NNReal ENNReal

variable {G : Gauge} {L : Register G} {S : Table L} (V : ∀ i, Chamber S i)

abbrev other (i : Axis) := (Finset.univ.erase i)
lemma apart {i j : Axis} (h : j≠i) : j∈other i := Finset.mem_erase.mpr ⟨h,Finset.mem_univ _⟩
def low (i : Axis) (s : ℝ) (p : E4) := if p i ≤ 1 then (p i+s)⁻¹ else 0
def cost (i : Axis) (Q : Finset Axis) (s : ℝ) (f : Grouping) (p : E4) := low i s p * crop (Q.erase i) f p
lemma low_nn (i : Axis) (s) (p : E4) (hs : 0<s) (hp : 0≤p i) : 0≤low i s p := by unfold low; split <;> positivity
lemma low_m (i : Axis) (s) : Measurable (low i s) := Measurable.ite (measurableSet_le (by fun_prop)
    (measurable_const (a:=1))) (by fun_prop) measurable_const
lemma cost_nn (i Q s f p) (hs : 0<s) (hp : 0 ≤ p i) (hf : ∀ j∈Q.erase i,Plus (f j)) : 0≤cost i Q s f p :=
  mul_nonneg (low_nn _ _ _ hs hp) (crop_nonneg (Q.erase i) _ hf p)
lemma low_int (i : Axis) (A : Weight L) (s : ℝ) (hs : 0<s) : Integrable (low i s) (ν (V i) A) := by
  let T := {p : E4| p i≤1}
  let μ := ν (V i) A
  have hi : Integrable (T.indicator fun p:E4 => s⁻¹) μ :=
    (integrableOn_const (show μ T≠⊤ from (within (V i) A 1).ne)).integrable_indicator (measurableSet_le (by fun_prop) measurable_const)
  refine hi.mono' (low_m i s).aestronglyMeasurable ?_
  filter_upwards [before (V i) A] with p hp
  rw [Real.norm_of_nonneg (low_nn i _ _ hs hp)]; unfold low; split_ifs with H
  · rw [indicator_of_mem (show p∈T from H)]; exact inv_anti₀ hs (by linarith)
  rw [indicator_of_notMem (show p∉T from H)]
lemma cost_int (i : Axis) (A : Weight L) (s : ℝ) (hs : 0<s) (Q) (f : Grouping) :
    Integrable (cost i Q s f) (ν (V i) A) := crop_int (low_int V i A s hs) _ _
private lemma projects (i : Axis) (A : Weight L) (Q : Finset Axis) (h : ℕ → Profile) (f : ℕ→Grouping)
    (hf : ∀ n l,l∈Q.erase i → Plus (f n l)) (q : ℝ)
    (hv : ∀ᶠ n in atTop, Runs (ν (V i) A) i 1 (stamp (h n)))
    (hc : ∃ c : ℝ,0<c ∧ ∀ᶠ n in atTop, ∀ p : E4, 0≤p i → low i (fuel q n) p ≤ c*Reel i (h n) p)
    (a : ℝ) (hh : Budget a (fun n => pay (ν (V i) A) i Q (h n) (f n))) :
    Budget a (fun n => ∫ p,cost i Q (fuel q n) (f n) p ∂ν (V i) A) := by
  obtain ⟨c,he,hc⟩ := hc; apply (hh.times c).signed
  · exact .of_forall fun n => integral_nonneg_of_ae ((before (V i) A).mono fun p hp => cost_nn i Q _ _ _ (fuel_pos ..) hp (hf n))
  filter_upwards [hv,hc] with n hv hc
  change _≤ c* ∫ p,Reel i (h n) p * crop (Q.erase i) (f n) p ∂ν (V i) A
  rw [← integral_const_mul]
  refine integral_mono_ae (cost_int V i _ _ (fuel_pos ..) _ _) ((crop_int (reel_int _ hv) _ _).const_mul c) ((before (V i) A).mono fun p hp => ?_)
  change _≤c*(_*_)
  rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (hc p hp) (crop_nonneg _ _ (hf n) p)

/-- For a point-like axis of a mixed cluster. Needs only transverse profiles. -/
theorem point_cost (H : S.Hierarchy) (i : Axis) (A : Weight L) (e) (Q : Finset Axis)
    (hi : i∈Q) (he : Mixed Q e) (hp : ∀ i∈Q,Pressed i A) (hk : ∀ i∈Q,Own A i (e i))
    (w : Axis→ℝ) (hw : ∀ i∈Q,w i≤0) (q : ℝ) (hq : q<0) (f : Grouping) (hf : Colors Q f)
    (δ : ℝ) (hd : 0<δ) : Budget δ (fun n => ∫ p,cost i Q (fuel q n) (mails w f n) p ∂ν (V i) A) := by
  let W := update w i q; let F := update f i center
  have hW : W i=q := update_self ..; have hF : F i=center := update_self ..
  obtain ⟨z,hz,h⟩ := walk V H Q e i hi he A hp hk W (fun j hj => by
    by_cases h : j=i
    · subst j; exact hW ▸ hq.le
    · rw [show W j=w j from update_of_ne h ..]; exact hw _ hj) δ hd
  have hx := mail_room hq center center_ends
  have he' : ∀ᶠ n in atTop, Room (mails W F n i) (1*fuel 0 n) := by
    simp_rw [mails,hW,hF,one_mul]; exact hx
  obtain ⟨m,h⟩ := h 0 le_rfl hz.le 1 le_rfl F (fun j hj => by
    by_cases he : j=i
    · subst j; rw [hF]; exact ⟨center_ends,center_plus,center_even⟩
    · rw [show F j=f j from update_of_ne he ..]; exact hf _ hj) he'
  obtain ⟨k,hV⟩ := runs_order (V i) H A (hp _ hi)
  let n := max m k
  have hy l : mails W F l= update (mails w f l) i (bill q l center) := by
    ext1 j; unfold mails
    by_cases h : j=i
    · subst j; rw [hF,hW,update_self]
    · simp [W,F,h]
  have ht := h n (le_max_left m k); simp_rw [hW,hy,pay_self,hF] at ht
  apply projects V i A Q _ _ (fun n l hh => bill_plus (hf l (Finset.mem_of_mem_erase hh)).2.1 _ _) q ?_ ?_ δ ht
  · refine .of_forall (fun k => hV _ (le_max_right ..) _ ?_ _ (center_ends.width _) (center_even.tall _))
    simp [fuel0]
  let C : ℝ := 2⁻¹ ^ n * 2⁻¹^(2*n)
  have hC : 0<C := by unfold C; positivity
  refine ⟨C⁻¹,inv_pos.mpr hC,?_⟩
  filter_upwards [he'] with j hj p hp
  let a := fuel q j
  let s := 1*fuel 0 j
  rw [hy j,update_self] at hj
  have hS : 1≤s := by simp [s,fuel0]
  rw [low]; split_ifs with H
  · rw [inv_mul_eq_div]; apply (le_div_iff₀ hC).mpr
    refine le_trans ?_ (lower n s a (p i) hS (fuel_pos ..) hj hp)
    change (p i+a)⁻¹ * _ ≤ _
    unfold C
    have hx : 0<p i+a := by have := show 0<a from fuel_pos ..; linarith
    rw [← mul_assoc,(mul_comm (p i+a)⁻¹)]; gcongr; linarith
  exact mul_nonneg (inv_pos.mpr hC |>.le) (lamp_signs n q 0 1 center center_ends center_plus j zero_lt_one hj i p hp)


private abbrev rear (u : ℝ≥0) (q : ℝ) (n) := bill q n civic-remote u (fuel q n)
private lemma earning (H : S.Hierarchy) (i : Axis) (A : Weight L) (u : ℝ≥0) (hu : Lowered i A u)
    (k : ℕ) (j : Axis) (hj : j≠i) (q : ℝ) :
    (∀ n, Integrable (fun p : E4 => Reel i (rear u q n) p * ‖p j‖^(2*k)) (ν (V i) A)) ∧
    Budget (-q) (fun n => ∫ p, Reel i (rear u q n) p * ‖p j‖^(2*k) ∂ν (V i) A) := by
  obtain ⟨C,hC,h⟩ := remote_top u
  have ht (n) := (show 0<fuel q n from fuel_pos q n)
  let f n (p : E4) := Reel i (rear u q n) p * ‖p j‖^(2*k)
  let μ := ν (V i) A
  let c := mom i j k (u+u:ℝ≥0)
  have hc := placed_moment (V i) H A j hj k u hu
  have hp n : ∀ᵐ p ∂μ, 0 ≤ f n p := (before (V i) A).mono fun p hp =>
    mul_nonneg (remote_sign u _ (ht n) i p hp) (pow_nonneg (norm_nonneg _) _)
  have hh (n) : ∀ᵐ p ∂μ, f n p ≤ C*fuel (-q) n*c p := by
    filter_upwards [before (V i) A] with p hi
    rw [fuel_neg]
    exact (mul_le_mul_of_nonneg_right (h _ (ht n) _ hi) (pow_nonneg (norm_nonneg _) (2*k))).trans_eq
      (mul_assoc ..)
  have hI n : Integrable (f n) μ := by
    apply (hc.const_mul (C*fuel (-q) n)).mono'
    · unfold f Reel; have he := Lap_meas 1 (stamp (rear u q n)); apply Measurable.aestronglyMeasurable; fun_prop
    filter_upwards [hp n,hh n] with p hf hr
    simpa only [Real.norm_of_nonneg hf] using hr
  have hz : 0 ≤ (∫ p,c p ∂μ) := integral_nonneg fun _ => mom_nn ..
  refine ⟨hI,C*(∫ p,c p ∂μ),mul_nonneg hC hz,Eventually.of_forall fun n => ?_⟩
  change ‖integral μ (f n)‖ ≤ _
  rw [Real.norm_of_nonneg (integral_nonneg_of_ae (hp n))]
  exact (integral_mono_ae (hI n) (hc.const_mul _) (hh n)).trans_eq (by rw [integral_const_mul,mul_right_comm])

lemma rein (i j : Axis) (hij : i≠j) (Q : Finset Axis) (hi : i∈Q) (A : Weight L) (f : Grouping) (h b : Profile)
    (he : ∀ k∈Q, k≠i → Plus (f k)) (hp : ∀ p : E4, 0≤p j → 0≤ Reel j h p) (hl : Runs (ν (V j) A) j 1 (stamp h))
    (C : ℝ) (hc : ∀ t,b t ≤ C) :
    pay (ν (V j) A) j Q h (update f i b) ≤ C*pay (ν (V j) A) j (Q.erase i) h f := by
  unfold pay; rw [← integral_const_mul]
  have ht := reel_int h hl
  refine integral_mono_ae (crop_int ht _ _) ((crop_int ht _ _).const_mul C) ((before (V j) A).mono fun p ho => ?_)
  dsimp only
  rw [crop_cons (Q.erase j) _ i _ _ (Finset.mem_erase.mpr ⟨hij,hi⟩),Finset.erase_right_comm,mul_left_comm C]
  apply mul_le_mul_of_nonneg_left _ (hp p ho); apply mul_le_mul_of_nonneg_right (hc _) (crop_nonneg _ _ _ _)
  intro l ha
  have heq := Finset.mem_of_mem_erase ha
  exact he _ (Finset.mem_of_mem_erase heq) (Finset.mem_erase.mp heq).1

/-- Gap-axis cost when the rest contains both signs; i may have offsets. -/
theorem gap_cost (H : S.Hierarchy) (i : Axis) (A : Weight L) (e) (j : Axis) (hi : j≠i)
    (hk : e i≠e j) (he : Mixed (other i) e) (hp : ∀ j∈other i,Pressed j A) (hE : ∀ i,Own A i (e i))
    (w : Axis→ℝ) (hw : ∀ j∈other i,w j≤0) (q : ℝ) (hq : q<0) (f : Grouping) (hf : Colors (other i) f)
    (δ : ℝ) (hd : 0<δ) : Budget δ (fun n => ∫ p,cost i Finset.univ (fuel q n) (mails w f n) p ∂ν (V i) A) := by
  let Q := other i
  have hj : j∈Q := apart hi
  obtain ⟨a,ha,h⟩ := walk V H Q e j hj he A hp (fun i _ => hE i) w hw δ hd
  have hh : ∀ᶠ n in atTop, Room (mails w f n j) (1*fuel a n) := by
    simp_rw [one_mul]; exact mail_room (lt_of_le_of_lt (hw j hj) ha) (f j) (hf j hj).1
  obtain ⟨m,hm⟩ := h a ha.le le_rfl 1 le_rfl f hf hh
  obtain ⟨n₁,h₁⟩ := runs_order (V j) H A (hp j hj)
  let N := max m n₁
  let d := lamps N (w j) a 1 (f j)
  have hz := hm N (le_max_left ..)
  obtain ⟨u,hu⟩ := (descends i A).exists
  let r := rear u q
  let J := mails w f
  let F n := update (J n) i (bill q n civic)
  have heq (n) (k : Axis) (h : k≠i) : F n k=J n k := update_of_ne h ..
  have hR (n) : Runs (ν (V i) A) i 1 (stamp (r n)) := runs_gap (V i) H A u hu _ (by simp) _ (remote_gap u _ (fuel_pos ..))
  refine projects V i A _ r _ (fun n l h => bill_plus ((hf l h).2.1) _ _) _ (.of_forall hR) ?_ _ ?_
  · obtain ⟨c,v,hc,hv,h⟩ := remote_base u
    refine ⟨c⁻¹,inv_pos.mpr hc,?_⟩
    filter_upwards [(fuel_falls hq).eventually (gt_mem_nhds hv)] with n hn p hp
    change fuel q n<v at hn
    rw [low]; split_ifs with H
    · have he := h _ (fuel_pos q n) hn.le _ hp H
      change _ ≤ _*Reel i _ p
      rw [inv_mul_eq_div,le_div_iff₀ hc,mul_comm]; exact (div_eq_mul_inv ..).symm.trans_le he
    exact mul_nonneg (inv_nonneg.mpr hc.le) (remote_sign u _ (fuel_pos ..) i p hp)
  obtain ⟨g,hG,hg,hg',he⟩ := paid_bill N 1 le_rfl (w j) a ((hw j hj).trans ha.le) (f j)
  obtain ⟨K,hK⟩ := (finite_range w).bddBelow
  let z := other i
  obtain ⟨k,hk'⟩ := exists_nat_gt ((-K*((z.erase j).card:ℝ) - q)/a)
  have hx := earning V H i A u hu k j hi q
  have hP n p : 0 ≤ p i → 0≤Reel i (r n) p := fun hp => remote_sign u _ (fuel_pos ..) i p hp
  have Hf := far_pay (V i) A r Finset.univ f w (.of_forall hP) (-K) (fun l _ => by simpa using (show K ≤ w l from hK ⟨l,rfl⟩)) j (Finset.mem_univ _) hi k (-q)
    (.of_forall hx.1) hx.2 g hG a ha.le
  have hm : Budget δ (fun n => pay (ν (V i) A) i Finset.univ (r n) (update (mails w f n) j (bill a n g))) := by
    apply Hf.rise
    have hz := (div_lt_iff₀ ha).1 hk'
    change -a* _ + -K * (z.erase j).card + _ ≤ _
    have hv : a*k ≤ a*(2*k:ℕ) := by gcongr; omega
    linarith
  obtain ⟨C,hC,hZ⟩ := remote_cost u
  apply (hm.add (hz.times C)).signed
  · exact .of_forall fun n => pay_nonneg (V i) A _ _ _ (hP n) (fun l hl => bill_plus (hf _ hl).2.1 _ _)
  filter_upwards [he,hh] with n hn hN
  have ht k : Plus (F n k) := by
    by_cases h : k=i
    · subst k; unfold F; rw [update_self]; exact bill_plus civic_plus q n
    · rw [heq n k h]; exact bill_plus (hf _ (apart h)).2.1 _ _
  let c := remote u (fuel q n)
  let b := bake N (1*fuel a n) (F n j)
  have H' : 0<1*fuel a n := by simpa using fuel_pos a n
  have hr (p : E4) (hp : 0≤p j) : 0≤ Reel j (d n) p :=
    lamp_signs N (w j) a 1 (f j) (hf _ hj).1 (hf _ hj).2.1 _ (by norm_num) hN _ p hp
  have Hy : Runs (ν (V j) A) j 1 (stamp (d n)) := h₁ N (le_max_right ..) _ H' _ (Ends.width (hf _ hj).1 _) ((hf _ hj).2.2.tall _)
  have Hx : F n j-b=d n := by unfold b; rw [heq n j hi]; rfl
  have Hw : F n i-c=r n := by unfold F; rw [update_self]
  have hA : Allows i A A (stamp (r n)) := fun t _ hh => ⟨u,hu,hu,remote_gap u _ (fuel_pos ..) t hh⟩
  have ha := alternate H _ _ (V i) (V j) A _ _ (hE i) (hE j) hi.symm hk Finset.univ (F n) (Finset.mem_univ _) (Finset.mem_univ _) c b
    (Hw.symm ▸ hA) (allows_all A A j _ (hp j hj) (hp j hj)) (Hw.symm ▸ hR n) (Hx.symm ▸ Hy) (Hx.symm ▸ hr) (fun k _ => ht k)
  have hl : pay (ν (V i) A) i Finset.univ (r n) (mails w f n)=pay (ν (V i) A) i Finset.univ (F n i-c) (F n) := by rw [Hw]; exact (pay_self ..).symm
  apply (hl.trans_le ha).trans
  rw [Hw,Hx]; apply add_le_add
  · apply le_trans (pay_mono (V i) A (F n) Finset.univ (r n) (hP n) (fun k _ => ht k) b (bill a n g) (hR n) j (Finset.mem_univ _) hi
      (fun x => (le_abs_self _).trans (show |b x|≤ _ from by unfold b; rw [heq n j hi]; exact hn x)))
    apply le_of_eq
    unfold F; rw [update_comm hi.symm, pay_self]
  rw [show update (F n) i c=update (mails w f n) i c from update_idem ..]
  apply rein V i j hi.symm _ (Finset.mem_univ _) A _ _ c (fun k _ h => bill_plus (hf _ (apart h)).2.1 _ _) hr Hy _ (fun t => (le_abs_self _).trans (hZ _ (fuel_pos ..) t))

/-- Low spectra of projected clusters on a line. Missing-axis price explicit. -/
theorem line_cost (H : S.Hierarchy) (l : Axis) (e : Axis→Bool) (A : Weight L) (hf : ∀ i, Own A i (e i))
    (he : Mixed (other l) e) (h : ∃ i∈other l,e i≠e l) (hp : ∀ j∈other l,Pressed j A)
    (i : Axis) (w : Axis→ℝ) (hw : ∀ j,w j≤0) (δ q : ℝ) (hq : q<0) (hd : 0<δ) (f : Grouping)
    (hl : Colors Finset.univ f) :
    Budget (if i=l then δ else -w l+δ) (fun n => ∫ p,cost i Finset.univ (fuel q n) (mails w f n) p ∂ν (V i) A) := by
  have HC : Colors (other l) f := fun j _ => hl j (Finset.mem_univ _)
  split_ifs with ht
  · subst i; obtain ⟨j,hj,h⟩ := h; exact gap_cost V H l A e j (Finset.mem_erase.mp hj).1 (Ne.symm h) he hp hf w (fun j _ => hw j) q hq f HC δ hd
  let Y := fun n p => cost i (other l) (fuel q n) (mails w f n) p
  have hh := point_cost V H i A e (other l) (apart ht) he hp (fun j _ => hf j) w (fun j _ => hw j) q hq f HC δ hd
  let C := SchwartzMap.seminorm ℝ 0 0 (f l)
  have hZ n (j) : Plus (mails w f n j) := bill_plus (hl _ (Finset.mem_univ _)).2.1 _ _
  apply (((budget_fuel _).times C).prod hh).signed
  · refine .of_forall fun n => integral_nonneg_of_ae ((before (V i) A).mono fun p hi => ?_)
    exact cost_nn i _ _ _ p (fuel_pos ..) hi fun j _ => hZ n j
  refine .of_forall fun n => ?_
  change _ ≤ C*fuel (-w l) n*integral (ν (V i) A) (Y n)
  rw [← integral_const_mul]
  refine integral_mono_ae (cost_int V i A _ (fuel_pos ..) _ _) ((cost_int V i A _ (fuel_pos ..) _ _).const_mul _) ((before (V i) A).mono fun p hi => ?_)
  have hz := crop_cons (other i) (mails w f n) l (mails w f n l) p (apart (Ne.symm ht))
  rw [update_eq_self] at hz
  change low _ _ p * crop (other i) _ p ≤ C*fuel _ n*(low _ _ p * crop _ _ p)
  rw [hz,mul_left_comm (C*fuel _ n)]; unfold other; rw [Finset.erase_right_comm]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ((le_abs_self _).trans
    (bill_cash (w l) n (f l) (-w l) (by simp) (p l))) (crop_nonneg _ _ (fun j _ => hZ _ _) _)) (low_nn _ _ _ (fuel_pos ..) hi)
end YM.Outer
