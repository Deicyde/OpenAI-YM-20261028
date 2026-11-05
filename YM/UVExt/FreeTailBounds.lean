import YM.Next.FREE_KERNELS.Reserve

/-! Ultraviolet boundary comparison for the actual preselected *linear* filter recursion;
Part A: real-momentum bounds, including uniformity over fan-out of the train and its starting
index, charging only the latter for the size of a small neighborhood of zero. No nonlinear
step or represented coupling convergence is presumed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric
open scoped Topology BigOperators

variable {j : ℕ} {M : Side}
namespace UV
lemma area_real_le (M : Side) {p : Momentum} (h : physical p) : ‖area M p‖ ≤ 1 := by
  unfold area; rw [norm_prod]; apply le_trans (Finset.prod_le_prod (s:=Finset.univ) (f:=fun i=> ‖plank M (p i)‖)
    (g:=fun _ : Axis=> (1:ℝ)) (fun i _=> norm_nonneg _) (fun i _ => ?_))
  · simp 
  simpa only [(physical_iff _).mp h i,abs_zero,mul_zero,Real.exp_zero] using plank_height M (p i)
lemma rail_real_le (M : Side) {p : Momentum} (h : physical p) (i : Axis) : ‖rail M (p i)‖ ≤ 1 := by
  simpa only [(physical_iff _).mp h i,abs_zero,mul_zero,Real.exp_zero] using rail_height M (p i)
lemma extra_real_le (v : Train j) {p : Momentum} (h : physical p) : ‖v.extra p‖ ≤ 1 := by
  induction v with
  | top j => exact norm_one.le
  | hop P h' ht v ih =>
    unfold Train.extra; rw [norm_mul,norm_pow]; exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) (area_real_le _ h))
      (norm_nonneg _) ih
lemma alias_decay : ∃ C : ℝ, 0 < C ∧ ∀ {k : ℕ} (v : Train k), 2 ≤ k → ∀ p ∈ realCube zone,
    ∀ l : Site v.mass,∀ a : Axis, ‖yen (v.drive a) (aliasAt p l)‖ ≤ C * decay 2 l := by
  obtain ⟨B,hB,h⟩ := alias_rail
  refine ⟨(B^4)^2,pow_pos (pow_pos hB _) _,fun {k} v hv p hp l a=>?_⟩
  have he (p : Momentum) (hp : p∈realCube zone) (l : Site v.mass) := (alias_in_real zone_pos hp l v.mass_odd).1
  have hA (p : Momentum) (hq : physical p) : ‖v.drive a p‖ ≤ ‖area v.mass p‖^k := by
    unfold Train.drive Train.smooth; rw [norm_mul,norm_mul,norm_pow]
    exact (mul_le_of_le_one_right (by positivity) (rail_real_le _ hq _)).trans
      (mul_le_of_le_one_right (by positivity) (extra_real_le _ hq))
  have hneg : physical (-aliasAt p l) := (physical_iff _).mpr (fun i=> by simp [show ((aliasAt p l) i).im=0 from (physical_iff _).mp (he p hp l) i])
  have ht' := hA _ hneg
  have ha : ‖area v.mass (aliasAt p l)‖ ≤ B^4 * (mix l)⁻¹ := by
    unfold area; rw [norm_prod]
    exact (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _=> (h v.mass v.mass_odd _ (mem_cube_real hp zone_pos) _ i).2)).trans_eq
      (by simp [Finset.prod_mul_distrib,Axis,mix])
  unfold yen; rw [norm_mul]
  refine (mul_le_of_le_one_right (norm_nonneg _) (ht'.trans (pow_le_one₀ (norm_nonneg _) (area_real_le _ hneg)))).trans
    ((hA _ (he p hp l)).trans ?_)
  rw [show ‖area v.mass (aliasAt p l)‖^k = ‖area v.mass (aliasAt p l)‖^(k-2)*‖area v.mass (aliasAt p l)‖^2 from by rw [←pow_add,Nat.sub_add_cancel hv]]
  exact (mul_le_of_le_one_left (by positivity) (pow_le_one₀ (norm_nonneg _) (area_real_le _ (he p hp l)))).trans
    ((pow_le_pow_left₀ (norm_nonneg _) ha 2).trans_eq (by rw [mul_pow,inv_pow,decay]))

lemma alias_gap : ∃ b : ℝ, 0 < b ∧ ∀ M L : Side, Odd L.val → ∀ p ∈ baseCube,
    ∀ l : Site L,l≠0 → b ≤ ‖blow M p l‖ := by
  let X := Σ (s : Side), {l : Site s// Odd s.val ∧ l≠0}
  obtain ⟨η,C,hη,hC,h⟩ := @blow_firm (X × Side) (fun i=>i.1.1) (fun i=>i.2)
    (fun i=>i.1.2.property.1) (fun i=>i.1.2.val) (fun i=>i.1.2.property.2)
  exact ⟨C,hC,fun M L H p hp l hv => (le_mul_of_one_le_right hC.le (one_le_pow₀ (grade_ge _))).trans
    (h (⟨L,l,H,hv⟩,M) p (base_subset_realCube hη hp))⟩

lemma drain_bound (k : ℝ) : ∃ C : ℝ, 0 < C ∧ ∀ {i : ℕ} (v : Train i), 2 ≤ i → ∀ p∈baseCube, ∀ a : Axis, ‖v.drain k a p‖ ≤ C := by
  obtain ⟨D,hD,hδ⟩ := decay_cost
  obtain ⟨c,hc,hℓ⟩ := alias_decay
  obtain ⟨η,hη,h₀⟩ := alias_gap
  have hN {i : ℕ} (v : Train i) (hi : 2 ≤ i) {p : Momentum} (hp : p∈baseCube) (a : Axis) :
      ‖feed v a (fun _ => 1) p‖ ≤ ((v.mass.val:ℝ)^2)⁻¹*(c*D) := by
    unfold feed shuttle; simp only [norm_mul,norm_inv,norm_pow,Complex.norm_natCast,mul_one]
    apply mul_le_mul_of_nonneg_left <;> [skip; positivity]; apply (norm_sum_le ..).trans
    calc
      _ ≤ ∑ l : Site v.mass, c * decay 2 l := Finset.sum_le_sum fun l _ => hℓ _ hi _ (base_subset_realCube zone_pos hp) _ _
      _ ≤ c*D := by rw [←Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hδ _) hc.le
  have hH {i : ℕ} (v : Train i) (hi : 2 ≤ i) {p : Momentum} (hp : p∈baseCube) (a : Axis) :
      ‖v.high a p‖ ≤ η⁻¹*(c*D) := by
    unfold Train.high; apply le_trans (norm_sum_le ..)
    calc
      _ ≤ ∑ l ∈ Finset.univ.erase 0, η⁻¹*(c*decay 2 l) := Finset.sum_le_sum fun l hl => (by
        have hb := hℓ v hi p (base_subset_realCube zone_pos hp) l a
        have hh := h₀ 1 v.mass v.mass_odd _ hp l (Finset.mem_erase.mp hl).1
        rw [norm_mul,norm_inv, mul_comm (η)⁻¹]
        exact mul_le_mul hb ((inv_le_inv₀ (hη.trans_le hh) hη).mpr hh) (by positivity) (by positivity [decay_pos l 2]))
      _ ≤ _ := by
        rw [← Finset.mul_sum,← Finset.mul_sum]; apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left _ hc.le) (by positivity)
        exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun l _ _=> (decay_pos _ _).le).trans (hδ _)
  let b := η⁻¹*(c*D)+ ‖(k:ℂ)‖⁻¹*(2*(c*D)); refine ⟨b, by unfold b; positivity,fun {i} v hi p hp a=>?_⟩
  unfold Train.drain b; refine (norm_add_le ..).trans (add_le_add (hH _ hi hp _) ?_)
  simp only [Train.levelNoise, norm_mul,norm_inv]; apply mul_le_mul_of_nonneg_left _ (by positivity)
  have ht (l) : ‖Train.stream (j:=i) l a p‖ ≤ Train.tapMoney l*(c*D) := by
    induction l with
    | nil => simp only [Train.tapMoney,List.map_nil,List.sum_nil,zero_mul,Train.stream,norm_zero,le_rfl]
    | cons t u ih =>
      change ‖feed t a (fun _=> 1) p + Train.stream u a p‖ ≤ _
      simp only [Train.tapMoney,List.map_cons,List.sum_cons]; rw [add_mul]
      exact (norm_add_le ..).trans (add_le_add (hN t hi hp _) ih)
  exact (ht _).trans (mul_le_mul_of_nonneg_right v.tap_safe (by positivity))

lemma plank_approx (M : Side) (z : ℂ) (h : M.val*‖z‖ ≤ domainRadius) :
    ‖plank M z - 1‖ ≤ meter.high * M.val * ‖z‖ ∧ ‖rail M z - 1‖ ≤ meter.high * M.val * ‖z‖ := by
  have he (d : ℤ) (hd : |d| ≤ M.val) : ‖twirl z d - 1‖ ≤ meter.high * M.val * ‖z‖ := by
    let w : ℂ := d*z
    rw [show twirl z d - 1=chip w from by unfold twirl chip w; rw [mul_left_comm]]
    have hw : ‖w‖ ≤ M.val*‖z‖ := by
      unfold w; rw [norm_mul, Complex.norm_intCast]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hd) (norm_nonneg _)
    exact (meter.above w (hw.trans h)).trans (mul_assoc meter.high _ _ ▸ (mul_le_mul_of_nonneg_left hw meter.high_pos.le))
  have h₀ (g : ℕ→ℂ) : (M.val:ℂ)⁻¹ * (∑ i∈Finset.range M.val, g i) - 1 = (M.val:ℂ)⁻¹* (∑ i∈Finset.range M.val, (g i - 1)) := by
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one,mul_sub,inv_mul_cancel₀ (side_ne M)]
  rw [plank_centers,rail,h₀,h₀]; constructor <;> exact average_bound _ _ (fun i hi => he _ (by have hI := Finset.mem_range.mp hi; first | exact all_centers _ _ hI | {rw [abs_of_nonneg (Int.natCast_nonneg _)]; exact_mod_cast hI.le}))

lemma sub_prod (x y : ℂ) (hx : ‖x‖ ≤ 1) : ‖x*y-1‖ ≤ ‖x-1‖+‖y-1‖ := calc
  _ = ‖x*(y-1)+(x-1)‖ := by congr 1; ring
  _ ≤ ‖x*(y-1)‖+‖x-1‖ := norm_add_le ..
  _ ≤ ‖x-1‖+‖y-1‖ := by rw [add_comm]; exact add_le_add_right ((norm_mul x (y-1)).trans_le (mul_le_of_le_one_left (norm_nonneg _) hx)) _

lemma sub_pow (k : ℕ) (x : ℂ) (hx : ‖x‖ ≤ 1) : ‖x^k-1‖ ≤ k*‖x-1‖ := by
  induction k with
  | zero => simp only [pow_zero,sub_self,norm_zero,Nat.cast_zero,zero_mul,le_rfl]
  | succ k ih =>
    rw [pow_succ',Nat.cast_succ,add_mul,one_mul,add_comm (k*‖x-1‖)]
    exact (sub_prod _ _ hx).trans (add_le_add_right ih _)

lemma sub_finset {α : Type*} (x : α→ℂ) (s : Finset α) {R : ℝ} (h : ∀ a∈s, ‖x a‖ ≤ 1)
    (hR : ∀ a∈s, ‖x a-1‖ ≤ R) : ‖∏ a∈s, x a - 1‖ ≤ s.card * R := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha,Finset.card_insert_of_notMem ha, Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm ((s.card:ℝ)*R)]
    exact (sub_prod _ _ (h _ (Finset.mem_insert_self ..))).trans (add_le_add (hR _ (Finset.mem_insert_self ..))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)) (fun i hi => hR i (Finset.mem_insert_of_mem hi))))

variable {p : Momentum} {δ : ℝ}
lemma motor_quote (hδ : 0 < δ) (hd : δ ≤ domainRadius) (hp : physical p) (h : ∀ a, ‖p a‖ ≤ δ) (v : Train j) (a : Axis) :
    |‖yen (v.drive a) (narrow v.mass p)‖ - 1| ≤ (8:ℝ)*meter.high*δ*(j+4) := by
  have hb (M L : Side) (hl : M≤ L) (q : Momentum) (hq : q∈({p,-p}:Set Momentum)) :
      physical (narrow L q) ∧
      (∀ a, ‖plank M (narrow L q a)-1‖ ≤ meter.high * (M.val / (L.val:ℝ)) * δ ∧
        ‖rail M (narrow L q a)-1‖ ≤ meter.high * (M.val / (L.val:ℝ)) * δ) ∧
      ‖area M (narrow L q) - 1‖ ≤ 4*meter.high*(M.val/(L.val:ℝ))*δ := by
    have Hq a : (q a).im=0 ∧ ‖q a‖ ≤ δ := by rcases hq with rfl|rfl; exact ⟨(physical_iff _).mp hp a,h a⟩; simpa only [Pi.neg_apply,norm_neg,Complex.neg_im,neg_eq_zero] using And.intro ((physical_iff _).mp hp a) (h a)
    have hx : physical (narrow L q) := narrow_real L ((physical_iff _).mpr fun a => (Hq a).1)
    have he a : ‖narrow L q a‖ = ‖q a‖ / (L.val:ℝ) := by rw [narrow_apply,norm_div, Complex.norm_natCast]
    have hw : (M.val:ℝ)/L.val ≤ 1 := (div_le_one (side_pos L)).mpr (by exact_mod_cast hl)
    have hy a : M.val*‖narrow L q a‖ ≤ M.val/(L.val:ℝ)*δ := by
      rw [he, div_mul_eq_mul_div,mul_div_assoc]; exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (Hq _|>.2) (by positivity)) (by positivity)
    have hC a := plank_approx M (narrow L q a) ((hy a).trans ((mul_le_of_le_one_left hδ.le hw).trans hd))
    have hT a : _ := mul_le_mul_of_nonneg_left (hy a) meter.high_pos.le
    constructor
    · exact hx
    refine ⟨fun a => ⟨(hC a).1.trans ?_,(hC a).2.trans ?_⟩,?_⟩
    all_goals try { rw [mul_assoc,mul_assoc]; exact hT _ }
    convert (sub_finset (fun i => plank M (narrow L q i)) .univ (R:=meter.high*(M.val/(L.val:ℝ))*δ)
      (fun i _ => show ‖plank M (narrow L q i)‖≤1 by simpa [(physical_iff _).mp hx i] using plank_height M (narrow L q i)) ?_) using 1
    · rfl
    · simp [Axis]; ring
    intro i _; refine (hC _).1.trans ?_; rw [mul_assoc,mul_assoc]; exact hT i
  have hY {q} (hq : q∈({p,-p}:Set Momentum)) : ‖v.drive a (narrow v.mass q)-1‖ ≤ 4*meter.high*δ*(j+4) := by
    let L := v.mass; let z := narrow L q
    have hL := side_pos L; have hh (M : Side) (hm:M.val≤L.val) := hb M L hm q hq
    have hx := hh L le_rfl
    have ht' {i} (u : Train i) (he : u.mass.val≤L.val) : ‖u.extra z - 1‖ ≤ 8*meter.high*δ*(u.mass.val / (L.val:ℝ)) := by
      induction u with
      | top j => unfold Train.extra; simp only [sub_self,norm_zero]; have := meter.high_pos; positivity
      | @hop t P h1 h2 u ih =>
        let u' := Train.hop P h1 h2 u
        have hf : u.mass.val ≤ L.val := (Train.prev_mass ..).trans he
        have H := hh u'.mass he
        have hP := Train.smaller_mass L P u
        have hI := ih hf; have hM := meter.high_pos
        unfold Train.extra
        rcases ((by omega : P.J-t ≤ 1) |>.eq_or_lt) with hs|hs
        · rw [hs,pow_one]
          exact (sub_prod _ _ (area_real_le _ H.1)).trans (by change ‖area u'.mass z-1‖ + _ ≤ 8*meter.high*δ*(u'.mass.val/(L.val:ℝ)); apply (add_le_add H.2.2 hI).trans; change 3* _ ≤ (u'.mass.val/ (L.val:ℝ)) at hP; nlinarith [mul_nonneg (mul_pos hM hδ).le (sub_nonneg.mpr hP), mul_nonneg (mul_pos hM hδ).le (by positivity : 0 ≤ (u.mass.val/(L.val:ℝ)))])
        · rw [show P.J-_ = 0 from Nat.lt_one_iff.mp hs, pow_zero, one_mul]
          exact hI.trans (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by exact_mod_cast Train.prev_mass P u) (by positivity)) (by positivity))
    have hA : ‖area L z-1‖ ≤ 4*meter.high*δ := by
      simpa only [div_self hL.ne',mul_one] using hx.2.2
    have hR : ‖rail L (z a)-1‖ ≤ meter.high*δ := by simpa only [div_self hL.ne',mul_one] using (hx.2.1 a).2
    have hE : ‖v.extra z-1‖ ≤ 8*meter.high*δ := by simpa only [L,div_self (side_pos _).ne',mul_one] using (ht' v le_rfl)
    refine (sub_prod (v.smooth z) _ ?_).trans ?_
    · unfold Train.smooth; rw [norm_mul,norm_pow]; exact (mul_le_one₀ (pow_le_one₀ (norm_nonneg _) (area_real_le _ hx.1)) (norm_nonneg _) (extra_real_le _ hx.1))
    have ha := sub_prod (area L z^j) (v.extra z) ((norm_pow ..).trans_le (pow_le_one₀ (norm_nonneg _) (area_real_le _ hx.1)))
    have he := sub_pow j (area L z) (area_real_le _ hx.1)
    apply (add_le_add (ha.trans (add_le_add he hE)) hR).trans
    have hm := meter.high_pos; nlinarith
  rw [yen,← narrow_neg]
  have hh := (hb v.mass v.mass le_rfl p (by simp)).1
  have hA : ‖v.drive a (narrow v.mass p)‖ ≤ 1 := by rw [Train.drive,Train.smooth,norm_mul,norm_mul,norm_pow]; exact mul_le_one₀ (mul_le_one₀ (pow_le_one₀ (norm_nonneg _) (area_real_le _ hh)) (by positivity) (extra_real_le _ hh)) (by positivity) (rail_real_le _ hh _)
  have Hfinal : |‖v.drive a (narrow v.mass p) * _‖ - ‖(1:ℂ)‖| ≤ 4*meter.high*δ*(j+4) + 4*meter.high*δ*(j+4) := 
    (abs_norm_sub_norm_le _ (1:ℂ) |>.trans ((sub_prod _ _ hA).trans (add_le_add (hY (q:=p) (by simp)) (hY (q:=-p) (by simp)))))
  rw [norm_one] at Hfinal; linarith


lemma chip_extends : Continuous (dslope chip 0) ∧ dslope chip 0 0=Complex.I := by
  have hD : Differentiable ℂ chip := by unfold chip; fun_prop
  have he : HasDerivAt chip Complex.I 0 := by
      have hh := ((hasDerivAt_id' (0 : ℂ)).const_mul Complex.I).cexp.sub_const 1
      unfold chip; simpa only [mul_one,one_mul,mul_zero,zero_mul,Complex.exp_zero] using hh
  exact ⟨continuousOn_univ.mp ((continuousOn_dslope (Filter.univ_mem (f:=𝓝 (0:ℂ)))).mpr
    ⟨hD.continuous.continuousOn,hD 0⟩), by rw [dslope_same,he.deriv]⟩

lemma lap_approx {ε : ℝ} (he : 0 < ε) : ∃ δ : ℝ, 0 < δ ∧ ∀ p : Momentum, physical p →
    (∀ i : Axis, ‖p i‖ ≤ δ) → ∀ M : Side, ‖divisor M p - (lengthSq p:ℂ)‖ ≤ ε * lengthSq p := by
  let g := dslope chip 0
  have ht (x : ℂ) : x * g x = chip x := by simpa only [sub_zero,chip_origin, smul_eq_mul,g] using sub_smul_dslope chip 0 x
  have hc : Continuous (fun x : ℂ => ‖g x‖^2) := chip_extends.1.norm.pow _
  obtain ⟨δ,hδ,h⟩ := Metric.continuous_iff.mp hc 0 ε he
  refine ⟨δ/2,half_pos hδ,fun p hp hx M => ?_⟩
  have h1 (i : Axis) : |‖g (narrow M p i)‖^2-1| ≤ ε := by
    have hr := h (narrow M p i) (by
      rw [dist_zero_right,narrow_apply, norm_div, Complex.norm_natCast]
      exact (div_le_self (norm_nonneg (p i)) (by exact_mod_cast M.property : (1:ℝ) ≤ M.val)).trans_lt
        ((hx i).trans_lt (half_lt_self hδ)))
    simpa only [Real.dist_eq,g,chip_extends.2,Complex.norm_I,one_pow] using hr.le
  have h2 i : ‖seedQ M p i‖^2=‖p i‖^2* ‖g (narrow M p i)‖^2 := by
    unfold seedQ; rw [←ht,norm_mul,norm_mul,← mul_assoc,narrow_apply,norm_div,Complex.norm_natCast,mul_div_cancel₀ _ (side_pos M).ne',mul_pow]
  rw [divisor_normSq _ hp,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]; unfold lengthSq; rw [← Finset.sum_sub_distrib,Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  simp_rw [h2,sub_eq_add_neg]
  apply Finset.sum_le_sum; intro i hi
  have hh : ‖p i‖^2 * ‖g (narrow M p i)‖^2 + -(‖p i‖^2) = ‖p i‖^2*(‖g (narrow M p i)‖^2-1) := by ring
  rw [hh,abs_mul,abs_of_nonneg (by positivity : 0≤‖p i‖^2),mul_comm ε]; exact mul_le_mul_of_nonneg_left (h1 i) (by positivity)

lemma divisor_lower (M : Side) {p : Momentum} (hp : p∈baseCube) :
    meter.low^2*lengthSq p ≤ ‖divisor M p‖ := (divisor_real_bounds M (base_subset_realCube zone_pos hp)).1.trans
      (Complex.re_le_norm _)
lemma divisor_upper (M : Side) {p : Momentum} (hp : p∈baseCube) :
    ‖divisor M p‖ ≤ meter.high^2*lengthSq p := by
  rw [divisor_normSq M hp.1,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  convert (divisor_real_bounds M (base_subset_realCube zone_pos hp)).2 using 1
  rw [divisor_normSq M hp.1,Complex.ofReal_re]

lemma lid_approx (v : Train j) {p : Momentum} {a : Axis} (hp : p∈baseCube) {δ : ℝ} (hδ : 0 < δ)
    (hd : δ ≤ domainRadius) (h : ∀ i, ‖p i‖ ≤ δ) : ‖v.lid a p - 1‖ ≤ (8:ℝ)*meter.high*δ*(j+4) := by
  have hv := v.drive_flip a (narrow v.mass p)
  rw [show star (narrow v.mass p)=narrow v.mass p from narrow_real v.mass hp.1] at hv
  unfold Train.lid; rw [show ‖(yen (v.drive a) (narrow v.mass p))-1‖ = |‖yen (v.drive a) (narrow v.mass p)‖-1| from ?_]
  · exact motor_quote hδ hd hp.1 h v a
  unfold yen; rw [← hv, Complex.star_def,Complex.mul_conj,← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (by rw [← Complex.sq_norm]; positivity : 0 ≤ Complex.normSq (v.drive a (narrow v.mass p)))] -- rw of 1 ambiguous

lemma relative_radius (k : ℝ) {ε : ℝ} (hε : 0 < ε) : ∃ δ : ℝ, 0 < δ ∧ ∀ (j : ℕ), 2 ≤ j → ∀ p ∈ baseCube, p≠0 →
    (∀ i, ‖p i‖ ≤ δ/(j+4)) → ∀ v : Train j, ∀ a : Axis, ‖v.levelD k a p*divisor 1 p - 1‖ ≤ ε := by
  let u := meter.high; have hm : 0 < u := meter.high_pos; let c := meter.low; have hc : 0 < c := meter.low_pos
  obtain ⟨C,hC,hB⟩ := drain_bound k
  let η := ε*c^2/6; have hη : 0 < η := by unfold η; positivity
  obtain ⟨δ₀,hδ₀,hq⟩ := lap_approx hη
  obtain ⟨δ,hδ,h1,h2,h3,h4⟩ : ∃ δ : ℝ, 0<δ ∧ δ≤min 1 domainRadius ∧ δ ≤ δ₀ ∧
      δ ≤ ε/(3*C*u^2*4) ∧ (u^2/c^2)*(8*u*δ) ≤ ε/3 := by
    let δ := min (min 1 (min δ₀ domainRadius)) (min (ε/(3*C*u^2*4)) ((ε/3)/(u^2/c^2*8*u)))
    have hD : δ ≤ min 1 (min δ₀ domainRadius) := min_le_left ..
    have hd : δ ≤ min (ε/(3*C*u^2*4)) ((ε/3)/(u^2/c^2*8*u)) := min_le_right ..
    refine ⟨δ,lt_min (by positivity [domainRadius_pos]) (by positivity),hD.trans ?_,hD.trans ((min_le_right ..).trans (min_le_left ..)),hd.trans (min_le_left ..),?_⟩
    · exact min_le_min le_rfl (min_le_right ..)
    rw [← mul_assoc,← mul_assoc]; exact (le_div_iff₀' (by positivity)).mp (hd.trans (min_le_right ..))
  refine ⟨δ,hδ,fun j hj p hp hn hR v a=>?_⟩
  let M := v.mass; let R : ℝ := (j+4:ℕ); let hM := side_pos M; have hR₀ : 1 ≤ R := by unfold R; norm_cast; omega
  have H₀ (i) : ‖p i‖ ≤ δ := (hR i).trans (by apply div_le_self hδ.le; have : (0:ℝ) ≤ j := Nat.cast_nonneg j; linarith)
  have hSq := lengthSq_pos hn
  have ht : c^2*lengthSq p ≤ ‖divisor M p‖ := divisor_lower M hp
  have hu : ‖divisor 1 p / divisor M p‖ ≤ u^2/c^2 := by
    rw [norm_div,div_le_div_iff₀ ((mul_pos (pow_pos hc 2) hSq).trans_le ht) (by positivity)]
    exact le_trans (mul_le_mul_of_nonneg_right (divisor_upper 1 hp) (sq_nonneg c)) (by unfold u c at *; nlinarith)
  have hr : ‖divisor 1 p / divisor M p - 1‖ ≤ ε/3 := by
    have hM (M : Side):= hq _ hp.1 (fun i=> (H₀ i).trans h2) M
    have he := norm_add_le (divisor 1 p - (lengthSq p:ℂ)) ((lengthSq p:ℂ) - divisor M p)
    rw [sub_add_sub_cancel,norm_sub_rev ((lengthSq p):ℂ)] at he
    rw [div_sub_one (norm_pos_iff.mp ((mul_pos (pow_pos hc 2) hSq).trans_le ht)), norm_div, div_le_iff₀ ((mul_pos (pow_pos hc 2) hSq).trans_le ht)]
    have h1 := hM 1; have h1' := hM M; have hw := mul_le_mul_of_nonneg_left ht (show 0≤ ε/3 from by positivity)
    apply (he.trans (add_le_add h1 h1')).trans ; unfold η; linarith
  have hmotor : ‖v.lid a p - 1‖ ≤ (8:ℝ)*u*δ := by
     have h0 (a) : ‖p a‖ ≤ δ/R := by unfold R; push_cast; exact hR a
     exact (lid_approx v (a:=a) hp (δ:=δ/R) (by positivity) ((div_le_self hδ.le hR₀).trans (h1.trans (min_le_right ..))) h0).trans_eq (by
       unfold R u; push_cast; field_simp) -- syntax
  have hD' : ‖divisor 1 p‖ ≤ meter.high^2*(4*δ) := (divisor_upper _ hp).trans (by
    apply mul_le_mul_of_nonneg_left _ (by positivity); unfold lengthSq
    calc
      _ ≤ ∑ i : Axis, δ := Finset.sum_le_sum fun i _ => (sq_le_sq₀ (norm_nonneg _) hδ.le|>.mpr (H₀ i)).trans (by nlinarith [show δ≤1 from h1.trans (min_le_left ..)])
      _ ≤ (4:ℝ)*δ := by simp [Axis])
  have hT : ‖v.drain k a p * divisor 1 p‖ ≤ ε/3 := by
    rw [norm_mul]; apply (mul_le_mul (hB _ hj _ hp _) hD' (norm_nonneg _) hC.le).trans
    have hh := (le_div_iff₀' (by positivity)).mp h3
    change C * (u^2 * (4*δ)) ≤ _; linarith
  rw [Train.pole_split,show (v.lid a p*(divisor M p)⁻¹+v.drain k a p)*divisor 1 p - 1 = (v.lid a p - 1)*(divisor 1 p / divisor M p) +
    (divisor 1 p / divisor M p - 1) + v.drain k a p * divisor 1 p from by unfold M; ring]
  apply (norm_add_le ..).trans ((add_le_add ((norm_add_le ..).trans (add_le_add (show _ ≤ ε/3 from ?_) hr)) hT).trans_eq (by ring))
  rw [norm_mul]; apply (mul_le_mul hmotor hu (norm_nonneg _) (by positivity)).trans; rwa [mul_comm]
end UV
end YM.Next.Free
