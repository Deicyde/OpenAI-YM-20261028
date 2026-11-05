import YM.Push.ABSOLUTE_SUMS.Mixed

/-!
A finite loss in the real band: turn (sharper) size bounds and (much less sharp) high
same-amplitude derivative bounds into a proportional bound. Used *before* the reset root.
No demand on a continuation past the ends of the parameter interval.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InterpolatedSecantsFc
open Set Filter Function
open scoped Topology BigOperators ContDiff

theorem iteration_smooth {f : ℝ → ℝ} {x : ℝ} {n k j : ℕ} (h : ContDiffAt ℝ n f x) (he : k+j ≤ n) :
    ContDiffAt ℝ k (iteratedDeriv j f) x := by
  induction j generalizing k with
  | zero => exact h.of_le (by exact_mod_cast he : (k:WithTop ℕ∞) ≤ n)
  | succ j ih =>
    have h := ih (k:=k+1) (by omega)
    rw [iteratedDeriv_succ]
    exact h.derivWithin (by push_cast; rfl)

theorem affine_iterated (f : ℝ → ℝ) (u v x : ℝ) (j : ℕ) :
    iteratedDeriv j (fun t => f (u+v*t)) x = v^j * iteratedDeriv j f (u+v*x) := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ,iteratedDeriv_succ,funext ih,deriv_const_mul_field,
      show deriv (fun t => iteratedDeriv j f (u+v*t)) x = _ from deriv_comp_mul_left v (fun t => iteratedDeriv j f (u+t)) x,
      deriv_comp_const_add,smul_eq_mul,pow_succ,mul_assoc]

private theorem point_bound (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ {a b A : ℝ} {f : ℝ→ℝ},
    a<b → (∀ x∈Ioo a b, ContDiffAt ℝ j f x ∧ |f x| ≤ A) → ∃ x∈Ioo a b, (b-a)^j * |iteratedDeriv j f x| ≤ C*A := by
  induction j with
  | zero => exact ⟨1,zero_le_one,fun {a b A f} hab hf => by
      obtain ⟨z,hz,hz'⟩ := exists_between hab
      exact ⟨z,⟨hz,hz'⟩,by simpa using (hf z ⟨hz,hz'⟩).2⟩⟩
  | succ j ih =>
    obtain ⟨C,hC,H⟩ := ih
    refine ⟨6*3^j*C,by positivity,fun {a b A f} hab hf => ?_⟩
    let d := (b-a)/3
    have hd : 0<d := by unfold d; linarith
    have hh (u : ℝ) (hu : a ≤ u) (hv : u+d ≤ b) :
        ∃ x∈Ioo u (u+d), d^j * |iteratedDeriv j f x| ≤ C*A := by
      simpa using H (a:=u) (b:=u+d) (f:=f) (by linarith) (fun t ht =>
        let h := hf t (Ioo_subset_Ioo hu hv ht)
        ⟨h.1.of_le (Nat.cast_le.mpr (Nat.le_succ j)),h.2⟩)
    obtain ⟨l,hl,hL⟩ := hh a le_rfl (by unfold d; linarith)
    obtain ⟨r,hr,hR⟩ := hh (b-d) (by unfold d; linarith) (by linarith)
    rw [sub_add_cancel] at hr
    have hm : d ≤ r-l := by dsimp only [d] at *; linarith only [hr.1,hl.2]
    have hy t (ht : t ∈ Icc l r) := iteration_smooth (hf t ⟨hl.1.trans_le ht.1,ht.2.trans_lt hr.2⟩).1 (k:=1) (j:=j) (by omega)
    obtain ⟨t,ht,he⟩ := exists_deriv_eq_slope (iteratedDeriv j f) (a:=l) (b:=r) (by linarith)
      (continuousOn_of_forall_continuousAt fun t ht => (hy t ht).continuousAt) (fun t ht =>
      ((hy t (Ioo_subset_Icc_self ht)).differentiableAt (by simp)).differentiableWithinAt)
    have hz := mul_le_mul_of_nonneg_left (abs_sub (iteratedDeriv j f r) (iteratedDeriv j f l)) (pow_pos hd j).le
    refine ⟨t,⟨hl.1.trans ht.1,ht.2.trans hr.2⟩,?_⟩
    rw [iteratedDeriv_succ,he,abs_div,abs_of_pos (hd.trans_le hm),show b-a=3*d by dsimp [d]; ring,pow_succ,mul_pow]
    calc
      _ ≤ (3^j*d^j*(3*d)) * (|iteratedDeriv j f r - iteratedDeriv j f l|/d) := by gcongr
      _ = 3^j * 3 * (d^j * |iteratedDeriv j f r - iteratedDeriv j f l|) := by field_simp
      _ ≤ 3^j * 3 * (2*(C*A)) := by gcongr 3^j * 3 * ?_; linarith only [hz,hR,hL]
      _ = _ := by ring

private lemma inner_change {a b : ℝ} {f : ℝ→ℝ} {n k : ℕ} (hf : ∀ x∈Ioo a b, ContDiffAt ℝ n f x)
    (hk : k<n) {A : ℝ} (hA : ∀ x∈Ioo a b, |iteratedDeriv (k+1) f x| ≤ A) {x y : ℝ} (hx : x∈Ioo a b) (hy : y∈Ioo a b) :
    |iteratedDeriv k f x-iteratedDeriv k f y| ≤ |x-y| * A := by
  have hh z (hz : z∈Ioo a b) := (iteration_smooth (hf z hz) (k:=1) (j:=k) (by omega)).differentiableAt (by simp)
  have he := Convex.norm_image_sub_le_of_norm_deriv_le hh (by simpa [iteratedDeriv_succ] using hA)
    (convex_Ioo a b) hy hx
  simpa only [Real.norm_eq_abs,mul_comm A] using he

private lemma unit_price (q j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ {f : ℝ→ℝ} {A B : ℝ},
    (∀ x∈Ioo (0:ℝ) 1, ContDiffAt ℝ (j+q:ℕ) f x ∧ |f x| ≤ A ∧ |iteratedDeriv (j+q) f x| ≤ B) →
      ∀ x∈Ioo (0:ℝ) 1, |iteratedDeriv j f x| ≤ C*A+B := by
  induction q generalizing j with
  | zero => exact ⟨0,le_rfl,fun H x hx => by simpa using (H x hx).2.2⟩
  | succ q ih =>
    obtain ⟨C,hc,h⟩ := ih (j+1)
    obtain ⟨D,hd,h'⟩ := point_bound j
    refine ⟨C+D,add_nonneg hc hd,fun {f A B} H x hx => ?_⟩
    obtain ⟨y,hy,he⟩ := h' (b:=1) (f:=f) zero_lt_one (fun z hz => let Q := H z hz
                                         ⟨Q.1.of_le (Nat.cast_le.mpr (by omega)),Q.2.1⟩)
    rw [sub_zero,one_pow,one_mul] at he
    have hg : ∀ z∈ Ioo (0:ℝ) 1, |iteratedDeriv (j+1) f z| ≤ C*A+B :=
      h (fun z hz => (show j+(q+1)=j+1+q by omega) ▸ H z hz)
    have hb := (abs_nonneg _).trans (hg x hx)
    have hw := inner_change (fun z hz => (H z hz).1) (k:=j) (by omega) hg hx hy
    have hz : |x-y| ≤ 1 := abs_le.mpr ⟨by linarith [hx.1,hy.2],by linarith [hx.2,hy.1]⟩
    exact le_trans (by simpa using abs_add_le (iteratedDeriv j f x-iteratedDeriv j f y) (iteratedDeriv j f y)) (by nlinarith only [hw,he,hb,hz])

private lemma encloses {a b h : ℝ} (hh : 0 < h) (hw : h ≤ b-a) (x : ℝ) (hx : x ∈ Ioo a b) :
    ∃ y, a ≤ y ∧ y+h ≤ b ∧ x ∈ Ioo y (y+h) := by
  refine ⟨min (b-h) (max a (x-h/2)), le_min (by linarith) (le_max_left ..),
    by linarith only [min_le_left (b-h) (max a (x-h/2))], lt_of_le_of_lt (min_le_right ..) (max_lt hx.1 (by linarith)), ?_⟩
  exact sub_lt_iff_lt_add.mp (lt_min (by linarith only [hx.2]) (lt_of_lt_of_le (by linarith) (le_max_right ..)))

/-- Bound on the first derivative from real observations on a fixed interval and a coarser
high-derivative size payment. No continuity of the latter at the boundary needed. -/
theorem interpolation (n : ℕ) (hn : 1 ≤ n) : ∃ C : ℝ, 0 ≤ C ∧ ∀ {a b h A B : ℝ} {f : ℝ→ℝ}, 0<h → h≤ b-a →
    (∀ x∈Ioo a b, ContDiffAt ℝ n f x ∧ |f x| ≤ A ∧ |iteratedDeriv n f x| ≤ B) →
      ∀ x∈Ioo a b, |deriv f x| ≤ C*A/h + h^(n-1)*B := by
  obtain ⟨C,hc,H⟩ := unit_price (n-1) 1
  refine ⟨C,hc,fun {a b h A B f} hh hw hf x hx => ?_⟩
  obtain ⟨y,hy,hb,hx'⟩ := encloses hh hw x hx
  let u (z : ℝ) := y+h*z
  have hm z (hz : z∈Ioo (0:ℝ) 1) := hf (u z) ⟨by dsimp only [u]; nlinarith only [hy,hz.1,hh], by dsimp only [u]; nlinarith only [hz.2,hb,hh]⟩
  obtain ⟨z,hz,rfl⟩ : ∃ z∈Ioo (0:ℝ) 1, u z=x := ⟨(x-y)/h,⟨by exact div_pos (sub_pos.mpr hx'.1) hh, by rw [div_lt_one hh]; linarith [hx'.2]⟩,
    by unfold u; field_simp; ring⟩
  rw [show 1+(n-1) = n by omega] at H
  have he := H (A:=A) (B:=h^n*B) (f:=f ∘ u) (fun z hz => ?_) z hz
  · change |iteratedDeriv 1 (fun i => f (y+h*i)) z| ≤ _ at he
    rw [affine_iterated,pow_one,iteratedDeriv_one,abs_mul,abs_of_pos hh,show n=(n-1)+1 by omega,pow_succ] at he
    rw [← le_div_iff₀' hh,add_div] at he
    exact he.trans_eq (by field_simp)
  obtain ⟨h1,h2,h3⟩ := hm z hz
  refine ⟨h1.comp z (by unfold u; fun_prop),h2,?_⟩
  change |iteratedDeriv n (fun i => f (y+h*i)) z| ≤ _
  rw [affine_iterated,abs_mul,abs_of_pos (pow_pos hh _)]
  exact mul_le_mul_of_nonneg_left h3 (pow_pos hh _).le
end YM.PhysicalNext.InterpolatedSecantsFc
