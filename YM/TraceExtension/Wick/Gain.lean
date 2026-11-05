import YM.TraceExtension.Wick.Expansion

/-! Bootstrapping the polylog class: integration by a comparison avoiding
any series summability assumptions. -/
set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension.Wick
open Set Filter Function Asymptotics Metric
open scoped Topology BigOperators Classical

lemma tile_d (a : ℤ) (x : ℝ) (hx : 0<x) : HasDerivAt (tile a) (a * x^(a-1)) x := by
    apply (hasDerivAt_zpow a x (Or.inl hx.ne')).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hx] with x hx; rw [tile,fill_at hx]
lemma log_tile (k : ℕ) (x : ℝ) (hx : 0<x) : HasDerivAt (joint 0 (k+1)) ((k+1:ℝ)*Real.log x^k*x⁻¹) x := by
    have he := (Real.hasDerivAt_log hx.ne').pow (k+1); simp only [Nat.add_one_sub_one,Nat.cast_add,Nat.cast_one] at he
    apply he.congr_of_eventuallyEq; filter_upwards [lt_mem_nhds hx] with i hi; simp [joint,tile,fill_at hi]

def integrates (f p : ℝ→ℝ) := ∀ x : ℝ, 0<x → HasDerivAt p (f x) x
lemma integrate_joint (a : ℤ) (k : ℕ) : ∃ p∈board, integrates (joint a k) p := by
    rcases eq_or_ne a (-1) with h|h
    · subst a; refine ⟨(↑k+1:ℝ)⁻¹ • joint 0 (k+1),board.smul_mem _ (jointBoard _ _),fun x hx=> ?_⟩
      have he : (↑k+1:ℝ) ≠ 0 := by positivity
      convert! ((log_tile k x hx).const_smul (↑k+1:ℝ)⁻¹) using 1; simp [joint,tile,fill_at hx]; field_simp
    let b := a+1; let c : ℝ := b
    have hc : c≠0 := Int.cast_ne_zero.mpr (show b≠0 by unfold b; omega)
    induction k with
    | zero=>
      refine ⟨c⁻¹ • tile b,board.smul_mem _ (tileBoard _),fun x hx=>?_⟩
      convert! ((tile_d b x hx).const_smul c⁻¹) using 1; simp only [joint,tile, fill_at hx,pow_zero,mul_one, smul_eq_mul,show b-1=a by omega]; rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    | succ k ih=>
      obtain ⟨p,P,t⟩ := ih; let u : ℝ := k+1
      let g := tile b * joint 0 (k+1)
      refine ⟨c⁻¹ • (g-u • p),board.smul_mem _ (board.sub_mem (board_mul _ _ (tileBoard b) (jointBoard _ _)) (board.smul_mem _ P)), fun x hx=>?_⟩
      have ht := ((((tile_d b x hx).mul (log_tile k x hx)).sub ((t x hx).const_smul u)).const_smul c⁻¹)
      convert! ht using 1
      simp only [joint,tile,fill_at hx,smul_eq_mul, zpow_zero, one_mul,show b-1=a by omega]; dsimp only [u]; change _= c⁻¹ * ((c*_*_+_)-_); rw [show x^b=x^a*x from zpow_add_one₀ hx.ne' _]; field_simp; ring
lemma integrate_poly (f) (h : f∈board) : ∃ p∈board, integrates f p := by
    unfold board at h
    induction h using Submodule.span_induction with
    | mem x hx=> obtain ⟨a,b,rfl⟩:=hx; exact integrate_joint ..
    | zero=> exact ⟨0,board.zero_mem,fun x _=>hasDerivAt_const ..⟩
    | add x y _ _ hx hy=> obtain ⟨p,P,h⟩:=hx; obtain ⟨q,Q,t⟩:=hy; exact ⟨p+q,board.add_mem P Q,fun x hx=>(h x hx).add (t x hx)⟩
    | smul a x _ hx => obtain ⟨p,P,h⟩:=hx; exact ⟨a • p,board.smul_mem a P,fun x hx=> (h x hx).const_smul a⟩

private lemma monotone_from (f g : ℝ→ℝ) (b : ℝ) (h : ∀ x∈Ioo 0 b, HasDerivAt f (g x) x ∧ 0≤g x) : MonotoneOn f (Ioo 0 b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioo ..)
    · exact fun x hx=> (h _ hx).1.continuousAt.continuousWithinAt
    · rw [isOpen_Ioo.interior_eq]; exact fun x hx=> (h x hx).1.differentiableAt.differentiableWithinAt
    rw [isOpen_Ioo.interior_eq]; intro x hx; rw [(h _ hx).1.deriv]; exact (h _ hx).2

lemma mostly_lt {b : ℝ} (hb : 0 < b) : ∀ᶠ x in past, x∈ Ioo (0:ℝ) b := by
    filter_upwards [mostly,(gt_mem_nhds hb).filter_mono nhdsWithin_le_nhds] with k hk ht using ⟨hk.1,ht⟩
private lemma base_and_tail (f g : ℝ → ℝ) {k : ℤ} (hk : k≠-1) (h : integrates g f) (hp : g=O[past] tile k) :
    ∃ b : ℝ, 0<b ∧ ∃ A : ℝ, MonotoneOn (fun x => A*x^(k+1)+f x) (Ioo 0 b) ∧ MonotoneOn (fun x=> A*x^(k+1)-f x) (Ioo 0 b) := by
    obtain ⟨C,hC,hk'⟩ := isBigO_iff'.mp hp
    obtain ⟨b,hb,H⟩:= Metric.nhdsWithin_basis_ball.eventually_iff.mp hk'
    let A := C/((k:ℝ)+1); have ha : (k:ℝ)+1≠0 := by exact_mod_cast (show k+1≠0 by omega)
    have he (x : ℝ) (h : 0<x) : HasDerivAt (fun x:ℝ=> A*x^(k+1)) (C*x^k) x := by
       convert! ((hasDerivAt_zpow (k+1) x (Or.inl h.ne')).const_mul A) using 1; simp [A,← mul_assoc,ha]
    have hv x (hh:x∈ Ioo 0 b) : ‖g x‖≤ C*x^k := by
        have hp : x∈ball (0:ℝ) b ∩ Ioi 0 := ⟨Metric.mem_ball.mpr (by rw [Real.dist_eq,sub_zero,abs_of_pos hh.1]; exact hh.2), hh.1⟩
        have hz := H hp; rwa [tile,fill_at hh.1, Real.norm_of_nonneg (zpow_nonneg hh.1.le _)] at hz
    exact ⟨b,hb,A,monotone_from _ _ b (fun x hx=> ⟨(he x hx.1).add (h x hx.1),by have he := (abs_le.mp (hv _ hx)).1; linarith⟩),monotone_from _ _ b (fun x hx=> ⟨(he x hx.1).sub (h x hx.1),sub_nonneg.mpr (abs_le.mp (hv _ hx)).2⟩)⟩

private lemma valley (u : ℝ→ℝ) (s : ℝ) (hs : 0<s) (hm : MonotoneOn u (Ioo 0 s))
    (hb : BddBelow (u '' Ioo 0 s)) : ∃ t : ℝ,Tendsto u past (𝓝 t) := by
    let t:= sInf (u '' Ioo 0 s); refine ⟨t,tendsto_order.mpr ⟨fun b hh=> ?_,fun b hh=>?_⟩⟩
    · exact (mostly_lt hs).mono fun i hi=> lt_of_lt_of_le hh (csInf_le hb (mem_image_of_mem u hi))
    obtain ⟨a,⟨w,hv,rfl⟩,hA⟩:= exists_lt_of_csInf_lt ((nonempty_Ioo.mpr hs).image u) hh
    exact (mostly_lt hv.1).mono fun i hi=> lt_of_le_of_lt (hm ⟨hi.1,hi.2.trans hv.2⟩ hv hi.2.le) hA

private lemma remainder_o (f g : ℝ→ℝ) {k : ℤ} (hk : k≠-1) (h : integrates g f) (hp : g=O[past] tile k) : AtOrder f (k+1) := by
    obtain ⟨b,hb,A,hB,hA⟩ := base_and_tail _ _ hk h hp
    let a:= b/2; have ha : a∈ Ioo 0 b:= ⟨half_pos hb,half_lt_self hb⟩
    let u (x:ℝ) := A*x^(k+1)+f x; let v (x:ℝ):=A*x^(k+1)-f x
    have he₁ (x) (hx:x∈ Ioo 0 a) : u x ≤ u a := hB ⟨hx.1,hx.2.trans ha.2⟩ ha hx.2.le
    have he₂ (x) (hx:x∈ Ioo 0 a) : v x ≤ v a := hA ⟨hx.1,hx.2.trans ha.2⟩ ha hx.2.le
    let d := k+1; rcases lt_or_gt_of_ne (show d≠0 by unfold d; omega) with hy|hy
    · let C:=|A| + |u a| + |v a|
      apply cost_order; refine isBigO_iff.mpr ⟨C,?_⟩
      filter_upwards [mostly_lt ha.1,mostly] with x hx hv
      rw [tile,fill_at hx.1,Real.norm_of_nonneg (zpow_nonneg hx.1.le d),Real.norm_eq_abs];
      have hp : 1≤x^d := by simpa only [zpow_zero] using zpow_le_zpow_right_of_le_one₀ hx.1 hv.2.le hy.le
      have hz := (abs_le.mp (show |A*x^d|≤ |A| * x^d by rw [abs_mul,abs_of_nonneg (show 0 ≤ x^d by linarith)])).1
      have hs : u a ≤ |u a| *  x^d := (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hp)
      have hw : v a ≤ |v a| *  x^d := (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hp)
      have hF := (he₁ x hx).trans hs; have hG := (he₂ x hx).trans hw; unfold C; change |f x| ≤ _ * x^d
      have h₁ : A*x^d+f x=u x:=rfl; have h₂ : A*x^d-f x=v x:=rfl; apply abs_le.mpr; constructor <;> linarith [mul_nonneg (abs_nonneg (u a)) (show 0 ≤ x^d by linarith),mul_nonneg (abs_nonneg (v a)) (show 0 ≤ x^d by linarith)]
    have hN : Tendsto (fun x:ℝ=> A*x^d) past (𝓝 0) := by
        have hx : d.toNat≠0 := by omega
        simp_rw [show ∀ x:ℝ, x^d=x^(d.toNat) from fun x=> by rw [← zpow_natCast, Int.toNat_of_nonneg hy.le] ]
        simpa [hx] using ((show Continuous (fun x:ℝ=> A*x^d.toNat) by fun_prop).tendsto 0).mono_left (nhdsWithin_le_nhds (s:=Ioi 0))
    have hc : BddBelow (u '' Ioo 0 a) := by
        refine ⟨-(|A| * a^d)*2-v a,?_⟩
        rintro y ⟨x,hx,rfl⟩
        have h : |A*x^d|≤|A| * a^d := by rw [abs_mul,abs_of_nonneg (zpow_nonneg hx.1.le d)]; apply mul_le_mul_of_nonneg_left (zpow_le_zpow_left₀ hy.le hx.1.le hx.2.le) (abs_nonneg _)
        have he : A*x^d-f x≤v a := he₂ x hx
        change _ ≤ A*x^d+_; linarith [(abs_le.mp h).1]
    obtain ⟨t,hh⟩:= valley u a ha.1 (fun _ hx _ hv hs=> hB ⟨hx.1,hx.2.trans ha.2⟩ ⟨hv.1,hv.2.trans ha.2⟩ hs) hc
    have ht : Tendsto v past (𝓝 (-t)) := by
       have he := (hN.add hN).sub hh; rw [add_zero,zero_sub] at he; refine he.congr fun x=> ?_; change _- (A*x^d+f x)=_; unfold v; ring
    refine ⟨(fun _=>t),?_,isBigO_iff.mpr ⟨A,?_⟩⟩
    · convert board.smul_mem t one_board using 1; ext; simp
    filter_upwards [mostly_lt ha.1] with x hx
    have hu : t≤u x := le_of_tendsto hh ((mostly_lt hx.1).mono fun y hy => hB ⟨hy.1,hy.2.trans (hx.2.trans ha.2)⟩ ⟨hx.1,hx.2.trans ha.2⟩ hy.2.le)
    have hv : -t≤ v x := le_of_tendsto ht ((mostly_lt hx.1).mono fun y hy => hA ⟨hy.1,hy.2.trans (hx.2.trans ha.2)⟩ ⟨hx.1,hx.2.trans ha.2⟩ hy.2.le)
    rw [tile,fill_at hx.1,Real.norm_of_nonneg (zpow_nonneg hx.1.le d),Real.norm_eq_abs]; apply abs_le.mpr; dsimp only [u,v] at *; simp only [Pi.sub_apply]; constructor <;> linarith

lemma primitives (f g : ℝ→ℝ) {k : ℤ} (hk : k≠ -1) (h : integrates g f) (hp : AtOrder g k) : AtOrder f (k+1) := by
    obtain ⟨p,x,hp⟩ := hp; obtain ⟨z, hz, ht⟩ := integrate_poly _ x
    have he : integrates (g-p) (f-z) := fun x hx=> (h x hx).sub (ht x hx)
    have hv : AtOrder (f-z+z) (k+1) := (remainder_o _ _ hk he hp).plus (own hz _);
    rwa [sub_add_cancel] at hv
end YM.TraceExtension.Wick
