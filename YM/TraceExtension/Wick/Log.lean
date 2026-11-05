import YM.TraceExtension.Wick.Gain

/-! No such expansion can have log-suppressed leading order. -/
set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension.Wick
open Function Set Filter Asymptotics
open scoped Topology BigOperators Classical

private abbrev Tag := ℤ × ℕ
private def degree (t : Tag) : Lex (ℝ × ℕ) := toLex (((1/2:ℝ)^(8+t.1)), t.2+2)
private def P (t : Tag) (n : ℕ) : ℝ := (ofLex (degree t)).1^n * (n:ℝ)^(t.2+2)
private def act (t:Tag) := (Real.log (1/2))^(t.2+2)
private lemma increases : Function.Injective degree := by
    rintro ⟨i,v⟩ ⟨s,t⟩ H
    change toLex _=toLex _ at H; apply toLex.injective at H
    simp only [Prod.mk.injEq,add_left_inj] at H; obtain ⟨h,rfl⟩:=H; congr 1
    rcases lt_trichotomy i s with hk|hk|hk
    · exact False.elim ((zpow_lt_zpow_right_of_lt_one₀ (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1) (add_lt_add_right hk 8)).ne h.symm)
    · exact hk
    exact False.elim ((zpow_lt_zpow_right_of_lt_one₀ (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1) (add_lt_add_right hk 8)).ne h)
private lemma negligible (t : Tag) (h : (ofLex (degree t)).1 < 1) : Tendsto (P t) atTop (𝓝 0) := by
    have hp : |(ofLex (degree t)).1| < 1 := by rwa [abs_of_nonneg (by dsimp [degree]; positivity)]
    exact (tendsto_pow_const_mul_const_pow_of_abs_lt_one _ hp).congr fun _=> mul_comm ..
private lemma decisive (t : Tag) (h : 1 ≤ (ofLex (degree t)).1) : Tendsto (P t) atTop atTop :=
    tendsto_atTop_mono (fun n:ℕ => show (n:ℝ)^(t.2+2) ≤ P t n from le_mul_of_one_le_left (by positivity) (one_le_pow₀ h))
        ((tendsto_pow_atTop (n:=t.2+2) (by omega)).comp tendsto_natCast_atTop_atTop)
private lemma supersedes {x y} (h : degree x<degree y) : Tendsto (fun n=> P x n / P y n) atTop (𝓝 0) := by
    let a:= (ofLex (degree x)).1; let b:=(ofLex (degree y)).1
    have ha : 0<a := by unfold a degree; dsimp; positivity
    have hb : 0<b := by unfold b degree; dsimp; positivity
    let i:=x.2+2; let j:=y.2+2
    have he : a<b ∨ a=b ∧ i<j := Prod.lex_def.mp h
    rcases he with hh|⟨hh,hu⟩
    · have hv : Tendsto (fun n:ℕ=> ((n:ℝ)^j)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp
        ((tendsto_pow_atTop (n:=j) (by unfold j; omega)).comp tendsto_natCast_atTop_atTop)
      have hg : |a/b|<1 := by rw [abs_of_nonneg (by positivity)]; exact (div_lt_one hb).mpr hh
      have ht := (tendsto_pow_const_mul_const_pow_of_abs_lt_one i hg).mul hv; rw [zero_mul] at ht; apply ht.congr; intro t; dsimp only [P]; unfold a b i j; rw [div_pow]; ring
    have hv : Tendsto (fun n:ℕ=> ((n:ℝ)^(j-i))⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp
      ((tendsto_pow_atTop (n:=j-i) (by omega)).comp tendsto_natCast_atTop_atTop)
    refine hv.congr' ?_; filter_upwards [eventually_gt_atTop 0] with n hn; change _=a^n*(n:ℝ)^i/(b^n*n^j); rw [hh];
    rw [show (n:ℝ)^j=n^(j-i)* (n:ℝ)^i by rw [← pow_add]; congr; omega]; field_simp

private def life (n : ℕ) := (1/2:ℝ)^n
private def share (s : ℝ) := s^8*Real.log (s⁻¹)^2
private lemma singleValue (t : Tag) (n) : share (life n) * joint t.1 t.2 (life n) = act t*P t n := by
    let r : ℝ := 1/2
    have h : 0<r := by unfold r; norm_num
    unfold joint tile; rw [fill_at (show 0<life n from pow_pos h _)]
    simp only [share, Real.log_inv, sq, neg_mul_neg,P,degree, ofLex_toLex,act, life, Real.log_pow,mul_pow]
    -- x^n commutes with zpow
    have he (a:ℤ) : (r^n)^a=(r^a)^n := by rw [← zpow_natCast r n, ← zpow_natCast (r^a) n, ← zpow_mul,← zpow_mul,mul_comm]
    rw [zpow_add₀ (ne_of_gt h),mul_pow,he, show r^(8:ℤ)=r^(8:ℕ) from zpow_natCast .., ← pow_mul, ← pow_mul r, Nat.mul_comm (8:ℕ) n]
    ring
private lemma board_limit {u} (hu : u∈ board) {A : ℝ}
    (hx : Tendsto (fun n=> share (life n)*u (life n)) atTop (𝓝 A)) : A=0 := by
    let t (x : Tag) := joint x.1 x.2
    have he : u ∈ LinearMap.range (Finsupp.linearCombination ℝ t) := by
        rw [Finsupp.range_linearCombination];
        refine Submodule.span_mono (s:={f:ℝ→ℝ|∃ a k,f=joint a k}) ?_ hu
        rintro f ⟨a,k,rfl⟩; exact ⟨⟨a,k⟩,rfl⟩
    obtain ⟨g,hg⟩:=he
    let F (x : Tag) := g x * act x
    have hy n : share (life n)*u (life n)=∑ x∈g.support,F x*P x n:= by
        rw [← hg,Finsupp.linearCombination_apply,Finsupp.sum,Finset.sum_apply, Finset.mul_sum];
        apply Finset.sum_congr rfl; intro x h; change share _ * (g x*joint x.1 x.2 _) = _
        unfold F; rw [mul_left_comm, singleValue x, mul_assoc]
    simp_rw [hy] at hx
    rcases g.support.eq_empty_or_nonempty with h|h
    · exact tendsto_nhds_unique hx (by simp [h])
    obtain ⟨k,hk,hP⟩:= Finset.exists_max_image _ degree h
    by_cases he : (ofLex (degree k)).1 < 1
    · suffices h : Tendsto (fun n=> ∑ x∈g.support, F x * P x n) atTop (𝓝 (∑ x ∈g.support,(0:ℝ))) by
        simp only [Finset.sum_const_zero] at h; exact tendsto_nhds_unique hx h
      apply tendsto_finsetSum _ fun i hi=> ?_
      have hb : (ofLex (degree i)).1 ≤ (ofLex (degree k)).1 := by
        -- lex
        rcases (hP i hi).eq_or_lt with H|H
        · rw [H]
        rcases Prod.lex_def.mp H with hb|⟨hb,hc⟩
        · exact hb.le
        exact hb.le
      simpa only [mul_zero] using (negligible _ (hb.trans_lt he)).const_mul (F i)
    have hp := hx.mul (tendsto_inv_atTop_zero.comp (decisive _ (le_of_not_gt he))); rw [mul_zero] at hp
    have hk' : F k ≠ 0 := mul_ne_zero (Finsupp.mem_support_iff.mp hk) (pow_ne_zero _ ((Real.log_neg (by norm_num : (0:ℝ)<1/2) (by norm_num)).ne))
    let v (i : Tag) := if i=k then F k else 0
    have hr : Tendsto (fun n=>∑ x∈g.support,F x*(P x n/P k n)) atTop (𝓝 (∑ i∈g.support,v i)) := by
        apply tendsto_finsetSum _ fun i hi=> ?_
        by_cases ht:i=k
        · subst i; apply tendsto_const_nhds.congr';
          filter_upwards [eventually_gt_atTop 0] with n hn; rw [div_self (by dsimp [P,degree]; positivity : P k n ≠ 0)]; simp [v]
        have hL := (supersedes (lt_of_le_of_ne (hP i hi) (increases.ne ht))).const_mul (F i); simpa only [v,if_neg ht,mul_zero] using hL
    have hs : ∑ i ∈g.support,v i=F k := by simp [v,hk];
    exact False.elim (hk' (hs ▸ tendsto_nhds_unique_of_eventuallyEq hr hp (Eventually.of_forall (fun n => by simp_rw [Finset.sum_mul,div_eq_mul_inv,mul_assoc]; rfl))))

lemma no_powerlog {f : ℝ→ℝ} {A : ℝ} (hp : AtOrder f 0) (ht : Tendsto (fun s=> (s^8 * (Real.log s⁻¹)^2)*f s) past (𝓝 A)) : A=0 := by
    obtain ⟨u,w,h⟩:=hp
    apply board_limit w
    have he : Tendsto life atTop past := tendsto_nhdsWithin_iff.mpr ⟨tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num), Eventually.of_forall fun i=> by change 0<life i; unfold life; positivity⟩
    have hh := ht.comp he
    have hy (n) : share (life n)=act ⟨0,0⟩*P ⟨0,0⟩ n := by
       rw [← singleValue]; simp [joint,tile]
    have hv : Tendsto (fun n=> share (life n)) atTop (𝓝 0) := by
        simp_rw [hy]; simpa only [mul_zero] using (negligible ⟨0,0⟩ (by norm_num [degree])).const_mul (act ⟨0,0⟩)
    have hr : Tendsto (fun n=> share (life n)*(f-u) (life n)) atTop (𝓝 0) := by
        apply ((isBigO_of_le atTop (f:=fun n=> share (life n)) (g:=fun n=> share (life n)) (fun _=> le_rfl)).mul (h.comp_tendsto he)).trans_tendsto
        simpa only [tile,zpow_zero, Function.comp_apply,mul_one] using hv
    have hq:= hh.sub hr; rw [sub_zero] at hq; apply hq.congr; intro n; change share _ * f _ - share _ * (f _- u _)=_; ring
end YM.TraceExtension.Wick
