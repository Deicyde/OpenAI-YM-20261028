import YM.RG08.Canon.Siren
/-! # Identification at one period INCLUDING the first-loop finite
 term. These use full rescaled step at any forest & period before images.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Canon
open Filter MeasureTheory YM.PertExtension.Series.Tested
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent Finset Next.Free Matrix FreeResolvent Reflect
open PertExtension.Series.Radial PertExtension.Chart PertExtension.GaussianScore
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {W Z : Air G}
lemma verse_zero (Q:Pot G 2)(Z:Air G)(n r : ℕ): stanza (sector Q Z n r) c (0:Link G c)=0 := by
  cases r
  · rw [sector, stanza_zero]; rfl
  rename_i k; rw [← zero_smul ℝ (0:Link G c),mnemonic]; simp
lemma excise_says (Q:Pot G 2)(Z:Air G)(q): sector Q (excise Z) q=sector Q Z q := by
  funext j; cases j with
  | zero=> rfl
  | succ j=> cases j <;> simp [sector,excise]
lemma token_change (h : Decked Z)(Q:Pot G 2)(t:ℝ)(x:Link G c) :
    t^2*(oblige Q Z 2 t x-oblige Q Z 2 t (0:Link G c)) = grand 4 (sector Q Z 0) c (t•x) + t^2*grand 2 (sector Q Z 1) c (t•x) := by
  simp_rw [excise_note Q Z]; rw [add_sub_add_right_eq_sub,mul_sub, ← loopCount Q 2 (excise_below h) (excise_heap Z) t x, ← loopCount Q 2 (excise_below h) (excise_heap Z) t 0,smul_zero]
  simp_rw [excise_says,verse_zero]; simp only [Finset.sum_const_zero,mul_zero,sub_zero]
  have ht : trimmed 2 0 = range (4+1) := by ext; unfold trimmed; simp; omega
  have hy : trimmed 2 1 = range (2+1) := by ext; unfold trimmed; simp; omega
  have hz : trimmed 2 2 = {0} := by ext; unfold trimmed; simp
  have hv (x:ℕ)(h:x≥3) : trimmed 2 x=∅:=eq_empty_of_forall_notMem fun j hP=>by have hg:=(mem_filter.mp hP).2; omega
  rw [show 2+2+1=5 by norm_num]; unfold grand; rw [Finset.sum_apply,Finset.sum_apply]
  norm_num [Finset.sum_range_succ,ht,hy,hz,hv]
  right; rw [sector, stanza_zero]; rfl


private lemma credits2 (V B : Link G c→ℝ)(x:Link G c)(hv : ContDiffAt ℝ ω V 0)(hb:ContDiffAt ℝ ω B 0)(n:ℕ):
   ink (fun t:ℝ=> V (t•x)+t^2*B (t•x)) n= jet V n x + if 2 ≤ n then jet B (n-2) x else 0 := by
  let f (t:ℝ):= V (t•x); let g (t:ℝ):= B (t•x); let U(t:ℝ):=t^2
  have ha : ContDiffAt ℝ ∞ g 0 := ((show ContDiffAt ℝ ω B ((0:ℝ)•x) by simpa using hb).comp (f:=fun t:ℝ=>t•x) _ (contDiffAt_id.smul contDiffAt_const)).of_le le_top
  have hh : ContDiffAt ℝ ∞ f 0 := ((show ContDiffAt ℝ ω V ((0:ℝ)•x) by simpa using hv).comp (f:=fun t:ℝ=>t•x) _ (contDiffAt_id.smul contDiffAt_const)).of_le le_top
  change ink (f+U*g) _=_; rw [ink_add hh (g:=U*g) ((contDiffAt_id.pow 2).mul ha),Pi.add_apply,show ink f n=_ from pulse_ray V n (hv.of_le le_top) x,show ink (U*g) n=_ from ink_t_pow g ha 2 n,show ink g (n-2)=_ from pulse_ray _ _ (hb.of_le le_top) x]
lemma stroke_sep (V B A S : Link G c→ℝ) (hv : ContDiffAt ℝ ω V 0)(hb:ContDiffAt ℝ ω B 0)(ha : ContDiffAt ℝ ω A 0)(hs : ContDiffAt ℝ ω S 0)
    (h : ∀ x:Link G c, Fit 5 (fun t:ℝ=>V (t•x)+t^2*B (t•x)) (fun t:ℝ=>A (t•x)+t^2*S (t•x))) :
    (∀ i, i≤4 → Tensor.coeff V i 0=Tensor.coeff A i 0) ∧ (∀ i,i≤2 → Tensor.coeff B i 0=Tensor.coeff S i 0) := by
  let ψ (V B:Link G c→ℝ) (x:Link G c) (t:ℝ):=V (t•x)+t^2*(B (t•x))
  have he (V B : Link G c→ℝ)(x:Link G c)(hv : ContDiffAt ℝ ω V 0)(hb : ContDiffAt ℝ ω B 0) : Aspiration (ψ V B x) (ink (ψ V B x)) := by
    let f(t:ℝ):=t • x; have hu' : ContDiffAt ℝ ω f 0:=contDiffAt_id.smul contDiffAt_const; have hu : f 0=0:=zero_smul ..
    exact ink_aspire (((hu.symm ▸ hv:ContDiffAt ℝ ω _ (f 0)).comp _ hu'|>.add ((contDiffAt_id.pow _).mul ((hu.symm ▸ hb:ContDiffAt ℝ ω _ (f 0)).comp _ hu'))).of_le le_top)
  have hp (x : Link G c)(n)(hn:n≤4) : jet V n x + (if 2 ≤ n then jet B (n-2) x else 0)= jet A n x + if 2 ≤ n then jet S (n-2) x else 0 := (credits2 _ _ x hv hb n|>.symm).trans ((aspiredV (h x) (he V B x hv hb) (he A S x ha hs) hn).trans (credits2 _ _ x ha hs n))
  have hh (x:Link G c)(i:ℕ)(hi:i≤2) : jet V (i+2) x=jet A (i+2) x ∧ jet B i x=jet S i x := by
    have ht:= hp x (i+2) (by omega); have hT:= hp ((2:ℝ)•x) (i+2) (by omega); simp only [Nat.le_add_left,add_tsub_cancel_right,if_pos,jet_smul,pow_add] at ht hT
    interval_cases i <;> norm_num at ht hT ⊢ <;> exact ⟨by linarith,by linarith⟩
  refine ⟨fun i hi=>?_,fun i hi=>?_⟩
  · apply Tensor.ext_diag _ _ (Tensor.coeff_symm (hv.of_le le_top)) (Tensor.coeff_symm (ha.of_le le_top)); funext x
    change jet V i x=jet A i x
    by_cases hi:i<2
    · simpa [show ¬ 2 ≤ i by omega] using hp x i (by omega)
    obtain ⟨j,rfl⟩:= Nat.exists_eq_add_of_le (not_lt.mp hi); rw [add_comm]; exact (hh x j (by omega)).1
  apply Tensor.ext_diag _ _ (Tensor.coeff_symm (hb.of_le le_top)) (Tensor.coeff_symm (hs.of_le le_top)); funext x; exact (hh x i hi).2
end YM.RG08.Canon
