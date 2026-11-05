import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Pane.Mural
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Pane
open Filter Function Lattice Wilson RG RG.Supply Input Precision Org Tree Exterior Set
open Further.PhysicalPeriodLimitF933 Gauge Jacobi Macrame Macrame.Lace Polytrace Withdrawal Liquid Enamel Loom Matrix Finset
open Push Push.Uniform Shingle Pitch Extra.Iteration Extra.Iteration.Calibration Bid Bloch Laurent
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c C f F : Side} {P : Patch} {Z : KernelChoices} {T : RG.Stage} {n : ℕ}
    {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} (hC : C.val=c.val*n) (h₂ : 2 ≤ c.val)
local notation "L" => project (h:=h) (H:=H) hC h₂
variable (Q : Paintings.Supply G P Z T) (t : Forest (decreed h)) {p W : PathData G} {u : Dir G c → AxisChart G t}
local notation "R" => circuit (H:=H) hC h₂ t
variable {v : Dir G C→AxisChart G (circuit (H:=H) hC h₂ t)} (hv : Q.h.Service (S:=stepped Z H) (circuit (H:=H) hC h₂ t) T.clip p v)
    (hu : Critical (S:=stepped Z h) t T.clip p u)

lemma beat (x:Site c) (i : Site C) : cell x ((L).low.cut i)=cell (wrap C (n • Lattice.lift x)) i := by
  have he : (L).low.cut i=wrap c (Lattice.lift i):= by rw [← (wrap_lift i)]; change splitter _ _=_; rw [Macrame.branch, wrap_lift]
  rw [he,cell_wrap,cell_duality (n:=C),cell_wrap,← mode_scale]
  have hp : ((C.val:ℂ)⁻¹*n) = (c.val:ℂ)⁻¹ := by
    have hx : (C.val:ℂ)=(c.val:ℂ)*n := by rw [hC]; push_cast; rfl
    have hh : (n:ℂ)≠0 := by intro h; apply Bloch.side_ne C; rw [hx,h,mul_zero]
    field_simp
    rw [hx,mul_comm] -- edit
  unfold mon mode; congr 1
  -- sum arithmetic
  apply congr_arg
  refine Finset.sum_congr rfl fun i _=>?_
  simp only [reciprocal,Pi.smul_apply, smul_eq_mul,nsmul_eq_mul]; rw [← hp]; ring

lemma oscillate (x: Site c) (σ : TypeFace 1→G.ColorIndex→ℂ) : coverC (h:=h) (H:=H) hC h₂ (wave x σ)= wave (wrap C (n • Lattice.lift x)) σ := by
  ext i j
  change (cell x ((L).low.cut i.1)* σ i.2 j).re=(cell _ _*_).re
  rw [beat hC h₂]

section money
variable {Y : ℝ} {O : ChartRatio G} (hs : p.Bounds T.clip T.width T.paths Y) (hc : Q.bulletin h) (h' : Q.bulletin H) (ho : LocalRatio O)
variable {S' : Clip} {θ γ α : ℝ} (H' : FiniteBound (S:=stepped Z H) (circuit (H:=H) hC h₂ t) p W T.clip S' α O v θ γ Y) (hg : 0≤γ)
include hv hu ho H' hc hs h' hg
lemma surge (he : 0≤ θ) (h₁ : 1≤ Y) :
    0<Q.sights ∧ FiniteBound (S:=stepped Z h) t p W T.clip S' α O u (Q.allowance+θ) (min Q.sights γ) Y := by
  let A:=coverC (h:=h) (H:=H) hC h₂ (G:=G); let b:=onpass (Fitted.narrow L (G:=G)); let k:= n^4; let d:ℝ:=k
  have hA : 0<n := Nat.pos_of_mul_pos_left (show 0<c.val*n from hC ▸ C.pos)
  have hk:0<d:= by unfold d k; positivity
  have hD := compensate (b:=draft (c:=C) α W S') A (Eventually.of_forall (fun y=> pays_pile hC h₂ W S' y α (h:=h) (H:=H))) hk.ne' H'.classicalResult -- edit
  obtain ⟨u',hu',hP,hP'⟩:= Q.stationed hs hc t
  obtain ⟨v',hv',hQ,hQ'⟩:= Q.stationed hs h' R
  obtain ⟨hh,hN,-⟩:= Q.move hs ho hC h₂ hc h' 0 0 (by simp) (by simp)
  refine ⟨hh, Work.F05.hessian_pos hP' hP hu, fun s=> thermal_jet hP' hP hu s ho hs,hD.1,fun q i j s t' hh₁ hh₂=> ?_⟩
  let X:= wave i s; let y:= wave j t'; let x₁:= Inflation.lame i s; let x₂:=Inflation.lame j t'
  let t₀:= Lace.plain Z (h:=H)
  let M:= Calibration.determinant (S:=stepped Z h) t q p T.clip u O; let N:= Calibration.determinant (S:=stepped Z H) R t₀ p T.clip v O
  let f:= thermal (S:=stepped Z h) t q T.clip p u O; let g:= thermal (S:=stepped Z H) R t₀ T.clip p v O
  let u₀:=draft α W S' (c:=c); let v₀:=draft α W S' (c:=C)
  let val (u:Dir G c →ℝ):=(iteratedFDeriv ℝ 2 u 0 ![X,y]); let wide (j: Dir G C→ℝ):= iteratedFDeriv ℝ 2 j 0 ![A X,A y]
  have hx:= (Q.move hs ho hC h₂ hc h' x₁ x₂ (Inflation.score i s hh₁) (Inflation.score j t' hh₂)).2.2
  have hvv : ∀ f : Dir G C →ℝ, ContDiffAt ℝ ω f 0 → val (f ∘ A)=wide f := fun f hf=> by  unfold val wide; rw [jet_liner A f hf,ContinuousMultilinearMap.compContinuousLinearMap_apply]; apply congr_arg; ext1 j; fin_cases j <;> rfl
  have hr : wide v₀=d*val u₀ := by rw [← hvv _ H'.classicalResult]; exact congr($(hD.2 2) ![X,y])
  have hm : ContDiffAt ℝ ω M 0:= determinant_jet hP' hP hu q ho
  have hn : ContDiffAt ℝ ω N 0:= determinant_jet hQ' hQ hv.critical t₀ ho
  let I:= tint G (Body 1 c); let J:= tint G (Body 1 C)
  rw [← Q.declaration hs ho _ hc t q u hu, ← Q.declaration hs ho _ h' R t₀ v hv.critical] at hx
  have hX : val M= Paintings.Supply.declared t q u p T.clip O x₁ x₂:= Inflation.spectrum M X y (((show ContDiffAt ℝ ω M (I 0) from map_zero I ▸ hm).comp _ I.contDiff.contDiffAt))
  have hY : wide N= Paintings.Supply.declared R t₀ v p T.clip O (b x₁) (b x₂):= Inflation.spectrum N _ _ (((show ContDiffAt ℝ ω N (J 0) from map_zero J ▸ hn).comp _ J.contDiff.contDiffAt)) -- map_zero
  let r:ℝ:=(c.val:ℝ)^4; let r':ℝ := (C.val:ℝ)^4; have hε:0<r:=by unfold r; positivity
  change |val f-val u₀| ≤ _
  change |_ / r - _ / r'| ≤ _ at hx
  rw [← hX,← hY] at hx
  let p':= wrap C (n • Lattice.lift i); let q':= wrap C (n • Lattice.lift j)
  have hl : wide g - wide N=d*(val f-val M) := by
    have hp : (g-N) ∘ A =ᶠ[𝓝 0] d • (f-M) := (piles hC h₂ Q t hv hu).mono fun x hx=> by
      change g (A x)-N (A x) = d*(f x-M x); unfold g N f M thermal Calibration.determinant; change Precision.loop _ (lifting R (represent (A x)) (v (A x)))=d * Precision.loop p (lifting t (represent x) (u x)) at hx; simp only [add_sub_assoc, sub_self, add_zero]; exact hx
    have hj : ContDiffAt ℝ ω g 0:= H'.born t₀
    have hh : ContDiffAt ℝ ω f 0:= thermal_jet hP' hP hu q ho hs
    have hw : wide (g-N)=d* val (f-M) := by rw [← hvv (g-N) (hj.sub hn)]; exact congr($((compensate A hp hk.ne' (hj.sub hn)).2 2) ![X,y]) -- edit
    unfold val wide at hw; rw [iteratedFDeriv_sub_apply (hj.of_le le_top) (hn.of_le le_top),iteratedFDeriv_sub_apply (hh.of_le le_top) (hm.of_le le_top)] at hw; exact hw
  have hb : |wide g-wide v₀| ≤ (r'*θ*Y*Real.exp (-γ*C.val)):= by
    have hb:=H'.wave_price t₀ p' q' s t' hh₁ hh₂; rw [site_card,Nat.cast_pow] at hb; unfold wide; rw [show A X = wave p' s from oscillate (h:=h) (H:=H) hC h₂ .., show A y=wave q' t' from oscillate (h:=h) (H:=H) hC h₂ ..]; exact hb
  have heq : r'=d*r := by unfold r r' d k; rw [hC]; push_cast; ring
  let tmin:=Real.exp (-min Q.sights γ * c.val)
  have hX : |val M-wide N/d| ≤ r*Q.allowance*Real.exp (-Q.sights*c.val) := by
    rw [heq] at hx; rw [← div_div] at hx; rw [← sub_div,abs_div,abs_of_pos hε,div_le_iff₀ hε] at hx
    exact hx.trans_eq (by ring)
  have hY : |wide g/d-val u₀| ≤ r*θ*Y*tmin := by
    have hc : c.val ≤ C.val := le_trans (Nat.le_mul_of_pos_right _ hA) hC.symm.le
    have hh: Real.exp (-γ*C.val)≤tmin:= by
      apply Real.exp_monotone; exact (mul_le_mul_of_nonpos_left (by exact_mod_cast hc) (neg_nonpos.mpr hg)).trans (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right ..)) (Nat.cast_nonneg _)) -- ambiguous
    rw [← div_le_div_iff_of_pos_right hk] at hb -- edit
    rw [heq] at hb; rw [show val u₀=wide v₀/d from by rw [hr]; field_simp,← sub_div,abs_div,abs_of_pos hk]
    apply hb.trans; rw [show _*Real.exp _ /d=r*θ*Y*Real.exp (-γ*C.val) by field_simp]
    gcongr
  have he' : Real.exp (-Q.sights*c.val) ≤ tmin := Real.exp_monotone (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left ..)) (Nat.cast_nonneg _))
  rw [site_card,Nat.cast_pow,show val f-val u₀=(wide g/d-val u₀)+(val M-wide N/d) by field_simp; nlinarith only [hl]]
  refine (abs_add_le _ _).trans ((add_le_add hY hX).trans ?_); change _ ≤ r*_ *Y*tmin
  have hz : r*Q.allowance*Real.exp (-Q.sights*c.val) ≤ r*Q.allowance*Y*tmin := mul_le_mul
    (le_mul_of_one_le_right (mul_nonneg hε.le hN) h₁) he' (Real.exp_pos _).le (by positivity)
  linarith only [hz]
end money
end YM.PhysicalNext.Repeat.Pane
