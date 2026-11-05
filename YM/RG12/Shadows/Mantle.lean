import YM.RG12.Shadows.Display
/-! Pack derivative process. On these first two clocks exactly (reserved sign purchases).
One-variable steering via panel, station can demand more differentiated E by replacing here. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Shadows
open Set Metric Filter Function ConnectedActivityE6 ConnectedActivityE6.Blaze
open scoped ContDiff Topology BigOperators Classical
section
variable {E F:Type} [NormedAddCommGroup E] [NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
lemma iter_scale (f:E→F)(s:ℝ){n:ℕ}(hf:ContDiffAt ℝ n f 0): iteratedFDeriv ℝ n (fun y:E=> f (s • y)) 0 = (s^n) • iteratedFDeriv ℝ n f 0:=by
   let L:= s • ContinuousLinearMap.id ℝ E; have h0:L 0=(0:E):= map_zero L
   change iteratedFDeriv ℝ n (f ∘ L) _=_; rw [Push.Uniform.iter_lin_at (h0.symm ▸ hf),h0]; ext v
   simpa only [smul_apply,ContinuousMultilinearMap.compContinuousLinearMap_apply,L, ContinuousLinearMap.id_apply,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using! (iteratedFDeriv ℝ n f 0).map_smul_univ (fun _=>s) v
lemma iter_neg (f:E→F){n:ℕ}(hf:ContDiffAt ℝ n f 0):iteratedFDeriv ℝ n (fun y:E=> f (-y)) 0 = ((-1:ℝ)^n) • iteratedFDeriv ℝ n f 0:= by simpa only [neg_one_smul] using iter_scale f (-1) hf
end
section
variable {R:Haze}{n:ℕ}{p q:ℝ}{I E F:ℕ→Type} [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℝ (E i)][∀ i,NormedAddCommGroup (F i)][∀ i,NormedSpace ℝ (F i)]
abbrev Counter (I E F:ℕ→Type) := ∀ i:ℕ,I i→E i→F i
def Smooths (n:ℕ)(f:Counter I E F):Prop:= ∀ᶠ i:ℕ in atTop,∀ j:I i,ContDiffAt ℝ (n:WithTop ℕ∞) (f i j) 0
lemma Smooths.mono {f:Counter I E F}(h:Smooths n f){m:ℕ}(hm:m≤n):Smooths m f:= Filter.Eventually.mono h fun _ hi j=> (hi j).of_le (Nat.cast_le.mpr hm)
-- Gains on n-th exactly.Can include θ^n explicitly in supplied operands.
def Flares (R:Haze)(n:ℕ)(p:ℝ)(f: Counter I E F) := Keeps R p I (fun i j=> normJ n (f i j) 0)
namespace Flares
variable {f g: Counter I E F}(h:Flares R n p f)
include h
lemma mono (hp:q≤p):Flares R n q f:= by obtain ⟨v,ha,hb⟩:=h; exact ⟨_,ha.slower hp,hb⟩
lemma same (he:∀ᶠ i:ℕ in atTop,∀ j,normJ n (g i j) 0 ≤ normJ n (f i j) 0):Flares R n p g:= Keeps.assures h (he.mono fun i hi j=> by simpa only [abs_of_nonneg (norm_nonneg _)] using! hi j)
lemma sameZero (he:∀ᶠ i:ℕ in atTop,∀ j, g i j =ᶠ[𝓝 0] f i j):Flares R n p g:= h.same (he.mono fun i hi j=> by unfold normJ; rw [((hi j).iteratedFDeriv n (𝕜:=ℝ)).eq_of_nhds])
lemma assumes :∃ w:ℕ→ℝ, Charges R p w∧∀ᶠ i:ℕ in atTop,∀ j,normJ n (f i j) 0 ≤ w i:=by obtain ⟨v,ha,hb⟩:=h; exact ⟨_,ha,hb.mono fun i hi j=> (le_abs_self _).trans (hi j)⟩
omit h in
lemma mk {w:ℕ→ℝ}(hr: Charges R p w)(hf:∀ᶠ i:ℕ in atTop,∀ j, normJ n (f i j) 0 ≤ w i):Flares R n p f:= ⟨_,hr,hf.mono fun i hi j=>by simpa only [abs_of_nonneg (norm_nonneg _)] using! hi j⟩
lemma flip (he:Smooths n f): Flares R n p (fun i j y=> f i j (-y)):= by refine h.same (Eventually.mono he fun i hi j=>?_); simp [normJ,iter_neg _ (hi j),norm_smul]
lemma adds (hg:Flares R n p g)(hh:Smooths n f)(hk:Smooths n g):Flares R n p (f+g):=by
  obtain ⟨v,hv,H⟩:=h.assumes; obtain ⟨w,hw,hG⟩:=hg.assumes; refine mk (hv.add hw) ?_
  filter_upwards [hh,hk,H,hG] with i ha hb hc hd j
  change ‖iteratedFDeriv ℝ _ (f i j+g i j) 0‖ ≤ _; rw [iteratedFDeriv_add_apply (ha j) (hb j)]
  exact (norm_add_le ..).trans (add_le_add (hc j) (hd j))
lemma scales {v:ℕ→ℝ}(hv:Charges R q v)(hh:Smooths n f):Flares R n (p+q) (fun i=> v i • f i):=by
  obtain ⟨w,ha,hF⟩:=h.assumes; refine mk (ha.mul hv.absolute) ?_
  filter_upwards [hF,hh] with i ha hh j
  change normJ n (v i • f i j) 0 ≤ _; rw [normJ,iteratedFDeriv_const_smul_apply (hh j),norm_smul, Real.norm_eq_abs,mul_comm]
  exact mul_le_mul_of_nonneg_right (ha j) (abs_nonneg _)
lemma negates (hh:Smooths n f):Flares R n p (-f):=by
   simpa only [add_zero,neg_one_smul] using! h.scales (Charges.frozen (-1) R) hh
lemma subs (hg:Flares R n p g)(hh:Smooths n f)(hk:Smooths n g):Flares R n p (f-g):=by
   simpa only [sub_eq_add_neg] using h.adds (hg.negates hk) hh (Filter.Eventually.mono hk fun i hi j=> (hi j).neg)
   -- confused dot project
end Flares
end
end YM.RG12.Shadows
