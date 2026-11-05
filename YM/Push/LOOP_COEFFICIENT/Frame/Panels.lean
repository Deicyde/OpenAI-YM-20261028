import YM.Push.LOOP_COEFFICIENT.Frame.Balance

/-!
# The two equations of a centered panel at flat
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Frames
open Function Set Filter
open scoped Topology ContDiff BigOperators
variable {ι κ : Type} [Fintype ι] [Fintype κ] {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedRing F] [NormedAlgebra ℝ F] {s : Scope E} {k n : ℕ} {A B C K J : ℝ}
structure Weaving (ι κ E : Type) where
  frame : ι → E → ℝ
  path : ι → κ → E → ℝ
  center : ι → ℝ
  step : κ → ℝ
  goal : κ → ι

structure Weaving.Strands (W : Weaving ι κ E) (B : ℝ) : Prop where
  unit : 1≤B
  center i : 0≤ W.center i
  step i : 0≤ W.step i
  centers : ∑ i,W.center i = 1
  steps : ∑ i,W.step i = 1
  frame i x : 1 ≤ W.frame i x
  path i j x : 0 ≤ W.path i j x
  outside x : weighted W.center (fun i => W.frame i x) ≤ B
  sourced i x : weighted W.step (fun j => W.frame (W.goal j) x + W.path i j x) ≤ B*W.frame i x

def ply (W : Weaving ι κ E) (f : ι → E → F) (v : ι → κ → E → F) (i : ι) (x : E) := weighted W.step (fun j => f (W.goal j) x * v i j x)
structure Panel (W : Weaving ι κ E) (g : F → F) (f : ι → E → F) (v : ι → κ → E → F) : Prop where
  atFrame i : f i 0 = 1
  atPath i j : v i j 0 = 1
  smooth i : ContDiffAt ℝ ω (f i) 0
  smooth' i j : ContDiffAt ℝ ω (v i j) 0
  placed i : f i =ᶠ[𝓝 0] g ∘ ply W f v i
  centered : (fun x => g (weighted W.center (fun i => f i x))) =ᶠ[𝓝 0] fun _ => 1

variable {W : Weaving ι κ E} {f : ι → E → F} {v : ι → κ → E → F} {g : F → F}
  (hw : W.Strands B) (h : Panel W g f v)
include hw h
omit hw in
lemma ply_diff (i : ι) : ContDiffAt ℝ ω (ply W f v i) 0 := weighted_diff W.step (fun j x => f (W.goal j) x * v i j x) fun j => (h.smooth _).mul (h.smooth' i j)
lemma ply_zero (i : ι) : ply W f v i 0 = 1 := by simp only [ply,h.atFrame,h.atPath,mul_one,weighted,← Finset.sum_smul,hw.steps,one_smul]
lemma panel_prod (hf : ∀ i,Legacy s (W.frame i) (f i) 0 k K) (hv : ∀ i j, Legacy s (W.path i j) (v i j) 0 k A) (i : ι) (j : κ) : Legacy s (fun x => W.frame (W.goal j) x + W.path i j x) (fun x => (f (W.goal j) x,v i j x)) 0 k (A+K) := by
  have hm := hf (W.goal j); have hu := hv i j; exact ((hm.mono (fun _ => zero_le_one.trans (hw.frame ..)) (le_add_of_nonneg_left hu.nonneg)).majorize (fun x => le_add_of_nonneg_right (hw.path i j x))).prod ((hu.mono (hw.path i j) (le_add_of_nonneg_right hm.nonneg)).majorize (fun _ => le_add_of_nonneg_left (zero_le_one.trans (hw.frame ..)))) (h.smooth _) (h.smooth' ..)



omit hw h

private def surplus (F : Type) [NormedRing F] : F × F → F := fun x => x.1*x.2 - (x.1+x.2)
private lemma surplus_diff (F : Type) [NormedRing F] [NormedAlgebra ℝ F] : ContDiffAt ℝ ω (surplus F) (1,1) := by unfold surplus; fun_prop
private lemma surplus_rate (F : Type) [NormedRing F] [NormedAlgebra ℝ F] : fderiv ℝ (surplus F) (1,1) = 0 := by
  let a : F×F := (1,1)
  have he := hasFDerivAt_fst (𝕜:=ℝ) (p:=a); have hh := hasFDerivAt_snd (𝕜:=ℝ) (p:=a)
  rw [show fderiv ℝ (surplus F) (1,1) = _ from ((he.mul' hh).sub (he.add hh)).fderiv]
  simp [a,add_comm]
include h hw in
lemma Panel.remainder (hf : ∀ i,Legacy s (W.frame i) (f i) 0 k K) (hv : ∀ i j, Legacy s (W.path i j) (v i j) 0 k A) (hv' : ∀ i j, Engrave s (W.path i j) (v i j) 0 (k+1) A) (i : ι) (j : κ) : Imprint s (fun x => W.frame (W.goal j) x + W.path i j x) (fun w => iteratedFDeriv ℝ (k+1) (fun x => f (W.goal j) x * v i j x) 0 w - iteratedFDeriv ℝ (k+1) (f (W.goal j)) 0 w) (opus (surplus F) (1,1) (k+1) (A+K)+A) := by
  let g := fun x => (f (W.goal j) x, v i j x); have hg := (h.smooth (W.goal j)).prodMk (h.smooth' i j); have hg0 : g 0=(1,1) := Prod.ext (h.atFrame _) (h.atPath ..)
  have he := (panel_prod hw h hf hv i j).muted (surplus F) (by rw [h.atFrame,h.atPath]; exact surplus_diff F) hg (by rw [h.atFrame,h.atPath]; exact surplus_rate F) (fun i => add_nonneg (zero_le_one.trans (hw.frame ..)) (hw.path ..)); change Engrave _ _ (surplus F ∘ g) 0 _ (opus _ (g 0) _ _) at he; rw [hg0] at he
  have ht (w : Fin (k+1) → E) := congr_arg (fun z => iteratedFDeriv ℝ (k+1) z 0 w) (show (surplus F ∘ g) = (fun x => f (W.goal j) x * v i j x) - (f (W.goal j)+v i j) from rfl)
  simp only [iteratedFDeriv_sub_apply (f:=(fun x => f (W.goal j) x * v i j x)) (g:=f (W.goal j)+v i j) (((h.smooth (W.goal j)).mul (h.smooth' i j)).of_le le_top) (((h.smooth (W.goal j)).add (h.smooth' i j)).of_le le_top), iteratedFDeriv_add_apply ((h.smooth (W.goal j)).of_le le_top) ((h.smooth' i j).of_le le_top), _root_.sub_apply,_root_.add_apply] at ht
  convert! Imprint.add he ((hv' i j).majorize fun _ => le_add_of_nonneg_left (zero_le_one.trans (hw.frame ..))) using 2; rw [ht]; abel
include h hw in
lemma Panel.spool (hf : ∀ i,Legacy s (W.frame i) (f i) 0 k K) (hv : ∀ i j, Legacy s (W.path i j) (v i j) 0 k A) (hv' : ∀ i j, Engrave s (W.path i j) (v i j) 0 (k+1) A) (hA : 0≤A) (hK : 0≤K) (i : ι) : Imprint s (W.frame i) (fun w => iteratedFDeriv ℝ (k+1) (ply W f v i) 0 w - weighted W.step (fun j => iteratedFDeriv ℝ (k+1) (f (W.goal j)) 0 w)) ((opus (surplus F) (1,1) (k+1) (A+K)+A)*B) := by
  have ho : 0≤opus (surplus F) (1,1) (k+1) (A+K) := Finset.sum_nonneg fun _ _ => by unfold pages; positivity
  have he := Imprint.mean W.step hw.step hw.steps (add_nonneg ho hA) (h.remainder hw hf hv hv' i) (fun _ => le_rfl) |>.move hw.unit (hw.sourced i)
  convert he using 2; unfold ply; rw [iterated_weighted W.step (fun j x => f (W.goal j) x * v i j x) (fun j => (h.smooth _).mul (h.smooth' ..))]; unfold weighted; simp [smul_sub,Finset.sum_sub_distrib]
include h hw in
lemma Panel.center_price (L : F →L[ℝ] F) (hg : fderiv ℝ g 1=L) (hf : ∀ i,Legacy s (W.frame i) (f i) 0 k K) (hK : 0≤K)
    (hJ : ∀ (f : E → F), 1=f 0 → ContDiffAt ℝ ω f 0 → ∀ (m : E → ℝ), (∀ x,0≤m x) → Legacy s m f 0 k (K*B) → Imprint s m (fun w => iteratedFDeriv ℝ (k+1) (g ∘ f) 0 w - fderiv ℝ g 1 (iteratedFDeriv ℝ (k+1) f 0 w)) J) : Imprint s (fun _ => 1) (fun w => L (weighted W.center fun i => iteratedFDeriv ℝ (k+1) (f i) 0 w)) J := by
  let u (x : E) := weighted W.center fun i => f i x
  have hu : u 0=1 := by simp only [u,h.atFrame,weighted, ← Finset.sum_smul,hw.centers,one_smul]
  have hU := Legacy.mean (s:=s) W.center hw.center hw.centers hK h.smooth hf (m:=fun _ => B) hw.outside
  have he := hJ u hu.symm (weighted_diff _ _ h.smooth) _ (fun _ => zero_le_one) ⟨fun i hi => (hU.levels i hi).move hw.unit (by simp)⟩
  have ht : iteratedFDeriv ℝ (k+1) (g ∘ u) 0 = 0 := by rw [show iteratedFDeriv ℝ (k+1) (g ∘ u) 0 = iteratedFDeriv ℝ (k+1) (fun _ => (1:F)) 0 from (h.centered.iteratedFDeriv ℝ (k+1)).self_of_nhds,iteratedFDeriv_const_of_ne (by omega)]; rfl
  rw [ht,hg] at he
  simpa only [_root_.zero_apply, zero_sub,neg_neg, u,iterated_weighted W.center _ h.smooth] using! he.neg
include h hw in
lemma Panel.incidence (hf : ∀ i,Legacy s (W.frame i) (f i) 0 k K) (hv : ∀ i j, Legacy s (W.path i j) (v i j) 0 k A) (hv' : ∀ i j, Engrave s (W.path i j) (v i j) 0 (k+1) A) {D M} (hD : ∀ i,Legacy s (W.frame i) (ply W f v i) 0 k D)
    (hM : ∀ (f : E → F), 1=f 0 → ContDiffAt ℝ ω f 0 → ∀ (m : E → ℝ), (∀ x,0≤m x) → Legacy s m f 0 k D → Imprint s m (fun w => iteratedFDeriv ℝ (k+1) (g ∘ f) 0 w - fderiv ℝ g 1 (iteratedFDeriv ℝ (k+1) f 0 w)) M) (hA : 0≤A) (hK : 0≤K) (i : ι) : let L := fderiv ℝ g 1
    Imprint s (W.frame i) (fun w => iteratedFDeriv ℝ (k+1) (f i) 0 w - L (weighted W.step (fun j => iteratedFDeriv ℝ (k+1) (f (W.goal j)) 0 w))) (M + ‖L‖*((opus (surplus F) (1,1) (k+1) (A+K)+A)*B)) := by
  intro L; have he := hM (ply W f v i) (ply_zero hw h i).symm (ply_diff h i) (W.frame i) (fun _ => zero_le_one.trans (hw.frame ..)) (hD i)
  have ht := h.spool hw hf hv hv' hA hK i |>.linear L
  convert Imprint.add he ht using 2; rw [((h.placed i).iteratedFDeriv ℝ (k+1)).self_of_nhds,Function.comp_apply,map_sub]; dsimp only [L]; abel


end YM.Push.Loops.Frames
