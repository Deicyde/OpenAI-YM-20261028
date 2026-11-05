import YM.Extra.SOURCE_HISTORIES.Counter
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Malachite.Sheen
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Malachite.Tilth

/-!
# Both predictors, jets in b through n and first tilt

Everything on Coat, Heir. Through response transforms still needed. V jets
will compare on germs, *not* b jets everywhere uniformly shrinking only
rates (frameC). Don't chart-substitute directly. Need lifts and measures.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Malachite
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Gate Census Progress.StationaryScenes Progress.StationaryScenes.Green
open Tablet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}

abbrev diver (X : Coat T F) := forecast T X.x F X.k-study X

structure Photic (X : Coat T F) (u t C : ℝ) (n : ℕ) : Prop where
  light : Portrait (diver X) 0 n t u C
  studies b : ‖b‖ ≤ u→ Brush n C 1 (study X) b
  horizon b i j : ‖b‖ ≤ u→ Brush n C 1 (fun x=> (stoneC X x).submatrix (tube X) (tube X) i j) b
  peak b i j : ‖b‖ ≤ u→ Brush n C 1 (fun x=> optics X x i j) b
  shade : Price (notice X) (notice X) ((stoneC X 0).submatrix (tube X) (tube X) - optics X 0) 0 t

lemma settled {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Y] [NormedSpace ℝ Y] {n : ℕ}
    {f : E→Y} {x : E} {v : ℝ} : Brush n v 1 f x ↔ Offset.Through n f x v :=
  ⟨fun h=> ⟨h.smooth, (offer.mp h).inside⟩, fun h=> offer.mpr ⟨h.smooth,h.pay⟩⟩

section purchase
variable (G : Gauge) (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (n : ℕ) (hn : 2≤n) {p : ℝ→ℝ}
    (hv : Rate G L (-(1/2)) p) (hh : ∀ᶠ x in atTop,0≤p x)
include hD hn hv hh
lemma treasure (j : ℝ) : ∃ t C : ℝ→ℝ, Rate G L j t ∧ Rate G L 0 C ∧ ∀ᶠ x in atTop,
    ∀ (c f:Side) (S : StepData c f) (T : Tube G S), S.patch=D → Works P L x S T →
    ∀ (F : Forest S.ratio) (Y : Coat T F), Y.x=x → 0≤ t x ∧ 0 ≤ C x ∧ Photic Y (p x) (t x) (C x) n := by
  obtain ⟨η,r,Q,M,hP,H⟩:= shoots P L D hD
  obtain ⟨V,W,hW⟩:= sieve G P L D hD n (by omega) η r Q hP hv hh
  obtain ⟨a,d,v,w,u,c,ha,hd,hv',hw',hu,hc,Hh⟩:= AnalyticBridge.SectorAffine.assembly G D P hD n
  obtain ⟨r',M',hr,hm,he⟩:= survey G D P hD n
  let m:= tubularPrice G L; let t x:= missPay η r Q v c m (radiusB x); let C' := activation G n 0 d*c; let C x:= M'+V x+C'
  have hz : Rate G L j (fun x=> Real.exp (-v*radiusB x)) := by
    apply ((Rate.cutoff (δ:=v) hv')).compare
    filter_upwards with x; rw [abs_of_pos (Real.exp_pos _),abs_of_pos (Real.exp_pos _)]; apply Real.exp_monotone
    have he : (till x:ℝ) ≤ (radiusB x:ℝ) := by exact_mod_cast Nat.div_le_self ..
    nlinarith
  refine ⟨t,C,((hP.physical G L j m).mul_left _).add (hz.mul_left _),((Rate.const _).add W).add (Rate.const _),?_⟩
  filter_upwards [H,hW,Hh,he,hh,hv.below (by norm_num) _ (lt_min ha hr), ConnectedActivityE6.room G P L] with x hW' hW hz he hg hc' hR c' f S T hx ht F Y hy; subst x
  let x:=Y.x
  have H₀ := hR c' f S T ht
  have hA := hW' c' f S T F Y.blank rfl hx ht.length_eq H₀ (Y.bowed (temp_nonneg _))
  have h' (b:Directions G c') (hp: ‖b‖≤p x) := hW c' f S T hx ht F Y rfl hA.scale _ hp
  have he' : p x ≤ a ∧ p x≤r':= le_min_iff.mp ((le_abs_self _).trans hc')
  have hv (b : Directions G c') (hp:‖b‖ ≤ p x) : Brush n M' 1 (forecast T Y.x F Y.k) b :=
    settled.mpr (he S T hx ht.funds H₀.buys _ _ b (hp.trans he'.2))
  have HH (b:Directions G c') (hp: ‖b‖≤p x) := hz.2 S T hx H₀.buys ht.funds (bareStores S) F 1 (noFlags ..).symm Y.k _ ((reader_norm b).trans (hp.trans he'.1))
  have ho := h' 0 (by rw [norm_zero]; exact hg); have hy₀ : KernelJets n d v w u c (bareStores S) F T x 1 Y.k 0 := by simpa only [map_zero] using HH 0 (by rw [norm_zero]; exact hg)
  have h₀: 0≤ C':= mul_nonneg (zero_le_one.trans (activation_one G n 0 hd)) hc.le
  have hh : 0 ≤ V x:= ho.sorts.nonneg; have hu : 0≤ C x:= add_nonneg (add_nonneg hm.le hh) h₀
  have hg' : 0≤t x:= add_nonneg (mul_nonneg hA.scale.disc (hA.scale.heap _)) (mul_nonneg hc.le (Real.exp_pos _).le)
  have hx : V x ≤ C x:= (le_add_of_nonneg_left hm.le).trans (le_add_of_nonneg_right h₀)
  refine ⟨hg',hu,⟨?_,?_,?_⟩,fun b hb=> ((h' b hb).sorts).climb hx le_rfl,
    fun b i j hb=> ((h' b hb).cloud (tube Y i) (tube Y j)).climb hx le_rfl,fun b i j hb => ((rayD i j (HH b hb).cJets hd hc.le)).climb (le_add_of_nonneg_left (add_nonneg hm.le hh)) le_rfl,
    night Y ht.funds hA.scale hy₀ hd⟩
  · intro z hz; exact ((settled.mp (show Brush n _ _ (diver Y) z from (hv z hz).separating (h' z hz).sorts))).mono (le_add_of_nonneg_right h₀)
  · unfold diver; rw [Pi.sub_apply,cool_chart Y ht.funds,clean_study Y ht.funds,sub_zero]
  rw [sub_zero]; have hk : (n:WithTop ℕ∞)≠ 0 := by exact_mod_cast (by omega:n≠0)
  apply (tilt0 Y ht.funds hA.scale hy₀ (by omega) hd hc.le
    (fun i j=> (ho.drills i j).differentiableAt hk) (fun i j=> (ho.mine i j).differentiableAt hk)
    ((contDiffAt_pi.mpr ho.paper).differentiableAt hk) (price_one (settled.mp ho.charge) (by omega))).trans
  change t x * V x ≤ _; rw [mul_comm (t x)]; exact mul_le_mul_of_nonneg_right hx hg'
end purchase
end YM.PhysicalNext.Repeat.Malachite
