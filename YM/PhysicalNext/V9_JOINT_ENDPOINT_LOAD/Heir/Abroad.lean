import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Distinct
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Flux
import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Center
import YM.Extra.ITERATION_NO_LOSS.Continuity
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Delay


/-!
# Real unscaled source rows near 1 on the no-hole stencil

To compare an inherited E expectation with its flat tree predictor.
Different budget than the actual affine-mean jet curriculum: *unscaled*
sup jets in a common patch around 1; NOT generally true for the
mean in the presence of frozen coordinates. The table here is initially a
local model on the full all-regular layout, the row source UNMASKED via
Offset's fixedBase (not asserting global clearance of the actual sectors in
which we need this). This file only for estimating E after agreements and
returning to actual curvature and group fields. No identification of
ActualScalar scanners etc. Uses the true left-exp normalization.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Filter Set Lattice Wilson Pressure Precision RG Tree Next.SectorChange
   Next.SectorChange.Rows Wisps AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
   AnalyticBridge.SectorAffine.Offset Next.Fluctuations
open Push.Uniform (Allows Requests)
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f}

private lemma translated {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} {f : E → F} {x : E} {C : ℝ} (h : Allows n f x C) : Allows n (fun y => f (x+y)) 0 C := by
  refine ⟨(show ContDiffAt ℝ ω f (x+0) from (add_zero x).symm ▸ h.analytic).comp (f:=fun y => x+y) 0 (contDiffAt_const.add contDiffAt_id),fun i hi => ?_⟩
  rw [iteratedFDeriv_comp_add_left, add_zero]; exact h.norm_le i hi
private lemma request_shift {E : Type} {f : PriceCoords G c → E} {o : Site c} {R : ℕ} (u : PriceCoords G c)
    (h : Requests Set.univ f coordRoot o R) : Requests Set.univ (fun y => f (u+y)) coordRoot o R :=
  fun _ _ _ _ hv => h _ (Set.mem_univ _) _ (Set.mem_univ _) fun i hi => congr_arg (u i+ ·) (hv i hi)

abbrev polarView {V : Config G c} (s : Signed) (u z : PriceCoords G c) := pull s 0 (field V (u+z))

private lemma shipLetters (G : Gauge) (n : ℕ) : ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
    ∀ {c f : Side} (S : StepData c f) (V : Config G c) (o : Signed) (u : PriceCoords G c), ‖u‖ ≤ r →
      Letters (polarView (V:=V) o u) o.act n C ∧ Letters (replica S.ratio ∘ polarView (V:=V) o u) (o.act ∘ S.ratio.parent) n C := by
  obtain ⟨r,C,hr,hC,h⟩ := coordinates G n
  let M := max C G.colorScale
  refine ⟨r,M,hr,hC.trans_le (le_max_left ..),?_⟩
  intro c f S V o u hu
  have hf : Letters (polarView (V:=V) o u) o.act n M := by
    refine ⟨fun i j => by rw [separation_signed]; exact Work.E03.sep_step ..,fun e => request_shift u (coarse_pull_support o V e),fun i => ?_⟩
    apply Allows.mono (C:=C) _ (le_max_left ..); unfold polarView
    simp_rw [ProjectorNext.Equivariance.pull_formula]; split
    · exact translated (((h u hu V).1 _).inverse (f:=fun y => field V y (ProjectorNext.Equivariance.bonds o 0 i)))
    exact translated ((h u hu V).1 _)
  refine ⟨hf,⟨(fun i j => by simp only [comp_apply,separation_signed]; exact Work.E03.parent_step ..),fun i => ?_,fun i => ?_⟩⟩
  · simp only [comp_apply,replica]; split
    · exact fun _ _ _ _ _ => rfl
    exact hf.use _
  simp only [comp_apply,replica]; split
  · exact Push.Uniform.allows_const _ ((mat_paid _).le.trans (le_max_right ..))
  exact hf.through _

lemma noFlags (x : ℝ) (G : Gauge) (c : Side) : RG.flags (temp x) (1:Config G c)=∅ := by
  have he := Work.E04.temp_nonneg x
  simp [flags,faceValue,travel,square,Step.read,he]

private lemma zView_cost (G : Gauge) (P : Patch) (K : KernelChoices) (hp : P.Branches K G) (n : ℕ) (d C : ℝ) (hd : 0 < d) : ∃ r Z : ℝ,
    0 < r ∧ 0 < Z ∧ ∀ᶠ x : ℝ in atTop, ∀ {c f : Side} (S : StepData c f), S.patch=P → S.kernel=K → 100*(1+radiusB x) ≤ c.val →
    ∀ (u : PriceCoords G c), ‖u‖ ≤ r → ∀ (o : Signed) (k : S.Choices) (i : Bond c) (F : Forest S.ratio), curb (shots S x) (bareStores S) F x o (.inr i) →
      Letters (polarView (V:=1) o u) o.act n C → Point 0 (o.act i.1) d n (fun z => zNoise (field 1 (u+z)) k o i) Z := by
  obtain ⟨r,M,hr,hM,h⟩ := chosen_branch G P K hp n
  let Z := (Real.sqrt K.penalty) * (curvatureCost G * ((2:ℝ)^n*C*M))
  let E := Real.exp (n*d*(predReach P+1:ℕ))
  refine ⟨r,max 1 (E*Z),hr,zero_lt_one.trans_le (le_max_left ..),?_⟩
  filter_upwards [h] with x h c f S hS hK hF u hu o k i F hi hL
  let Q (z : PriceCoords G c) := S.prediction (facade S o (field 1 z) 0) (Push.SectorMeasure.Oriented.choice o k) i
  have he : Allows n (fun y => G.mat (Q y)) u M := allows_first_slice
    ((h S hS hK hF F (bareStores S) 1 (noFlags ..).symm o i u hi hu).1 _)
  have hb := (hL.through i).times (translated he |>.inverse (f:=fun y => Q (u+y)))
  have h := (curvature_price (U:=fun y => polarView (V:=1) o u y i*(Q (u+y))⁻¹) hb).smul (Real.sqrt K.penalty)
  rw [abs_of_nonneg (Real.sqrt_nonneg _)] at h
  have h := Offset.Point.of_support (R:=predReach P+1) (p:=o.act i.1) (Offset.Through.control h) (?_) hd.le
  · unfold zNoise Tube.Z; rw [hK]; exact h.mono le_rfl (le_max_right ..)
  apply request_shift (f:=fun y => (Real.sqrt K.penalty) • G.curvature (pull o 0 (field (1:Config G c) y) i*(Q y)⁻¹))
  intro v _ w _ hx
  have h₁ := coarse_pull_support o (1:Config G c) i v (Set.mem_univ _) w (Set.mem_univ _) (fun j hj => hx j (by omega))
  have h₂ := prediction_near_eq (hS ▸ hK ▸ hp : S.patch.Branches S.kernel G) (facade S o (field 1 v) 0) (facade S o (field 1 w) 0)
      (Push.SectorMeasure.Oriented.choice o k) i (facade_dep ?_ (fun _ _ => rfl))
  · dsimp only at h₁ ⊢; rw [h₁,show Q v=Q w from h₂]
  rw [hS]; exact field_dep (fun _ _ => rfl) hx

abbrev ink (T : Tube G S) (F : Forest S.ratio) (x : ℝ) (t : S.Choices) (u : PriceCoords G c) := tape.symm
    (Rows.restrict x (shots S x) (bareStores S) F (Offset.fixedBase T x (field 1 u) t))

lemma abroad (G : Gauge) (P : Patch) (Pt : Teller G) (hp : P.Branches Pt.bind G) (n : ℕ) :
    ∃ r d N : ℝ, 0<r ∧ 0<d ∧ 0<N ∧ ∀ᶠ x : ℝ in atTop, ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → Pt.Funds S T →
      100*(1+radiusB x) ≤ c.val → ∀ (F : Forest S.ratio) (k : S.Choices) (u : PriceCoords G c), ‖u‖ ≤ r →
      Parcel 0 (down S) d n (fun z => ink T F x k (u+z)) N := by
  obtain ⟨r,C,hr,hC,h⟩ := shipLetters G n
  obtain ⟨d,M,hd,hM,h₁⟩ := bound_plotted G Pt.top.width_pos n (L:=Pt.top.paths) Pt.top.clip hC.le (by norm_num : (0:ℝ)<2)
  obtain ⟨e,N,he,hN,h₂⟩ := bound_plotted G Pt.below.width_pos n (L:=Pt.below.paths) Pt.below.clip hC.le (by norm_num : (0:ℝ)<2)
  obtain ⟨d',U,hd',hU,h₃⟩ := wide G Pt P.L n C N hC.le hN
  obtain ⟨e',W,he',hW,h₄⟩ := Offset.noise G Pt n C N hC.le hN
  let s := min (min d e) (min d' e'); have hs := lt_min (lt_min hd he) (lt_min hd' he')
  obtain ⟨b,Z,hb,hZ,h₅⟩ := zView_cost G P Pt.bind hp n s C hs
  let B := max (M+U) (Z+W); have hB : 0<B := (add_pos hM hU).trans_le (le_max_left ..)
  refine ⟨min r b,s,slip*B, lt_min hr hb,hs,mul_pos slip_pos hB,?_⟩
  filter_upwards [h₅] with x hx c f S T hP hT hF F k u hu j
  rcases j with ⟨⟨o,i⟩,α⟩
  let j : Rows.Receipt G S := ((o,i),α)
  let L := polarView (V:= (1:Config G c)) o u; let V := replica S.ratio ∘ L
  have hv (z) : facade S o (field 1 (u+z)) 0=V z := by rw [fixed_facade,← AnalyticBridge.SectorAffine.Identity.top_copy]; rfl
  obtain ⟨hL,hv'⟩ := h S 1 o u (hu.trans (min_le_left ..))
  obtain ⟨a,b,ha,hb⟩ := hT.feeds
  let R:=Stores.till x
  have hy (j : Twin c) : Point 0 (o.act j.1.1) s n (fun z => T.Xn R (L z) j) (N*1) := by
    unfold Tube.Xn; rw [hT.low]
    simpa only [one_smul] using! ((h₂ L _ hL T.down b hb 1 1 (by norm_num) (by norm_num) le_rfl (by norm_num) R _ S.patch.L.property j
      (fun w _ => by rw [mul_one]; exact G.chord_le_two _)).mono (s:=s) ((min_le_left ..).trans (min_le_right ..)) le_rfl)
  apply Point.color (w:=fun z => Rows.restrict x (shots S x) (bareStores S) F (Offset.fixedBase T x (field 1 (u+z)) k) j.1) _ α
  unfold Rows.restrict; split; swap; · exact Point.zero (mul_pos slip_pos hB).le
  next hi =>
  suffices H : Point 0 (down S j) s n (fun z => Offset.fixedBase T x (field 1 (u+z)) k j.1) B by
    simpa only [abs_of_pos Rows.slip_pos] using H.scale slip
  cases i with
  | inl i =>
    have hv0 : Point 0 (down S j) s n (fun z => T.Xf R (facade S o (field 1 (u+z)) 0) i) M := by
      simp_rw [hv,Tube.Xf,hT.high]
      simpa only [one_smul,mul_one] using! ((h₁ V _ hv' T.up a ha 1 1 (by norm_num) (by norm_num) le_rfl (by norm_num) R 1 (by decide) i
        (fun w _ => by rw [mul_one]; exact G.chord_le_two _)).mono ((min_le_left (min d e) _).trans (min_le_left ..)) le_rfl)
    have ht := h₃ S T hT (by rw [hP]) L (fun j z => T.Xn R (L z) j) _ hv' R 1 1 s zero_le_one zero_le_one le_rfl hs.le ((min_le_right ..).trans (min_le_left ..)) i (fun j _ => hy j)
    simp only [one_smul,mul_one] at ht
    exact (hv0.sub ht).mono le_rfl (le_max_left ..)
  | inr i =>
    have ht := h₄ S T hT L (fun j z => T.Xn R (L z) j) _ hL R 1 1 s zero_le_one zero_le_one le_rfl hs.le ((min_le_right ..).trans (min_le_right ..)) i (fun j _ => hy j)
    simp only [one_smul,mul_one] at ht
    exact ((hx S hP hT.knobs hF u (hu.trans (min_le_right ..)) o k i F hi hL).sub ht).mono le_rfl (le_max_right ..)
end YM.PhysicalNext.JointLoad.Heir
