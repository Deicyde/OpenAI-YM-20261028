import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Malachite.Mineral
import YM.Planned.ATOM_REGULAR_ESTIMATE.Localization
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Performs

/-!
# Buy dry in post-L gauges. Keep uniform Pad perturbation allowances in b

From `quenched` not asserting persistence of Authorization across a flag
boundary. Read the APERTURE even for positive derivative orders. Use even
when Z labels not involved in focus. Shares numericals across within-G slab.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Malachite
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Gate Census Progress.StationaryScenes Progress.StationaryScenes.Green
open Tablet Foramen Frond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}

structure Spark (X : Coat T F) (j : ℕ) (b : Directions G c) (M : ℝ) : Prop where
  drills (i k : Tubular f G) : ContDiffAt ℝ j (fun u=> Malachite.drills X u i k) b
  mine (i : Slots S × G.ColorIndex) (k : Tubular f G) : ContDiffAt ℝ j (fun u=> Malachite.mine X u i k) b
  paper (i : Mention c f × G.ColorIndex) : ContDiffAt ℝ j (fun u=> receipt X u i) b
  sorts : Brush j M 1 (study X) b
  charge : Brush j M 1 (ore X) b
  cloud (i l : Tubular f G) : Brush j M 1 (fun u=> stoneC X u i l) b

lemma grouped {A E : Type} {ι κ : Type} [Fintype ι] [Fintype κ] [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ι → Site c} {b : κ → Site c} {p : A} {K : E→Matrix ι κ ℝ} {t m v : ℝ} {j : ℕ}
    (L : A →L[ℝ] E) (h : Tablet j t m v K a b (L p)) (he : ‖L‖ ≤ 1) : Tablet j t m v (K ∘ L) a b p := by
  obtain ⟨ha,hb,hc,M,hd,hv⟩:=h
  exact ⟨ha,hb,hc,M,fun i j=> mul_one v ▸ Brush.reading L (hd i j) he,hv⟩

section assembly
variable (G : Gauge) (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (j : ℕ) (hj : 1≤j)
variable (η r Q : ℝ) (hp : Torch η r Q) {V : ℝ → ℝ} (h : Rate G L (-(1/2)) V) (hv : ∀ᶠ x in atTop,0 ≤ V x)
include hD hj hp h hv
-- price with visible grains
lemma sieve : ∃ M : ℝ→ℝ, Rate G L 0 M ∧ ∀ᶠ x in atTop, ∀ (c f:Side) (S : StepData c f) (T : Tube G S),
    S.patch=D → Works P L x S T → ∀ (F : Forest S.ratio) (X : Coat T F), X.x=x →
      Allow X.blank.plate (along S) (tubularPrice G L) η r Q→ ∀ u : Directions G c, ‖u‖≤ V x → Spark X j u (M x) := by
  obtain ⟨W,e,w,Y,H,hW,he,hw,hY,hP,Hh⟩:= quenched P L D hD j hj h hv η r Q hp
  obtain ⟨R,hR,Z,hZ,hZ',hF⟩:= Gate.beam P L D hD j
  let m:= tubularPrice G L; let b:= min e (retain e w W)
  let A x:= facePrice j (radiusB x) m W (payE e w W m); let B x:= ‖Coat.scale‖*|Z x|; let s x:= H x+1
  let J x:= driftP j (H x); let t x:= J x+s x
  let Q x:= Y*B x; let q x:= A x*Q x
  let L₀ x:=Q x*(1+s x)^j; let T x:= q x*(1+t x)^j; let v x:= ‖(1/2:ℝ)‖*(A x+A x)*(1+J x)^j
  have ha: Rate G L 0 A := polynomial G L j m W (payE e w W m)
  have hk : Rate G L 0 (fun x=>|Z x|):= hZ'.compare (Eventually.of_forall fun x=> by rw [abs_abs])
  have hz : Rate G L 0 Q:= (hk.mul_left _).mul_left _
  have hf : Rate G L 0 J := hP.mul_left _
  have ht := Rate.const (G:=G) (L:=L) (1:ℝ)
  have hs := hP.add ht
  refine ⟨fun x=> L₀ x+ T x+v x,Rate.add (Rate.add ?_ ?_) ?_,?_⟩
  · simpa only [zero_mul,zero_add] using! hz.mul ((ht.add hs).pow j)
  · simpa only [add_zero,zero_mul] using! (ha.mul hz).mul ((ht.add (hf.add hs)).pow j)
  · simpa only [zero_mul,zero_add] using! ((ha.add ha).mul_left ‖(1/2:ℝ)‖).mul ((ht.add hf).pow j)
  filter_upwards [Hh,hF,h.below (by norm_num) R hR] with x Hh hF hK c f S T' hS hU F X hX hB u hu; subst x
  let f₀ := ContinuousLinearMap.inl ℝ (Directions G c) (Directions G f)
  have hL₀ : ‖f₀‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x=> by simp [f₀,Prod.norm_def]
  have hu' (x) : ‖f₀ x‖ ≤ ‖x‖ := by simp [f₀,Prod.norm_def]
  let x:=X.x; obtain ⟨hK',ha,hM⟩:= Hh c f S T' hS hU F X rfl hB (f₀ u) ((hu' u).trans hu)
  have hh : 0 ≤ b := le_min he.le hK'.weather.1.le
  have hW': Tablet j b (A x) (J x) (drills X) (along S) (along S) u :=
    grouped f₀ (padjets X.shutter (ha.tilt le_rfl le_rfl hh (min_le_left ..)) hK' (min_le_right ..)) hL₀
  have hY' : Tablet j e Y (H x) (mine X) (aim S) (along S) u := grouped f₀ hM hL₀
  -- prima direction entry
  have hD (p : Mention c f) : Brush j (Z x) 1 (fun y=> strain (gem X y) p.1 p.2 0) u := by
    simp_rw [gem,sprig X _ _ hU.funds]; let K := (reachP p.1 G c f).toContinuousLinearMap.comp f₀
    have hK (v) (hp: ‖v‖≤ R) : ‖K v‖≤R := by
      exact max_le ((displacement_bounded _ _ v).trans hp) (by change ‖(0:Directions G f)‖ ≤ _; rw [norm_zero]; exact hR.le)
    have hp : ‖K‖≤1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v=>max_le ((displacement_bounded _ _ v).trans_eq (one_mul _).symm) (by change ‖(0:Directions G f)‖ ≤ _; simp)
    have h' := hF c f S T' hS hU (choice p.1 X.k) p.2 (K u) (hK u (by linarith [‹|V _|≤R›, le_abs_self (V x)])); simpa only [mul_one] using! reading K h' hp
  have ht' (i : Coat.Target c f G) : Brush j (B x) 1 (fun y=> receipt X y i) u := by
    unfold receipt ConnectedActivityE6.stand bar; simp_rw [show ∀ z:Directions G c, (if (gem X z).selected i.1.1 (spot S i.1.2) then _ else 0) = Coat.scale • strain (gem X z) i.1.1 i.1.2 0 from fun z=> if_pos (show (gem X z).selected i.1.1 (spot S i.1.2) from X.blank_all _ _)]
    exact colorEvaluated _ (((hD i.1).climb (le_abs_self _) le_rfl).smul Coat.scale)
  have hz : 0 ≤ B x := mul_nonneg (norm_nonneg _) (abs_nonneg _); have hq : 0≤ Q x := mul_nonneg hY hz
  have hi i : Brush j (Q x) (s x) (fun y=> ore X y i) u := beam_vec hY'.reverse hz zero_le_one ht' i
  have hj : 0 ≤ s x := add_nonneg hY'.pos zero_le_one
  have hf i : Brush j (q x) (t x) (fun y=> study X y i) u := (beam_vec hW'.reverse hq hj hi (tube X i)).opposite
  have hl : 0 ≤ L₀ x := mul_nonneg hq (pow_nonneg (add_nonneg zero_le_one hj) _)
  have hc : 0 ≤ T x := mul_nonneg (mul_nonneg hW'.basis hq) (pow_nonneg (add_nonneg zero_le_one (add_nonneg hW'.pos hj)) _)
  have hp : 0 ≤ v x := mul_nonneg (mul_nonneg (norm_nonneg _) (add_nonneg hW'.basis hW'.basis)) (pow_nonneg (add_nonneg zero_le_one hW'.pos) _)
  refine ⟨fun i j=> (hW'.singular i j).smooth,fun i j=> (hY'.singular i j).smooth,fun i=>(ht' i).smooth,
    (show Brush j _ _ (study X) u from fold zero_le_one hc (fun i=> (hf i).trim)) |>.climb (by change T x ≤ L₀ x+T x+v x; linarith only [hp,hl]) le_rfl,
    (show Brush j _ _ (ore X) u from fold zero_le_one hl (fun i=> (hi i).trim)) |>.climb (by change L₀ x ≤ L₀ x+T x+v x; linarith only [hp,hc]) le_rfl,
    fun i j=> ?_⟩
  exact ((((hW'.singular i j).gathering (hW'.singular j i)).smul (1/2:ℝ)).trim).climb (show v x≤ _ from le_add_of_nonneg_left (add_nonneg hl hc)) le_rfl
end assembly
end YM.PhysicalNext.Repeat.Malachite
