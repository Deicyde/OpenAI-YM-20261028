import YM.RG12.Shadows.Gully
/-! # Chronology colors at identity with speed^j per rank even when base and first
 agree. PRICING not allowed on background phase. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Sanction
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Silica Eider Metric Set Gaussian Tablet Quill Baffle Prism Brim Lotus Peak
open WardBin.Lies Push.PriceCompiler Foramen Gate
open YM.RG12.Shadows
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{V:Loom G}
namespace Barque
variable (B:Barque V)
abbrev cF (y:Panels 2) :=B.C6 y
lemma zeroW (i:B.I) : B.W6 i 0=0 := by
  rw [show B.W6 i 0=_ from (B.nearGauge.self_of_nhds.1 i).1,B.aim_zero]; unfold spot6; rw [clean_study _ B.H.laws.intake.ready]; rfl
structure Plates (t C:ℝ) : Prop where
   pay : 0≤C
   care:0≤t
   flutes(i:B.I):Brush 2 ((Fintype.card G.ColorIndex:ℝ)*2*C) B.helm (B.W6 i) 0
   farms(i:B.I):Brush 2 ((Fintype.card G.ColorIndex:ℝ)*2*C) B.helm (B.W9 i-B.W6 i) 0
   offset0(i:B.I):(B.W9 i-B.W6 i) 0=0
   miss(i:B.I)(j:G.ColorIndex): normJ 1 (fun y=>(B.W9 i y-B.W6 i y) j) 0 ≤ (C*t)*B.helm
   dense (i j:B.Q₀): Brush 2 (2*C) B.helm (fun y=>B.C6 y i j) 0 ∧ Brush 2 (2*C) B.helm (fun y=>B.C9 y i j) 0
   signal (i j:B.Q₀): ‖B.C9 0 i j-B.C6 0 i j‖ ≤ t
lemma shelf {t C:ℝ}(ht:0≤t)(hh:0≤C)(h:Photic B.X 0 t C V.n):B.Plates t C:=by
  have hC (i:B.I){F:Type}[NormedAddCommGroup F][NormedSpace ℝ F] (g : Directions G B.c→F) (hg : Brush V.n C 1 g 0):Brush 2 (2*C) B.helm (g ∘ B.aim0 i) 0 :=by
    have hh :=B.dome i; have hf:Brush 2 C 1 g (B.aim0 i 0):= (B.aim_zero i).symm ▸ hg.smaller V.depth
    have hk:=hf.compound (f:=B.aim0 i) (hh.smooth.of_le (Nat.cast_le.mpr V.depth)) hh.hp.le (fun i hp he=> hh.hops i hp (he.trans V.depth))
    convert! hk using 1
  let W (i:B.I) (j:G.ColorIndex):Prices G (Heir.clear B.S B.x B.F) →L[ℝ]ℝ:=ContinuousLinearMap.proj (B.a.seat i,j)
  have he i j: ‖W i j‖ ≤ 1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v=> by rw [one_mul]; exact norm_le_pi_norm v _
  let D:= diver B.X
  have hD:= h.light
  have hP:= Malachite.settled.mpr (hD.uniform 0 (by simp))
  have hF(i:B.I) : Brush 2 (2*C) B.helm (D ∘ B.aim0 i) 0:=hC i D hP
  have h6(i:B.I): Brush 2 (2*C) B.helm (study B.X ∘ B.aim0 i) 0:= hC i _ (h.studies _ (by simp))
  refine ⟨hh,ht,?_,?_,?_,?_,?_,?_⟩
  · intro i; rw [mul_assoc]; refine Blaze.tie _ _ (by positivity) ((B.dome i).hp.le) fun j=> ?_
    refine ((h6 i).report (W i j) (he i j)|>.climb (one_mul _).le le_rfl).shimmy (B.nearGauge.mono fun y hy=>?_)
    dsimp only; rw [(hy.1 i).1]; rfl
  · intro i; rw [mul_assoc]; refine Blaze.tie _ _ (by positivity) ((B.dome i).hp.le) fun j=> ?_
    refine ((hF i).report (W i j) (he i j)|>.climb (one_mul _).le le_rfl).shimmy (B.nearGauge.mono fun y hy=>?_)
    dsimp only; rw [Pi.sub_apply]; rw [(hy.1 i).1,(hy.1 i).2]; rfl
  · intro i; have he:= B.nearGauge.self_of_nhds.1 i
    change B.W9 i 0 - B.W6 i 0=0; rw [he.1,he.2,B.aim_zero]; ext j; exact congrFun hD.home (B.a.seat i,j)
  · intro i j
    have he' : (fun y=> (B.W9 i y-B.W6 i y) j) =ᶠ[𝓝 0] (W i j) ∘ (D ∘ B.aim0 i):=B.nearGauge.mono fun y hy=> by dsimp only; rw [(hy.1 i).1,(hy.1 i).2]; rfl
    unfold normJ; rw [(he'.iteratedFDeriv (𝕜:=ℝ) _).eq_of_nhds,norm_iteratedFDeriv_one]
    have hT:=B.dome i; have hd:DifferentiableAt ℝ (B.aim0 i) 0:= hT.smooth.differentiableAt (by exact_mod_cast (show V.n≠0 from by have ht:=V.depth; omega))
    have hp:DifferentiableAt ℝ D (B.aim0 i 0) := (B.aim_zero i).symm ▸ (hP.smaller V.depth).smooth.differentiableAt (by norm_num)
    rw [fderiv_comp _ (W i j).differentiableAt (hp.comp _ hd),fderiv_comp _ hp hd,B.aim_zero,(W i j).fderiv]
    have hl:‖fderiv ℝ (B.aim0 i) 0‖ ≤ B.helm:= by rw [←norm_iteratedFDeriv_one]; have h:= hT.hops 1 le_rfl (by have ht:=V.depth; omega); simpa only [pow_one] using! h
    refine (ContinuousLinearMap.opNorm_comp_le (W i j) ((fderiv ℝ D 0).comp (fderiv ℝ (B.aim0 i) 0))).trans ((mul_le_mul (he i j) (ContinuousLinearMap.opNorm_comp_le ..) (norm_nonneg _) zero_le_one).trans ?_)
    rw [one_mul]; refine mul_le_mul ?_ hl (norm_nonneg _) (by positivity)
    simpa only [sub_zero] using! hD.miss
  · intro i j; constructor
    · refine (hC i.1 _ (h.horizon 0 (B.a.colorSeat G i) (B.a.colorSeat G j) (by simp))).shimmy (B.nearGauge.mono fun y hy=> (hy.2 i j).1)
    exact (hC i.1 _ (h.peak 0 (B.a.colorSeat G i) (B.a.colorSeat G j) (by simp))).shimmy (B.nearGauge.mono fun y hy=> (hy.2 i j).2)
  intro i j; have he:=B.nearGauge.self_of_nhds.2 i j; rw [he.1,he.2,norm_sub_rev]; unfold C6d C9d; rw [B.aim_zero]
  exact only_price h.shade.1 le_rfl (B.a.colorSeat G i) (B.a.colorSeat G j)
end Barque
end YM.PhysicalNext.Repeat.Sanction
