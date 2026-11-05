import YM.RG12.Shadows.Snow
/-! Retain order per temperature on bona fide projections on Hot platform -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Sanction
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Silica Eider Metric Set Gaussian Tablet Quill Baffle Prism Brim Lotus Peak
open WardBin.Lies Push.PriceCompiler Foramen Gate Planned.AtomRegular.Foliage
open YM.RG12.Shadows
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{V:Loom G}
section
variable {X E F:Type}[NormedAddCommGroup X][NormedSpace ℝ X] [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable [FiniteDimensional ℝ X][FiniteDimensional ℝ E]
-- include generic J argument avoid TC Prof
private lemma kinetic (P:X×E→F)(c:X){a:ℝ}(hA:0<a)
    (S : Set (X×E))(hh:S=closedBall c a ×ˢ closedBall 0 1)(hP:∀ x∈ S,ContDiffAt ℝ (↑(2:ℕ)) P x):∃ M:ℝ,0<M ∧ ∀ (b:E),‖b‖≤1→
       Brush 2 M 1 (fun y:X=>P (y,b)) c ∧ ‖fderiv ℝ (fun y:X=>P (y,b)) c - fderiv ℝ (fun y:X=>P (y,-b)) c‖ ≤ M*(2*‖b‖):=by
    subst S; let S:=closedBall c a ×ˢ closedBall (0:E) 1; haveI:=FiniteDimensional.proper ℝ X; haveI:=FiniteDimensional.proper ℝ E
    obtain ⟨M,hM,hm⟩:=Brush.compact (show IsCompact S from (isCompact_closedBall ..).prod (isCompact_closedBall ..)) hP
    have hk(b:E)(h:‖b‖≤1):((c,b):X×E)∈S:=⟨mem_closedBall_self hA.le, mem_closedBall_zero_iff.mpr h⟩
    let t:=1+‖c‖; have ht:1≤t:=le_add_of_nonneg_right (norm_nonneg _)
    refine ⟨(2*M)*(1+(1+(1+t)))^2+M, by positivity,fun b hb=>?_⟩
    let L:=ContinuousLinearMap.inl ℝ X E; have he : ‖L‖ ≤ 1:=ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun i=> by simp [L,Prod.norm_def]
    let u:X→X×E:=fun i=>(i,b); have hu:Brush 2 (1+t) 1 u c := by
       let B:X×E:=(0,b); have hx:‖B‖≤1:=by change max ‖(0:X)‖ ‖b‖≤_; exact max_le (by simp) hb
       have hh: Brush 2 t 1 L c:= Brush.linearB L (by simp [L,Prod.norm_def,t]) (by rw [mul_one]; exact he.trans ht) zero_le_one
       refine (((Brush.certified zero_le_one B).climb hx le_rfl).gathering hh).shimmy (Eventually.of_forall (fun i=> by simp [u,B,L]))
    have hl(b:E)(he:‖b‖≤1): fderiv ℝ (fun y:X=> P (y,b)) c=(fderiv ℝ P (c,b)).comp L:= by
       let W (y:X):=(y,b); exact ((hP _ (hk b he)).differentiableAt (by norm_num)|>.hasFDerivAt.comp (f:=W) c (hasFDerivAt_prodMk_left c b)).fderiv
    have hg:‖-b‖≤1:=by rwa [norm_neg]
    constructor
    · have hg:= (hu.pine (hm _ (hk b hb))).trim; rw [mul_one, show Nat.factorial 2=2 from rfl,Nat.cast_ofNat] at hg; exact hg.climb (le_add_of_nonneg_right hM.le) le_rfl
    rw [hl b hb,hl (-b) hg,← ContinuousLinearMap.sub_comp]; have ht : Convex ℝ S:= (convex_closedBall ..).prod (convex_closedBall ..)
    have hy:= Convex.norm_image_sub_le_of_norm_fderiv_le (s:=S) (f:=fderiv ℝ P) (fun x hx=> ((hP x hx).fderiv_right (m:=↑(1:ℕ)) (by norm_num)).differentiableAt (by norm_num)) (fun x hx=> price_two (settled.mp (hm x hx)) le_rfl) ht (hk (-b) hg) (hk b hb)
    have hx : ‖((c,b):X×E)-(c,-b)‖ ≤ 2*‖b‖:= by
      change max ‖c-c‖ ‖b- -b‖ ≤ _; rw [sub_self,norm_zero,two_mul]; exact max_le (by positivity) ((norm_sub_le ..).trans_eq (by rw [norm_neg]))
    apply (ContinuousLinearMap.opNorm_comp_le ..).trans; apply (mul_le_of_le_one_right (norm_nonneg _) he).trans; apply hy.trans
    exact mul_le_mul (le_add_of_nonneg_left (by positivity)) hx (norm_nonneg _) (by positivity)
lemma angular (P:X×E→F)(c:X){a:ℝ}(hA:0<a)
    (S:Set (X×E))(hh:S=closedBall c a ×ˢ closedBall 0 1)(hP:∀ x∈ S,ContDiffAt ℝ (↑(2:ℕ)) P x)(K:ℝ):
    ∃ Q:ℝ, 0≤Q ∧∀ (J:Type)[NormedAddCommGroup J][NormedSpace ℝ J](U:J→X)(s:ℝ),U 0=c→Brush 2 K s U 0→∀ b:E,‖b‖≤1→
          Brush 2 Q (Q*s) (fun y=>P (U y,b)) 0 ∧ normJ 1 (fun y=>P (U y,b)-P (U y,-b)) 0 ≤ (Q*‖b‖)*s:=by
    obtain ⟨M,hM,hm⟩:=kinetic P c hA S hh hP
    let q:=2*M*(1+|K|)+(1+|K|)
    have hq: 2*M * |K| ≤ q:= by unfold q; rw [mul_add, mul_one]; linarith only [hM,abs_nonneg K]
    have hq':2*M≤q:= by unfold q; rw [mul_add,mul_one]; nlinarith only [hM,abs_nonneg K]
    refine ⟨q,by positivity, fun J _ _ U s hC h b hb=>?_⟩; obtain ⟨hv,hh⟩:=hm b hb; have hz:‖-b‖≤1:=by rwa [norm_neg]
    constructor
    · let f (x:X):= P (x,b); have hg:= h.pine (show Brush 2 M 1 f (U 0) from hC.symm ▸ hv)
      rw [show Nat.factorial 2=2 from rfl,Nat.cast_ofNat] at hg
      exact hg.climb hq' (mul_le_mul_of_nonneg_right (by unfold q; nlinarith only [hM,abs_nonneg K,le_abs_self K]) h.pos)
    let f (t:E)(x:X) := P (x,t)
    have hP t (hs:‖t‖≤1):DifferentiableAt ℝ (f t) (U 0):=hC.symm ▸ ((hm t hs).1.smooth.differentiableAt (by norm_num))
    have hy:=h.smooth.differentiableAt (by norm_num)
    change normJ 1 (f b∘U-f (-b)∘U) _ ≤ _; rw [normJ,norm_iteratedFDeriv_one,fderiv_sub ((hP b hb).comp (0:J) hy) ((hP (-b) hz).comp 0 hy), fderiv_comp 0 (hP b hb) hy, fderiv_comp 0 (hP (-b) hz) hy,hC,← ContinuousLinearMap.sub_comp]
    apply (ContinuousLinearMap.opNorm_comp_le ..).trans; rw [← norm_iteratedFDeriv_one]; have hU:=h.order 1 (by norm_num); rw [pow_one] at hU
    apply (mul_le_mul hh hU (norm_nonneg _) (by positivity)).trans
    calc
      _ = ((2*M*K)* ‖b‖)*s:=by ring
      _ ≤ _:=by have hs:=h.pos; gcongr; exact (mul_le_mul_of_nonneg_left (le_abs_self K) (by positivity)).trans hq
end
section compact
variable {d a K:ℝ}(χ:Chi)(h:Canary G d a)
include h
lemma optics9 : ∃ R:ℝ,0≤ R∧∀ (J:Type)[NormedAddCommGroup J][NormedSpace ℝ J](U:J→G.Mat)(s:ℝ),U 0=1→ Brush 2 K s U 0→∀ b:G.Color,‖b‖≤1→
    Brush 2 R (R*s) (fun y=>Eider.plume G χ d (U y) b) (0:J) ∧ Brush 2 R (R*s) (fun y=>palm G χ d (U y) b) (0:J) ∧
    normJ 1 (fun y=>Eider.plume G χ d (U y) b - Eider.plume G χ d (U y) (-b)) (0:J) ≤ (R*‖b‖)*s:=by
  obtain ⟨M,hM,hh⟩:= angular (X:=G.Mat) (uncurry (Eider.plume G χ d)) 1 h.side _ rfl (fun x hx=> (Eider.sheen h χ x.2 x.1 (show ‖x.1-1‖ ≤ _ by simpa only [← dist_eq_norm] using! hx.1)).of_le (WithTop.coe_le_coe.mpr le_top)) K
  obtain ⟨t,ht,hp⟩:= angular (X:=G.Mat) (uncurry (palm G χ d)) 1 h.side _ rfl (fun x hx=> Eider.lift h χ x.1 x.2 (show ‖x.1-1‖≤ _ by simpa only [← dist_eq_norm] using! hx.1)) K
  refine ⟨M+t,add_nonneg hM ht,fun J _ _ U s hz hU i hi=>?_⟩; have hZ:= hU.pos
  have he:= le_add_of_nonneg_right (a:=M) ht; have hv:= le_add_of_nonneg_left (a:=t) hM
  exact ⟨((hh J U s hz hU i hi).1).climb he (mul_le_mul_of_nonneg_right he hZ),((hp J U s hz hU i hi).1).climb hv (mul_le_mul_of_nonneg_right hv hZ),(hh J U s hz hU i hi).2.trans (by gcongr)⟩
end compact
end YM.PhysicalNext.Repeat.Sanction
