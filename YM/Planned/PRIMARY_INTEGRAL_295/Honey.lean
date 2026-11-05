import YM.Planned.PRIMARY_INTEGRAL_295.Bosom
import YM.Planned.PRIMARY_INTEGRAL_295.Density
import YM.Push.STATIONARY_UNIFORM.Prediction

/-!
# Core chamber absolute log radius Supplies for actual S.Frame prediction

Buy after L only; K threshold depends stage. `Inputs` verified including
unit-card colors W.Core.Th authentic trajectory on augmented log space.
Does not check pricer on actual near-frozen admissible records. Does not
exchange conditionals.Measure. Radius for analytic computations unscaled v.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Honey
open Function Filter Set Metric
open Labels Lattice RG Wilson Pressure Precision Exterior Tree Streets Carrier Bloch Place
open Villa Fizz Fizz.Gush Bazaars Cedar  Oval
open Bunks Little Work.F01 Little.Core
open Progress.StationaryScenes.Green Push.Uniform Floor Glints Windows Density Trinket
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius RealInnerProductSpace Classical
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Gauge} {k n d:ℕ} {c f : Side} {S:StepData c f}

abbrev Hollow (G: Gauge) (c f:Side):= Dir G c× Temps G f
section
variable (K:Core G S)
def boxCard (G:Gauge):ℝ:= 1 + (Fintype.card G.ColorIndex:ℝ)
lemma boxCard_pos (G:Gauge) :1≤boxCard G:=le_add_of_nonneg_right (by positivity)
lemma reach_fee : ‖Bosom.placed K‖ ≤ boxCard G:=by
   have h0 := boxCard_pos G; apply ContinuousLinearMap.opNorm_le_of_unit_norm (zero_le_one.trans h0); intro a ha
   apply (pi_norm_le_iff_of_nonneg (zero_le_one.trans h0)).2; intro i
   obtain ⟨⟨x,i⟩,rfl⟩:= (Work.E03.poleEquiv f).surjective i
   let e : Bond f:=(x,i); change ‖collect G (K.reachable a) e‖≤_; rw [Bosom.count_root]
   split <;> rename_i h
   · rw [norm_zero]; exact zero_le_one.trans h0
   let v:G.Color:=WithLp.toLp 2 fun j=> a (e,j)
   have hv(j:G.ColorIndex): (v j)^2≤1:=by
      have hx: |v j|≤1:= (norm_le_pi_norm a _).trans ha.le; exact (sq_abs _).symm.trans_le ((pow_le_pow_left₀ (abs_nonneg _) hx _).trans_eq (one_pow _))
   have he : ‖v‖^2 ≤ (Fintype.card G.ColorIndex:ℝ):= by rw [EuclideanSpace.real_norm_sq_eq]; simpa using Finset.sum_le_sum (s:=Finset.univ) (fun i _=> hv i)
   change ‖v‖≤_; unfold boxCard at *; nlinarith
end

-- total chamber with oriented ̅V plus Q; prove even for any L fixed.
def termook (s:Signed) (K:Core G S) : Hollow G c f → Config G f:= Function.uncurry (K.seek s)

/-- Pregrade primitive ambient exponential uniform cost at all ambient
points in unit ball. `Γ Inputs` on actual orientations. -/
lemma winding (G: Gauge) (n:ℕ) :∃ C:ℝ,1≤C ∧ ‖(1:G.Mat)‖ ≤ C ∧ ∀ c f (S:StepData c f), ∀ (K:Core G S) s, Push.Uniform.Inputs (termook s K) n C := by
   let v:=boxCard G; have hh:1≤v:=boxCard_pos G
   obtain ⟨C,hC,h⟩:= Push.Uniform.exists_allows (s:=closedBall (0:G.Color) v) (isCompact_closedBall _ _) (fun i _=> G.exp_jet.contDiffAt (x:=i)) n
   let B:= 1+‖(1:G.Mat)‖+Push.Uniform.composeCost n C v
   have hU:0≤Push.Uniform.composeCost n C v:=by unfold Push.Uniform.composeCost; positivity
   have he:1≤B:=by unfold B; linarith [norm_nonneg (1:G.Mat)]
   have hX : B ≤ 2^n*B*B:=by
      have he':1≤(2:ℝ)^n:=one_le_pow₀ (by norm_num); nlinarith [mul_le_mul_of_nonneg_right he' (show 0≤B^2 by positivity)]
   have hz : ‖(1:G.Mat)‖ ≤B:= by unfold B; linarith
   refine ⟨2^n*B*B,he.trans hX,hz.trans hX,fun c f S K s=> ?_⟩
   let T:=Hollow G c f
   have hl (e:Bond _)(x:T)(hp:‖x‖≤1): Allows n (fun y:T=>G.mat (menu (S:=S) y.1 (K.reachable y.2) e)) x (2^n*B*B):=by
      have hx (L:T→L[ℝ] G.Color) (hr:‖L‖≤v): Allows n (fun y=>G.mat (G.lieExp (L y))) x B:=by
         have hw : ‖L x‖≤v:= ((L.le_opNorm _).trans ((mul_le_of_le_one_right (norm_nonneg _) hp).trans hr))
         exact ((h _ (mem_closedBall.mpr (by rwa [dist_zero_right]))).comp (Push.Uniform.allows_linear hr hw)).mono
            (le_add_of_nonneg_left (by positivity))
      let A(y:T):=G.lieExp (collect G (K.reachable y.2) e); let W(y:T):=replica S.ratio (represent y.1) e
      have hA : Allows n (fun y=> G.mat (A y)) x B:=by
         let L:T→L[ℝ] G.Color:= ContinuousLinearMap.proj (φ:=fun _=>G.Color) (faceAlias f e) ∘L Bosom.placed K ∘L ContinuousLinearMap.snd ..
         have he : ‖L‖≤v:=by
             apply ContinuousLinearMap.opNorm_le_of_unit_norm (zero_le_one.trans hh); intro w hw
             change ‖collect G (K.reachable w.2) e‖ ≤ _
             apply (norm_le_pi_norm (K.reachable w.2) (pole e)).trans
             have hy: ‖w.2‖≤1:=(norm_snd_le _).trans hw.le
             exact ((Bosom.placed K).le_opNorm w.2).trans ((mul_le_of_le_one_right (norm_nonneg _) hy).trans (reach_fee K))
         exact hx L he
      have hW : Allows n (fun y=> G.mat (W y)) x B:=by
         unfold W replica; split
         · apply Push.Uniform.allows_const; rw [G.mat_one]; exact hz
         simp_rw [Work.F03.represent_link]
         let i:Body 1 c := (S.ratio.parent e.1, Exterior.coord e.2)
         let L:T→L[ℝ] G.Color:= ContinuousLinearMap.proj i ∘L ContinuousLinearMap.fst ..
         have he: ‖L‖≤v:=by
            apply ContinuousLinearMap.opNorm_le_of_unit_norm (zero_le_one.trans hh); intro y hy
            exact ((norm_le_pi_norm y.1 i).trans (norm_fst_le y)).trans (hy.le.trans hh)
         exact hx L he
      exact Allows.times hA hW
   refine ⟨?_,zero_le_one.trans (he.trans hX),fun e x hx=>?_⟩
   · change K.seek s (0:Dir G c) (0:Temps G f)=1; unfold seek menu
     rw [link_one,replica_one,Bosom.reaches_zero,show collect G 0=_ from ?_, Work.G07.at_zero_increment]; ext; simp [pull,Lattice.Step.read];
     rfl
   change Allows n (fun y:T=>G.mat (pull s 0 (menu (S:=S) y.1 (K.reachable y.2)) e)) x _
   unfold pull Lattice.Step.read; split
   · exact (hl _ x hx).inverse (f:=fun y=>_)
   exact hl _ x hx

section Prediction
-- Need n finite. radius positive even if c=1 infinite zone.
theorem binning (G: Gauge) (n:ℕ) (Q : KernelChoices) (P:Patch): ∃ (r C:ℝ), 0<r ∧ 1≤C ∧ r ≤ 1 ∧ ∀ (c f) (S:StepData c f), S.kernel=Q→S.patch=P→
    ∀ (K:Core G S) s (e:Bond c) (x:Hollow G c f), ‖x‖≤r → Allows n (fun y=> G.mat (K.target s y.1 y.2 e)) x C:=by
   classical
   let k:=n+2
   obtain ⟨C,hC,hB,H⟩:=winding G (k+1)
   obtain ⟨V,hV,Hv⟩:=Push.Uniform.exp_receipt G (k+1)
   obtain ⟨D,δ,hD⟩:=Push.Uniform.log_receipt G
   obtain ⟨W,r,hp,hR⟩:=Push.Uniform.focus_receipt G k
   let M:=predictionRadius P G Q k V C D δ r
   let F₀:StepData 1 P.L:=⟨P,Q,by simp⟩
   have he :0<M:=by
      let U:ℝ→Config G P.L:=fun _=>1
      apply Push.Uniform.prediction_radius_pos F₀ (U:=U) ?_ (by omega) Hv hD hR
      refine ⟨rfl,zero_le_one.trans hC,fun i x _=>?_⟩
      apply Push.Uniform.allows_const; change ‖G.mat (1:G.El)‖ ≤ _; rw [G.mat_one]; exact hB
   let T:=Push.Uniform.composeCost k W (Push.Uniform.connectorCost P G k V C)
   refine ⟨min 1 (M/2),max T 1, lt_min zero_lt_one (half_pos he),le_max_right ..,min_le_left ..,fun c f S hk hP K s e x hx=>?_⟩
   obtain ⟨rfl⟩:=hk; obtain ⟨rfl⟩:=hP
   have ha:= Push.Uniform.prediction_pay S (H c f S K s) (show 2≤k by omega) Hv hD hR x (mem_ball.mpr ?_) (t:=Push.SectorMeasure.Oriented.choice s K.k) e
   · exact (ha.order (by omega : n≤k)).mono (le_max_left ..)
   rw [dist_zero_right]; exact (hx.trans (min_le_right ..)).trans_lt (half_lt_self he)
end Prediction

section cold
-- projection/slice cost for D entry. when weights decay, LuHF constant.
lemma pulse_left {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] (L:E→L[ℝ] F) {f:F→H}{x:E}{C:ℝ} (h:Allows n f (L x) C)
    (hs:‖L‖≤1) : Allows n (f ∘ L) x C:=by
   refine ⟨h.analytic.comp _ L.contDiff.contDiffAt,fun k hk=>?_⟩
   rw [WardBin.Lies.liner L (h.analytic.of_le le_top)]; apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans
   simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]; exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg L) hs)).trans (h.norm_le k hk)

lemma banded {r:E}{C:ℝ} {f:E×F→G.Color} (x:F)(h : Allows (n+1) f (r,0) C) (hx:‖x‖≤1):
    Allows n (fun w=> (fderiv ℝ (fun y:F=> f (w,y)) 0) x) r C:=by
   let L:G.Color ≃L[ℝ] G.Color:=ContinuousLinearEquiv.refl ..
   let V:=ContinuousLinearMap.inr ℝ E F; let T:=ContinuousLinearMap.inl ℝ E F
   let F':(E×F→L[ℝ] G.Color)→L[ℝ] G.Color:= ContinuousLinearMap.apply ℝ G.Color (V x)
   have he : ‖T‖ ≤ 1:=by
      apply ContinuousLinearMap.opNorm_le_of_unit_norm zero_le_one; intro x hx; simp [T,hx]
   have hf:‖F'‖≤1:=by
      apply ContinuousLinearMap.opNorm_le_of_unit_norm zero_le_one; intro v hv; exact (v.le_opNorm _).trans (by simp [V,hv,hx])
   have hr : Allows n (fderiv ℝ f) (T r) C:=by
     refine ⟨h.analytic.fderiv_right le_top,fun k hk=>?_⟩
     rw [norm_iteratedFDeriv_fderiv]; exact h.norm_le (k+1) (by omega)
   have hG:= (pulse_left T hr he).linear F' hf; rw [one_mul] at hG; apply hG.germ
   have hR : ∀ᶠ y in 𝓝 (r, (0:F)), ContDiffAt ℝ ω f y := h.analytic.eventually (by simp)
   have ht := T.continuous.tendsto r; -- fix
   filter_upwards [ht.eventually hR] with w hw
   let q (y:F): E×F:= (w,y)
   have hx: HasFDerivAt q V 0 := by convert (hasFDerivAt_const (𝕜:=ℝ) w (0:F)).prodMk (hasFDerivAt_id (𝕜:=ℝ) (0:F)) using 1 <;> rfl
   change F' (fderiv ℝ f (T w))= fderiv ℝ (f ∘ q) 0 x
   rw [fderiv_comp _ (show DifferentiableAt ℝ f (q 0) from hw.differentiableAt (by simp)) hx.differentiableAt, hx.fderiv]; rfl
end cold
end YM.Planned.PrimaryIntegral295.Honey
