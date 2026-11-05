import YM.TraceExtension.Swift.Payer
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Swift
open Function Filter Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Push.Uniform Det Lamp Analysis Matrix Finset
open Metric Filch Turret Shepherd AnalyticBridge VerifiedReset Extra.Iteration SectorAffine Offset Fen Kits Pills Loft Xo Zn StressFlux MeasureTheory
open PhysicalNext.JointLoad.Heir
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{k m:ℕ}{n:Side}{A c:ℝ}
lemma shortE(G:Gauge)(n:Side)(L: Directions G n→L[ℝ] Link G n)(h:L=edgeColor.symm.toContinuousLinearMap): ‖L‖≤1:=by
   apply L.opNorm_le_bound zero_le_one; intro x; rw [one_mul]; refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr ?_; rintro ⟨i,k,j⟩; obtain ⟨k,rfl⟩:= axisEquiv.surjective k; change ‖edgeColor (L x) (i,k) j‖≤‖x‖; rw[h]; simp only [ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply]; apply le_trans (b:=‖x (i,k)‖) _ (norm_le_pi_norm x _); change |x (i,k) j| ≤ _; rw [← EuclideanSpace.basisFun_inner G.ColorIndex ℝ]; exact (abs_real_inner_le_norm ..).trans (by simp)
lemma biasU {F:Peat G n}(h:Allows k (F ∘ input G n) 0 A): Allows k (F ∘ increment 1) 0 A:=by
    let L:Directions G n→L[ℝ] Link G n:=edgeColor.symm.toContinuousLinearMap
    rw [show F ∘ increment 1=(F ∘ input G n) ∘ L from ?_]; exact pre_short L (f:=F ∘ input G n) (x:=0) ((map_zero L).symm ▸ h) (shortE G n L rfl)
    funext i; apply congr_arg F;funext a; change G.lieExp _ * 1=_;rw [mul_one,input_color]; unfold L;simp
lemma shallow (S:Stage):∀ᶠ x in atTop,0 < thetaP x∧ x⁻¹ ≤ sash S x ∧ sash S x ≤1:=by
    filter_upwards [eventually_gt_atTop (1:ℝ),sash_ok S 1 zero_lt_one] with x hx h
    have hp: 0<x:=lt_trans zero_lt_one hx; have ht:0<thetaP x:=mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr hp)) (wakeZ x)
    refine ⟨ht,(le_trans ?_ (le_mul_of_one_le_right ht.le (show 1 ≤ (1+(high x:ℝ))^S.power from one_le_pow₀ (by simp)))),h⟩; refine le_trans ?_ (le_mul_of_one_le_right (inv_pos.mpr (Real.sqrt_pos.mpr hp)).le (wok 1 x (by norm_num)))
    apply inv_anti₀ (Real.sqrt_pos.mpr hp); exact (Real.sqrt_le_left hp.le).mpr (by nlinarith)
where
 wakeZ(x):0<fog x:=Zn.wake ..
lemma astride(S:Stage)(A:ℝ)(ha:1≤ A):∀ᶠ x:ℝ in atTop, let t:= sash S x; t≤1 ∧ (∀ i:ℕ,i≤4→ calorie x≤(thinM x+thinM x)*t^(5-i)) ∧
       4*x*((thinM x+thinM x)*evenR 5 A*t^(5:ℕ))≤ swole x:=by
    let f(x:ℝ):= (1+(high x:ℝ))^S.power; have hf:ConstMass 0 f:= (mass zero_le_one|>.gather expansion).crop _
    let V(x):= 4*((thinM x+thinM x)*evenR 5 A*f x^5)*fog x^3
    have hP: ConstMass (0+(1/200+0+0)+((3:ℕ)* (1:ℝ))) V:=by
        have ht:= (((waveM (1/200)).gather (waveM (1/200))).prod (mass (show 0 ≤ evenR 5 A by unfold evenR; positivity))); exact ((mass (show (0:ℝ) ≤ 4 by norm_num)).prod (ht.prod (hf.crop 5))).prod ((waveM 1).pow 3)
    filter_upwards [shallow S,eventually_gt_atTop (1:ℝ),hP 5 (by norm_num), wave_sub 5 (1/4) (by norm_num)] with x hx he h ht
    intro t; have hv: 0<x:=lt_trans zero_lt_one he; obtain ⟨h₁,h₂,h₃⟩:=hx; refine ⟨h₃,fun i hi=>?_,?_⟩
    · have hz :1 ≤ thinM x:=wok _ _ (by norm_num); refine le_trans ?_ (le_mul_of_one_le_left (pow_nonneg (h₁' h₂ hv).le _) (show 1 ≤ thinM x+thinM x by linarith)); unfold calorie; rw [← inv_pow]; apply le_trans (pow_le_pow_left₀ (by positivity) h₂ _) (pow_le_pow_of_le_one (h₁' h₂ hv).le h₃ (by omega))
    let t₀:=thetaP x; change _ ≤ t₀^ (2:ℕ)*x^ (-(1/100:ℝ)); rw [show 4*x*((thinM x+thinM x)*evenR 5 A*t^ (5:ℕ))=t₀^(2:ℕ)*(V x *(x*(Real.sqrt x)⁻¹^ (3:ℕ))) from ?_]; swap; · unfold t t₀ V sash thetaP f; ring
    apply mul_le_mul_of_nonneg_left _ (show 0≤t₀^ (2:ℕ) from sq_nonneg _)
    refine le_trans (mul_le_mul_of_nonneg_right (h.2.trans ht) (by positivity : 0≤ x*(Real.sqrt x)⁻¹ ^ (3:ℕ))) ?_
    rw [show x*(Real.sqrt x)⁻¹^ (3:ℕ)= x^(-(1/2:ℝ)) from ?_, ← Real.rpow_add hv]; rotate_left
    · rw[Real.rpow_neg hv.le,← Real.sqrt_eq_rpow];field_simp;rw[Real.sq_sqrt hv.le]
    exact Real.rpow_le_rpow_of_exponent_le he.le (by norm_num)
where
 h₁' {x t:ℝ} (h:x⁻¹ ≤ t)(he:0<x):0<t:=lt_of_lt_of_le (inv_pos.mpr he) h
lemma stem (hG:G.Simple) (S:Stage)(k:ℕ)(hk:5 ≤ k)(D:ℝ)(hd:1≤D):∃ C:ℝ,0≤ C ∧∀ᶠ x:ℝ in atTop,∀ (n:Side)(R:Rep G n)(J:Dart G n) (F:Peat G n)(b:Axis)(H:Made S x R),|R.beta|≤4*x →
    HearthV (rill F (YCore x J b)) (ExtS n x) k (thinM x) C → Splendor (boom (Meld J x) b 0) (ExtS n x) k (thinM x) C →
    let K:=boom (Meld J x) b 0-rill F (YCore x J b); Allows 4 (K ∘ input G n) 0 (calorie x) →
    ∀ p:Directions G n, ‖p‖≤D→ Allows k (minor (R.beta • K) (sash S x)) p (swole x):=by
    obtain ⟨P,hP,H⟩:= atp G (k+1) D (by positivity)
    refine ⟨P,hP,?_⟩; filter_upwards [astride S D hd,eventually_gt_atTop (1:ℝ)] with x hx hX n R J F b hM h hp he K ht p hb
    let W:= ExtS n x; let U:= (increment (1:Config G n)); let s:= sash S x; obtain ⟨hv,hh,hK⟩:=hx
    have hs:0 < s:= (pet x hX.le S).1; have hd:0≤ D:=by positivity
    have hz(y:Directions G n)(hy:‖y‖≤ D*s): Allows k (K ∘ U) y (thinM x+thinM x):=by
        have ht(i): Allows (k+1) (fun v=> G.mat (U v i)) y P:=H _ _ _ (hy.trans (mul_le_of_le_one_right hd hv)) i
        have he:= he.tickets (Directions G n) U y (fun i=> (ht i).order (by omega)); have hf:= (hp.price (Directions G n) U y ht).smul (-1); rw [abs_neg,abs_one,one_mul] at hf
        exact (he.add hf).germ (Eventually.of_forall fun i=> by simp only [neg_one_smul]; rfl
        )
    have hi := heaven (f:=K ∘ U) 5 D hd hs.le hv hz (show _ from (hz 0 (by rw[norm_zero]; positivity)).nonneg) hk (fun i hi=> ((biasU ht).norm_le i (by omega)).trans (hh i (by omega))) p hb; exact (hi.smul R.beta).mono ((mul_le_mul_of_nonneg_right h hi.nonneg).trans hK)
end YM.Trace.Swift
