import YM.Planned.PRIMARY_INTEGRAL_295.Density
import YM.Push.STATIONARY_UNIFORM.Travel
/-!
# Per-occurrence exponential payments vs $̅V$ line length

Even multiwinding paths genuine matrix derivatives. Relative stencil
fixed per use. Does not estimate unmasked leak into monitored tableaux.
No sum approximation over grouped paths -- payments below one link/path.
Tau>0 budget arbitrary after Width.Birth for Teller supplier. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Drupes
open Function Filter Set Metric
open Labels Lattice RG Wilson Pressure Precision Exterior Tree Streets Carrier Bloch Place
open Villa Fizz Fizz.Gush Bazaars Cedar  Oval
open Bunks Little Work.F01 Little.Core Push.Uniform 
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius RealInnerProductSpace Classical
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Gauge} {k n d:ℕ} {c f : Side} {S:StepData c f}

def normL (L:E→L[ℝ] F):ℝ:=‖L‖
lemma normL_pos (L:E→L[ℝ] F):0≤normL L:=norm_nonneg L

/-- Mat linear for *physical* curves; won't infer linear curvature on arbitrary output groups. -/
def cbr (G:Gauge):G.Mat→L[ℝ] G.Color := (G.projectColor.toContinuousLinearMap).comp
   ((1/2:ℝ) • (ContinuousLinearMap.id ℝ G.Mat - ((starL ℝ:G.Mat ≃L[ℝ] G.Mat).toContinuousLinearMap)))
lemma identifies (u:G.El): G.curvature u= cbr G (G.mat u):=by
   unfold Gauge.curvature; rw [G.mat_inv]; rfl

def jetAd (G:Gauge) (X:G.Mat):Pay G:=
   let L:= ContinuousLinearMap.mul ℝ G.Mat; G.projectColor.toContinuousLinearMap ∘L (L.flip (star X) ∘L (L X ∘L G.colorMat.toContinuousLinearMap))

def oneL (G:Gauge):=normL (E:=G.Mat) (F:=G.Color) (cbr G)
lemma hOneL (G:Gauge):0≤oneL G:=normL_pos (E:=G.Mat) (F:=G.Color) _

lemma turned (x:G.El):(G.adjoint x).toContinuousLinearMap=jetAd G (G.mat x):=by ext; rfl
lemma shaders (G:Gauge)(k:ℕ): ∃ C:ℝ, 1≤C∧∀ x:G.El, Allows k (jetAd G) (G.mat x) C:=by
   have he:ContDiff ℝ ω (jetAd G):=by
      unfold jetAd; let L:=ContinuousLinearMap.mul ℝ G.Mat
      have hs : ContDiff ℝ ω (star:G.Mat→G.Mat) := (starL ℝ:G.Mat≃L[ℝ] G.Mat).contDiff
      apply ContDiff.clm_comp contDiff_const
      exact (L.flip.contDiff.comp hs).clm_comp (L.contDiff.clm_comp contDiff_const)
   obtain ⟨C,hC,h⟩:= exists_allows (isCompact_range (f:=G.mat) G.continuous_mat) (fun x _=> he.contDiffAt) k
   refine ⟨C+1,by linarith,fun x=> (h _ (mem_range_self ..)).mono (by linarith)⟩

-- subexponential path cost (not constant per label if normalized)
lemma art (C:ℝ) (hc:0≤C) (G:Gauge)(k:ℕ) :∃ D:ℝ,1≤D∧∀ n, Push.Uniform.travelCost G k n C ≤ D*(1+n)^k:=by
   let A:= Push.Uniform.composeCost k ((Real.exp 1*‖(1:G.Mat)‖)*(1+(2:ℝ)^k)^k) C
   have ha:0≤A:=by unfold A Push.Uniform.composeCost; positivity
   refine ⟨1+A,by linarith,fun n=>?_⟩
   have hy: (1 + (2:ℝ)^k*(1+n))^k ≤ (1+(2:ℝ)^k)^k*(1+n)^k:=by
      rw [←mul_pow]; exact pow_le_pow_left₀ (by positivity) (by have hi:=show 0≤(n:ℝ) from Nat.cast_nonneg _; nlinarith) k
   refine le_trans (b:=A*(1+n)^k) ?_ (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (by positivity))
   unfold A Push.Uniform.travelCost Push.Uniform.composeCost; calc
      _ ≤ (k.factorial:ℝ)*((Real.exp 1*‖(1:G.Mat)‖)*((1+(2:ℝ)^k)^k*(1+n)^k))*(1+C)^k:= by gcongr
      _ = _:=by ring

lemma enroll_speed (C:ℝ) (hc:0≤C)(G:Gauge)(k:ℕ):∀ η:ℝ, 0<η → ∃ D:ℝ,1≤D∧ -- replace colon
   ∀ {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E]{c:Side}{U:E→Config G c}{x:E} (_:∀ i,Allows k (fun y=>G.mat (U y i)) x C)
     (p:Site c)(q:Walk),Allows k (fun y=> (G.adjoint (travel (U y) p q)).toContinuousLinearMap) x (D*Real.exp (η*q.length)) :=by
   obtain ⟨M,hM,hB⟩:=shaders G k; obtain ⟨A,ha,ha'⟩:=art C hc G k
   intro η hη
   let Z:= Push.Uniform.composeCost k M A * widthCost η (k*k)
   have hz :0≤Z:=by unfold Z Push.Uniform.composeCost; have he:= widthCost_ge hη (k*k); positivity
   refine ⟨1+Z,by linarith,?_⟩
   intro E _ _ c U x h p q
   have ht:= (travel_jets (U:=U) h p (Nat.le_refl q.length)).mono (ha' _)
   simp_rw [Drupes.turned]; apply ((hB _).comp (f:=fun y=>G.mat (travel (U y) p q)) ht).mono
   let r:ℝ:=q.length; let u:=1+r
   have he :0≤r:=by unfold r; positivity
   have hu :1≤u^k:=one_le_pow₀ (by unfold u; linarith)
   calc
    Push.Uniform.composeCost k M (A*u^k) ≤ Push.Uniform.composeCost k M A*(1+r)^(k*k):=by
       unfold Push.Uniform.composeCost
       rw [pow_mul, mul_assoc _ ((1+A)^k), ←mul_pow]; apply mul_le_mul_of_nonneg_left _ (by positivity)
       exact pow_le_pow_left₀ (by positivity) (by unfold u at *; nlinarith) _
    _ ≤ Z*Real.exp (η*q.length):= by
       unfold Z; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (by unfold Push.Uniform.composeCost; positivity); exact widthBill η hη _ r he
    _ ≤ _:= by gcongr; linarith

-- For every deterministic function U and ̅V frozen, at any x. k exponential before cut. Or its transpose derivatives. No assumptions *over* stencil.

lemma measured (C:ℝ) (hc:0≤C)(G:Gauge)(k:ℕ):∀ η:ℝ, 0<η → ∃ D:ℝ,1≤D∧
   ∀ {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E]{c:Side}{U V:E→Config G c}{x:E}
    (_:∀ i,Allows k (fun y=>G.mat (U y i)) x C) (_:∀ i,Allows k (fun y=>G.mat (V y i)) x C)
    (p: Site c)(s:Slot), Allows k (fun y=> Little.Core.kink s (V y) (U y) p) x (D*Real.exp (η*s.length)) :=by
   intro η hη; obtain ⟨D,hD,hA⟩:= enroll_speed C hc G k η hη
   let L := (ContinuousLinearMap.apply ℝ G.Color (E:=G.Color)).flip
   let T:=travelCost G k 4 C
   let Y:= 2^k * ‖L‖ * D * (oneL G * T)
   have ht :0≤T:=by unfold T travelCost Push.Uniform.composeCost; positivity
   have hy:0≤Y:=by unfold Y; have h:=hOneL G; positivity
   refine ⟨1+Y,by linarith,?_⟩; intro E _ _ c U V x hU hV p s
   let X := Work.F03.slotFace s p
   let f(y:E):= G.curvature (faceValue (U y) X)
   let g(y:E):=(G.adjoint (travel (V y) p s.walk)).toContinuousLinearMap
   have he(y:E):Little.Core.kink s (V y) (U y) p = L (g y) (f y):=by unfold Little.Core.kink faceValue; rw [travel_at,travel_at,map_zero,zero_add]; rfl
   have hf:Allows k f x (oneL G*T):= by
     simp_rw [f,identifies]; apply Allows.linear
     exacts [travel_jets (U:=U) hU _ (w:=square s.plaq.val.1 s.plaq.val.2) (show _≤4 by simp [square]),le_rfl]
   simp_rw [he]; apply ((hA hV p s.walk).bilinear L (f:=g) hf le_rfl).mono
   have hw : s.walk.length≤s.length:=by unfold Slot.length; omega
   calc
    _ = Y * Real.exp (η*s.walk.length):=by unfold Y; ring
    _ ≤ _:= mul_le_mul (le_add_of_nonneg_left zero_le_one) (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hw) hη.le)) (Real.exp_pos _).le (by positivity)

lemma shot (C:ℝ)(hc:0≤C)(G:Gauge)(k:ℕ)(A:Clip) : ∃ D:ℝ,1≤D ∧
   ∀ {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E]{c:Side}{U:E→Config G c}{x:E}(_:∀ i,Allows k (fun y=>G.mat (U y i)) x C)
     (z:Cell c), Allows k (fun y=> Pressure.shoot A (U y) z) x D :=by
   let M:=travelCost G k 4 C; let D:= |Real.sqrt A.direct| *(oneL G*M)
   have hm:0≤M:=by unfold M travelCost Push.Uniform.composeCost; positivity
   have hd:0≤D:=by unfold D; have h:=hOneL G; positivity
   refine ⟨D+1,by linarith,?_⟩; intro E _ _ c U x h z
   simp only [shoot]; simp_rw [identifies]; have ht : Allows k (fun y=> G.mat (faceValue (U y) z)) x M :=
      travel_jets (U:=U) h z.1 (w:=square _ _) (by simp [square])
   exact (((ht.linear _ le_rfl).smul ..):Allows k _ _ D).mono (show D≤D+1 by linarith)
end YM.Planned.PrimaryIntegral295.Drupes
