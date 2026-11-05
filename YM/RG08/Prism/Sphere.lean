import YM.RG08.Prism.Truce
import YM.Work.F05.Measure

/-! # Pack thermostat coordinates and account exact analytic log ratio near 1. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Prism
open Function Matrix Lattice Exterior Wilson RG Precision Stationary RG08.Line Fold Drum Bloch Laurent Finset Filter Glyph Room Camera Tack Mount MvPolynomial
open Rudder Carrel Aggregate Spar Symmetry RG08.Cast Work.F05 Tree
open scoped Classical Matrix ContDiff Topology BigOperators InnerProductSpace PowerSeries
variable {G:Gauge}{c f:Side}{S:StepData c f}(F:Forest S.ratio)(A B:Bed){C:Castle G}{Z:ChartRatio G}

abbrev Lex (F:Forest S.ratio)(G:Gauge) (O:Type):=Cellar (Camera.Raw (Precision.Key F G) O)
variable {O:Type}[Fintype O](t:Lines G c 1→O)
def implant := modes (speak (grace G S F A B) (fir S) t)
def tone (x:Lex F G O):=low S (Camera.roll (implant F A B t) x)
def flame (x:Lex F G O):=high S (Camera.roll (implant F A B t) x)
def frock (x:Lex F G O): AxisChart G F:=fun i=>tone F A B t x (Pressure.pole i.val)
def trophy (Z:ChartRatio G):Still (Camera.Raw (Precision.Key F G) O):=Work.F05.toll F Z ∘ frock F A B t
lemma uniform (i):Pace (implant F A B t i):=paced ..
lemma seated : Camera.roll (implant F A B t) 0=0:=by change (speak (grace G S F A B) (fir S) t *ᵥ 0)=_;rw [Matrix.mulVec_zero]
lemma tone_pace:Pace (tone F A B t):= (low S).contDiff.contDiffAt.comp _ (Camera.roll_pace (fun i => uniform F A B t i))
lemma frock_pace:Pace (frock F A B t):=contDiffAt_pi.mpr (fun i=> (contDiffAt_apply ℝ G.Color (Pressure.pole i.val) _).comp _ (tone_pace ..))
lemma central: frock F A B t 0=0:=by funext i;unfold frock tone; rw [seated,map_zero];rfl
lemma trophy_pace (h:LocalRatio Z): Pace (trophy F A B t Z):=by
 unfold trophy Work.F05.toll Function.comp
 apply contDiffAt_prod; intro i _
 have hj : ContDiffAt ℝ ω Z.J (frock F A B t 0 i) := by
   rw [central]
   exact h.germ 0 (Metric.mem_ball_self h.patch)
 exact hj.comp 0 ((contDiffAt_pi.mp (frock_pace F A B t)) i)
lemma trophy_root(h:LocalRatio Z): trophy F A B t Z 0=1:=by unfold trophy Work.F05.toll Function.comp;rw [central];simp [h.anchored]
lemma tone_trunk (x:Lex F G O)(e:Edge (Site f))(he:e∈F.trunks):tone F A B t x (Pressure.pole e)=0:=by
 let V:=grace G S F A B
 have ht:onTree F (Proceed.wx S (speak V (fir S) t *ᵥ x)):=by
    change onTree F (fun i=>(speak _ _ _ *ᵥ _) (lowSlot S i))
    erw [(speak_zone V (fir S) t x).1] -- fir inl rw
    intro i y hy
    have hm: V.mean *ᵥ ((x ∘ Sum.inr) ∘ t)=iris G S F *ᵥ ((V.dark*V.vᵀ*(V.κ • V.Dᵀ)) *ᵥ ((x ∘ Sum.inr) ∘ t)):=by rw [Matrix.mulVec_mulVec,Drum.mean,Drum.g];simp only [Matrix.mul_assoc];rfl
    change (V.v *ᵥ (x ∘ Sum.inl)) (y.1, coord y.2, i) +
      (V.mean *ᵥ ((x ∘ Sum.inr) ∘ t)) (y.1, coord y.2, i) = 0
    have hv : (V.v *ᵥ (x ∘ Sum.inl)) (y.1, coord y.2, i) = 0 :=
      away G S F (x ∘ Sum.inl) i y hy
    rw [hm, hv, zero_add]
    exact away G S F _ i y hy
 ext i; exact ht i e he
lemma fad (h:LocalRatio Z): (fun x: Lex F G O=>∑ e:Edge (Site f),Real.log (Z.J (tone F A B t x (Pressure.pole e))))=ᶠ[𝓝 0] Real.log ∘ trophy F A B t Z:=by
 have ht :∀ᶠ x:Lex F G O in 𝓝 0, ∀ i:F.Free, 0 < Z.J (frock F A B t x i):=eventually_all.mpr (fun i=>by
    have hh : Tendsto (fun x=>frock F A B t x i) (𝓝 0) (𝓝 (0:G.Color)):=by
       simpa only [central,Pi.zero_apply] using! ((contDiffAt_pi.mp (frock_pace F A B t)) i).continuousAt.tendsto
    exact (hh.eventually (Metric.ball_mem_nhds _ h.patch)).mono fun _ hx=>h.pos _ hx)
 filter_upwards [ht] with x hx
 let K (i:Edge (Site f)):=Real.log (Z.J (tone F A B t x (Pressure.pole i)))
 let w:F.Free↪Edge (Site f):= Function.Embedding.subtype _
 have hu: (∑ i,K i)=(∑ i∈(Finset.univ.image w),K i):= (sum_subset (subset_univ _) (fun i _ hi=>by
   have hb:i∈F.trunks:=by by_contra! hO; exact hi (Finset.mem_image.mpr ⟨(⟨i,hO⟩:F.Free),Finset.mem_univ _,rfl⟩)
   unfold K;rw [tone_trunk _ _ _ _ _ _ hb,h.anchored,Real.log_one])).symm
 change (∑ i,K i)= Real.log (∏ i,Z.J (frock F A B t x i))
 rw [Real.log_prod (by intros i hi; exact (hx i).ne'),hu,Finset.sum_image (fun _ _ _ _ h=>w.injective h)];rfl

end YM.RG08.Prism
