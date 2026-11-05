import YM.RemainderComparison.Herbal.Brindle
/-!
 # Cost of sun within Terrain on AUX torus. Includes actual clamped
 gauge evaluation. Presentation can use aggregated functions on global
 sunny domain; Grass recovers quote without requiring smooth from masks.
 No unseen oath on numerics.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Herbal
open Function Filter Metric Set Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure PhysicalNext.Repeat Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange Next.Scheduling ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Sienna Fare Germ Token Aux
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {L : Side} {r j n k N m : ℕ} {Z σ C D W A v u d e t a c' B':ℝ}
variable {c f : Side} {S : StepData c f} {ι : Type} {α : Type}
variable {T : Tube G S} {F : Forest S.ratio} {Θ : ChartRatio G} {k': S.Choices} (ρ:Bid.Dir G c→AxisChart G F) (B:BudgetPoint) (β:ℝ)
local notation "Xs"=> Positions (Uniform.Primary c G)
local notation "Y"=> Poll.Body (Precision.Key F G)
local notation "θ"=> Lapis.orbit F ρ
local notation "v'"=> eaves G L t
local notation "A'"=> Access.apron G L t
local notation "D'"=> wick G L d t
local notation "e'"=> furl G L t
local notation "g"=> gStep β
variable {x:Positions (Uniform.Primary c G)} {K:KernelChoices} {O:Teller G}

variable {U : ℝ × Positions (Uniform.Primary c G) → Poll.Body (Precision.Key F G)→ ℝ} {H : Config G f → ℝ}
variable (P:Eden f G α)(hr:Eden.Culture P N k B.threshold (fineCost G k Z) A 1)
include hr
lemma asZero (y:Xs)(z:Y): P.proofE ρ (0,y) z=0:= by
   refine Finset.sum_eq_zero fun i hi=>?_
   have he:(0:ℝ) < P.grade i:= zero_lt_one.trans_le (hr.base i hi)
   simp only [matte,promote,zero_pow ((show 0<P.grade i from (by exact_mod_cast he)).ne'),zero_smul] -- edit

variable (hw:Weather T F Θ k' ρ B β d t a W u C K O k x L) (hc:Climate G L t d u C β)(hz:PaintSupply G k Z)(hj:j+N≤k)(hj':1≤j)
include hw hc hz hj hj'
def halberd (G:Gauge)(L:Side)(j N:ℕ)(t d u A C:ℝ):= (N:ℝ)*skys j N (wick G L d t) u A C
omit hw hc hr hj hz hj' in
lemma halberd_growth {p q f:ℝ→ℝ} (hp:Reserve G L p)(hq:Reserve G L q)(hf:Reserve G L f)(j N:ℕ)(d:ℝ): Reserve G L fun t=>halberd G L j N t d (p t) (q t) (f t):= (Reserve.const _).mul (skyFeeBudget (Reserve.wig _) hp hq hf ..)

def dawn (w:ℝ × Xs)(z:Y):= Real.exp (P.proofE ρ w z)
def raiseU (V:Config G f):= Real.exp (P.cloaked B β V)
lemma paid (he: halberd G L j N t d u A C * A'≤1)(hh : N * (g*fort G L N t A)≤1)
    (hS:∀ x∈Set.Icc (-1:ℝ) 1, Brush j σ 1 Real.exp x) :
    Playing F ρ β (dawn ρ P) (raiseU B β P) x D' e' u A' (Lantern.clump j (halberd G L j N t d u A C) σ) (Real.exp 1) j ((j+N)*j):=by
   let P':= P.proofE ρ; let S'':=A'; let h : Playing F ρ β P' (P.cloaked B β) x D' e' u A' (halberd G L j N t d u A C) (N*(g^1*fort G L N t A)) j (j+N):=eden ρ B β P (by simpa only [Nat.cast_one] using hr) hz hw hc hj -- casts
   have hf (y) (z):P' (0,y) z=0:=asZero ρ B P hr y z
   have hg (q) (hq:q∈Germ.patch Xs S'' u) (z:Y) (hz:‖z‖≤ D'): ‖P' q z‖≤1 := by
     let p:ℝ×Xs:=(0,q.2); have hp': p∈Germ.patch Xs A' u := ⟨mem_ball_self (hc.g_pos.trans hc.below),hq.2⟩
     let B':=halberd G L j N t d u A C; have hy i (hi:i∈Germ.patch Xs A' u) := (h.tagGerm.budget i hi z hz).smaller hj'
     have hH := ((convex_ball (0:ℝ) (A')).prod (convex_ball (0:Xs) u)).norm_image_sub_le_of_norm_fderiv_le (f:=fun x=>P' x z) (fun i hi=> (hy i hi).smooth.differentiableAt (by simp)) (fun i hi=>show ‖fderiv ℝ (fun x=>P' x z) i‖ ≤ B' from by rw [← norm_iteratedFDeriv_one]; exact (Brush.offer.mp (hy i hi)).inside 1 le_rfl) hp' hq
     have hl : ‖q-p‖≤ S'':= by rw [Prod.norm_def,max_le_iff]; unfold p; simp only [Prod.fst_sub,Prod.snd_sub,sub_zero,sub_self,norm_zero]; exact ⟨((patch_test ..).1 hq).1.le,(hc.g_pos.trans hc.below).le⟩
     rw [show P' p z=0 from hf ..,sub_zero] at hH
     exact hH.trans ((mul_le_mul_of_nonneg_left hl h.tagGerm.expense).trans he)
   refine ⟨h.tagGerm.exponents hg hS (fun i hi z=> by rw [hf,abs_zero]; exact zero_le_one),⟨Real.continuous_exp.comp_stronglyMeasurable h.group.bore, fun i j=>congr_arg Real.exp (h.group.gauge i j), fun i=>?_⟩,fun _ hi z hz=>congr_arg Real.exp (h.speak _ hi z hz)⟩
   unfold raiseU; rw [Real.norm_of_nonneg (Real.exp_pos _).le]
   apply Real.exp_le_exp.mpr; apply ((le_abs_self _).trans (h.group.rich i)).trans; rwa [pow_one]

section phaseBud
omit hw hc hz hj hj' hr
lemma paidGrit (j N :ℕ) {p q H:ℝ→ℝ}(hp:Reserve G L p)(hq:Reserve G L q)(hf:Reserve G L H) (d:ℝ): ∀ᶠ t in atTop,
    halberd G L j N t d (p t) (q t) (H t) * Access.apron G L t ≤1 ∧ ∀ (β), inBand (betaF G t L) β → N*(gStep β*fort G L N t (q t))≤1:=by
   have he:Rate G L 0 (fun t=>halberd G L j N t d (p t) (q t) (H t)):= (halberd_growth hp hq hf j N d).rate
   let V:= Access.apron G L; have ht:= (Rate.mul he Access.rates_apron).below (by norm_num) 1 zero_lt_one
   let f t:=fort G L N t (q t); have hF:Rate G L (-(1/2)+0) fun t=>N*(V t* |f t|):= (Access.rates_apron.mul (fortBudget hq N|>.absolute.rate)).mul_left _ -- |..| token
   filter_upwards [ht,hF.below (by norm_num) _ zero_lt_one,Access.wide hp.rate] with t hx hy hz
   refine ⟨(le_abs_self _).trans hx,fun β hβ=>?_⟩
   have hp:=hz.2 β hβ; exact (mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left (le_abs_self (f t)) hp.1.le).trans (mul_le_mul_of_nonneg_right hp.2.le (abs_nonneg _))) (Nat.cast_nonneg N)).trans ((le_abs_self _).trans hy)
end phaseBud
end YM.RemainderComparison.Herbal
