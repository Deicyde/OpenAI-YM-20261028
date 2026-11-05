import YM.Extension.UV.BoundedRows
import YM.Extension.UV.Canon.Nearby

/-!
A Banach holomorphic packet for the *actual canonical* fine boundary. All coordinates of forced
letters (including supports & flags, read on real configurations) share a uniform envelope with
the exponential anchored masses paid, and the regular part keeps its full frozen affine-jet
profile. Shift of the boundary coupling is genuinely to the same formula.
This covers the inward initial operand for analytic tuning, not a complete construction of its
coarse return maps or the physical tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extension.UV.Startup
open Set Filter Function Lattice Wilson RG RG.Supply Precision Input Tree Ovens Ovens.Pipes
open WilsonStartup Progress.DirectedRecipe Progress.DirectedRecipe.Rack UniformHol
open scoped Topology BigOperators
variable {G:Gauge} {a:Levels G}{H:Horizon a} {O:ChartRatio G} (k:Kin H O) (N p:ℕ)

abbrev half (a:Levels G) N:= a.clock.hatBeta N/2
def inside (a : Levels G) (N:ℕ) : Set ℂ:= {z:ℂ | half a N < z.re ∧ ‖z‖ < 2*a.clock.hatBeta N}
lemma inside_open : IsOpen (inside a N):= (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt continuous_norm continuous_const)
lemma inside_ofPad {x:ℝ} (he:x∈strictBand a N) : Metric.ball (x:ℂ) (a.clock.hatBeta N/8) ⊆ inside a N := by
 intro z hz
 have h := Metric.mem_ball.mp hz
 rw [dist_eq_norm] at h
 have hh := Complex.abs_re_le_norm (z-x)
 simp only [Complex.sub_re,Complex.ofReal_re] at hh
 unfold inside
 refine ⟨by unfold half; linarith [he.1,(abs_lt.mp (hh.trans_lt h)).1],?_⟩
 have hx := a.fits.delayed N
 have he' : ‖(x:ℂ)‖=x:= by norm_cast; exact Real.norm_of_nonneg (by linarith only [hx,he.1])
 linarith [norm_sub_norm_le z (x:ℂ),he.2]

structure Envelope where
   g : ℕ→ℝ
   bound i : (0≤g i)∧∀ U, |(canonical k N p (half a N)).activities.K i U| ≤ g i
   costs (x:Site (a.S.side N p)): SumBudget (fun i=>if x∈((canonical k N p (half a N)).activities.forced i).support then BudgetPoint.mass (a.budget N) ((canonical k N p (half a N)).activities.forced i).support (g i) else 0) (a.clock.forcedAllowance N)
lemma envelope_exists (ht : Planned.Port.AtTop k) (hk : Start.Allows a N) : Nonempty (Envelope k N p):= by
  obtain ⟨g,h,h'⟩:= (genuine_valid k N p ht hk _ (pays_min N)).boundK
  exact ⟨⟨g,h,h'⟩⟩

abbrev Key := ℕ×Config G (a.S.side N p)
local notation "Row" => Rows (Key (a:=a) N p)
abbrev TopSpace:= ℂ×Row
variable {k N p} (e:Envelope k N p)
def force (z:ℂ) (q:Key (a:=a) N p): ℂ:= embodiedK a N p z q.1 q.2 / (8*e.g q.1)
def datum (z:ℂ):TopSpace (a:=a) N p:= (z/(8*a.clock.hatBeta N), UniformHol.pack (force e z))
def regular (ζ: TopSpace (a:=a) N p) : ℕ → Config G (a.S.side N p)→ℂ:= fun i U=> (8*a.clock.hatBeta N) * ζ.1 * ((widen (Planned.Port.pot a N p) (Planned.Port.kettle a N p 1)).regular i U)
def hard (ζ: TopSpace (a:=a) N p) : ℕ → Config G (a.S.side N p)→ℂ := fun i U=> (8*e.g i) * ζ.2 ⟨i,U⟩

variable (he:Start.Allows a N)
include he
lemma force_bound {z : ℂ} (hz : z∈inside a N) q : ‖force e z q‖ ≤ 1/8:= by
 rcases eq_or_lt_of_le (e.bound q.1).1 with hv|hw
 · simp [force,hv.symm]
 have hm := (K_norm_compare k N p _ z q.1 q.2 he.clip (le_of_lt hz.1)).trans ((e.bound q.1).2 q.2)
 unfold force
 rw [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hw]
 rw [show ‖(8:ℂ)‖=8 from by norm_num,div_le_iff₀ (by positivity)]
 nlinarith
lemma force_eq {z:ℂ} (hz:z∈inside a N) i U : hard e (datum e z) i U=embodiedK a N p z i U:=by
 change 8*_*(UniformHol.pack (force e z) ⟨(i,U)⟩)=_
 rw [UniformHol.equals ⟨1/8,force_bound e he hz⟩]
 rcases eq_or_lt_of_le (e.bound i).1 with hv|hw
 · have h:= ((K_norm_compare k N p _ z i U he.clip (le_of_lt hz.1)).trans (e.bound i|>.2 U)).trans_eq hv.symm
   simp [hv.symm,norm_le_zero_iff.mp h]
 dsimp only [force]
 have hu: ((e.g i):ℂ) ≠0:= by exact_mod_cast hw.ne'
 field_simp
lemma datum_bound {z:ℂ} (hz:z∈inside a N) : ‖datum e z‖ ≤ 1/4:=by
 apply max_le
 · dsimp only [datum]; have hx := a.fits.delayed N
   rw [norm_div,norm_mul,show ‖(8:ℂ)‖=8 by norm_num,Complex.norm_real, Real.norm_of_nonneg (by linarith)]
   rw [div_le_iff₀ (by positivity)]; linarith [hz.2]
 apply (BoundedContinuousFunction.norm_le (by norm_num)).2; rintro ⟨q⟩
 dsimp [datum]; rw [UniformHol.equals ⟨1/8,force_bound e he hz⟩]; exact (force_bound e he hz q).trans (by norm_num)
lemma datum_analytic : DifferentiableOn ℂ (datum e) (inside a N) := by
 have hv : DifferentiableOn ℂ (fun z:ℂ=>z/(8*(a.clock.hatBeta N:ℂ))) (inside a N):= Differentiable.differentiableOn (differentiable_id.div_const _)
 exact hv.prodMk (UniformHol.liftOn (inside_open N) (fun q=> ((K_entire_piece _ _ q.1 q.2).div_const _).differentiableOn) (fun x hx=> ⟨_,(inside_open N).mem_nhds hx,1/8,fun z hz=> force_bound e he hz⟩))
omit he in
lemma regular_eq (z:ℂ) : regular (datum e z)=embodiedE a N p z:=by
 funext i U; have hx := a.fits.delayed N
 have hn : ((a.clock.hatBeta N:ℂ))≠0:= (by exact_mod_cast (by linarith : a.clock.hatBeta N ≠ 0))
 unfold regular datum embodiedE
 dsimp only
 field_simp

-- Observe explicitly that a common envelope rather than separate point suprema is charged to
-- the dyadic startup costs.
omit he in
lemma arbitrary_hard {w : ℝ} (hw : 0≤w) {ζ:TopSpace (a:=a) N p} (hz:‖ζ‖≤w):
     (∀ i U, ‖hard e ζ i U‖≤ w*8*e.g i) ∧ ∀ x:Site (a.S.side N p), SumBudget (fun i=>if x∈((canonical k N p (half a N)).activities.forced i).support then BudgetPoint.mass (a.budget N) ((canonical k N p (half a N)).activities.forced i).support (w*8*e.g i) else 0) (w*8*a.clock.forcedAllowance N):= by
   refine ⟨fun i U=>?_,fun x=>?_⟩
   · rw [hard,norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (e.bound _|>.1)]
     calc
        _ ≤ (8*(e.g i))*w:= mul_le_mul ((show ‖(8:ℂ)‖=8 from by norm_num) ▸ le_rfl) (((BoundedContinuousFunction.norm_coe_le_norm ..).trans ((le_max_right ..).trans hz))) (norm_nonneg _) (by linarith [e.bound i|>.1])
        _ = _ := by ring
   let f i:= if x∈((canonical k N p (half a N)).activities.forced i).support then BudgetPoint.mass (a.budget N) ((canonical k N p (half a N)).activities.forced i).support (e.g i) else 0
   have hx i : (if x∈((canonical k N p (half a N)).activities.forced i).support then BudgetPoint.mass (a.budget N) ((canonical k N p (half a N)).activities.forced i).support (w*8*e.g i) else 0) = (w*8)*f i:= by
      dsimp [f,BudgetPoint.mass]; split_ifs <;> ring
   simp_rw [hx]; have hg:= e.costs x
   refine ⟨fun i=>by have h:=hg.1 i; exact mul_nonneg (by positivity) h,hg.2.1.mul_left _,?_⟩
   rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hg.2.2 (by positivity)
lemma datum_lipschitz {x y:ℝ} (hx:x∈strictBand a N) (hy:y∈strictBand a N) : ‖datum e (x:ℂ)-datum e (y:ℂ)‖ ≤ |x-y|/(a.clock.hatBeta N/2):= by
    have ph:= a.fits.delayed N
    have db (x:ℂ) (hx:x∈Complex.ofReal '' strictBand a N) : Metric.ball x (a.clock.hatBeta N/8) ⊆ inside a N:= by obtain ⟨x,hx,rfl⟩:= hx; exact inside_ofPad N hx
    have h:= diam_lipschitz (f:=datum e) (U:=Complex.ofReal '' strictBand a N) ((convex_Icc ..).linear_image Complex.ofRealCLM.toLinearMap) (fun z hz=> (datum_analytic e he).differentiableAt ((inside_open N).mem_nhds (by obtain ⟨x,hx,rfl⟩:=hz; exact inside_ofPad N hx (Metric.mem_ball_self (by linarith))))) (fun z hz=> (datum_analytic e he).mono (db z hz)) (fun z hz u hu=> datum_bound e he (db z hz hu)) (by linarith) _ (mem_image_of_mem _ hx) _ (mem_image_of_mem _ hy)
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at h
    apply h.trans_eq; ring
end YM.Extension.UV.Startup
