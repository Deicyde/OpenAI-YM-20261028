import YM.RemainderComparison.Herbal.Golf
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

variable {U V : ℝ × Positions (Uniform.Primary c G) → Poll.Body (Precision.Key F G)→ ℝ} {H H' : Config G f → ℝ}
lemma raise (hp:Playing F ρ β U H x D' e' u A' A W n m) (ha:A≤C)(hp':W≤c')(hh:m≤r) : Playing F ρ β U H x D' e' u A' C c' n r:=
     ⟨hp.tagGerm.raise le_rfl le_rfl le_rfl ha hh,{ hp.group with rich:= fun i=> (hp.group.rich i).trans hp'}, hp.speak⟩
lemma still (l:ℝ) : Playing F ρ β (fun _ _=>l) (fun _=>l) x D' e' u A' ‖l‖ ‖l‖ j 0:= ⟨Cloud.still .., Actual.unit _,fun _ _ _ _=>rfl⟩
lemma unite (hp:Playing F ρ β U H x D' e' u A' A W n m)(hq:Playing F ρ β V H' x D' e' u A' C c' n m) : Playing F ρ β (fun x z=>U x z+V x z) (fun i=>H i+H' i) x D' e' u A' (A+C) (W+c') n m:=
    ⟨hp.tagGerm.gather hq.tagGerm,⟨hp.group.bore.add hq.group.bore,fun i j=> congr_arg₂ (· + ·) (hp.group.gauge i j) (hq.group.gauge i j), fun i=> (norm_add_le ..).trans (add_le_add (hp.group.rich i) (hq.group.rich i))⟩,fun _ hi j hj=>congr_arg₂ (·+·) (hp.speak _ hi j hj) (hq.speak _ hi j hj)⟩
lemma join (hp:Playing F ρ β U H x D' e' u A' A W n m)(hq:Playing F ρ β V H' x D' e' u A' C c' n k) : Playing F ρ β (fun x z=>U x z*V x z) (fun i=>H i*H' i) x D' e' u A' (A*C*3^n) (W*c') n (m+k):=by
   refine ⟨hp.tagGerm.mix hq.tagGerm,⟨hp.group.bore.mul hq.group.bore,fun i j=> congr_arg₂ (· * ·) (hp.group.gauge i j) (hq.group.gauge i j), fun i=>?_⟩,fun _ hi j hj=>congr_arg₂ (· * ·) (hp.speak _ hi _ hj) (hq.speak _ hi _ hj)⟩
   rw [norm_mul]; exact mul_le_mul (hp.group.rich _) (hq.group.rich _) (norm_nonneg _) hp.group.price
lemma concert {U:ι→ℝ × Positions (Uniform.Primary c G)→ Poll.Body (Precision.Key F G)→ ℝ}{H:ι→ Config G f→ℝ}(s:Finset ι) (f' p:ι→ℝ)(he:∀ i∈s,Playing F ρ β (U i) (H i) x D' e' u A' (f' i) (p i) n m) :
   Playing F ρ β (fun x z=>∑ i∈s,U i x z) (fun i=>∑ j∈s,H j i) x D' e' u A' (∑ i∈s,f' i) (∑ i∈s,p i) n m := by
   induction s using Finset.induction_on with
   | empty=> simp only [Finset.sum_empty]; exact raise ρ β (still ρ β 0) (norm_zero.le) (norm_zero.le) (by omega)
   | insert i s hi ih=> simp_rw [Finset.sum_insert hi]; exact unite ρ β (he i (mem_insert_self ..)) (ih fun i hi=> he _ (mem_insert_of_mem hi))
lemma gathering {U:ι→ℝ × Positions (Uniform.Primary c G)→ Poll.Body (Precision.Key F G)→ ℝ}{H:ι→ Config G f→ℝ}(s:Finset ι) (f' p:ι→ℝ)(z:ι→ℕ)(he:∀ i∈s,Playing F ρ β (U i) (H i) x D' e' u A' (f' i) (p i) n (z i)) :
   Playing F ρ β (fun x z=>∏ i∈s,U i x z) (fun i=>∏ j∈s,H j i) x D' e' u A' (∏ i∈s, (f' i* 3^n)) (∏ i∈s,p i) n (∑ i∈s,z i) := by
   induction s using Finset.induction_on with
   | empty=> simp only [Finset.prod_empty,Finset.sum_empty]; simpa only [norm_one] using! still (F:=F) ρ (x:=x) (L:=L) (t:=t) (d:=d) (u:=u) (j:=n) β 1 --args
   | insert i s hi ih=> simp_rw [Finset.prod_insert hi,Finset.sum_insert hi]; rw [mul_right_comm (f' i)]; exact join ρ β (he i (mem_insert_self ..)) (ih fun i hi=> he _ (mem_insert_of_mem hi))

lemma warm_ratio (hb:inBand (betaF G t L) β)(hp:0<betaF G t L): (gStep β)⁻¹ * Pressure.fiery G t L ≤ 2* Delay.fineMonitor G L t:= by
  let z:=betaF G t L; let y:=gStep z; let Y':=Delay.fineMonitor G L t
  have hz:0<y:= (Fare.gS z hp).1
  have hv:0<Y':=Delay.monitor_pos G L t
  have ht := inv_anti₀ (half_pos hz) (band_gap z β hp hb).1
  calc _ ≤ (y/2)⁻¹ * (y*Y'):=mul_le_mul_of_nonneg_right ht (mul_pos hz hv).le
       _ = _:=by field_simp; rfl

structure Eden (c:Side)(G:Gauge)(α: Type) where
  ground : Finset α
  grade : α→ℕ
  order : α→ℕ
  oil : α → Config G c→ℝ
namespace Eden
variable (P:Eden f G α)
structure Culture (N:ℕ)(j:ℕ)(b Z:ℝ)(a r:ℝ) : Prop where
   occupancy : P.ground.card≤ N -- no cost fixed number of grades
   enroll (i) : i∈P.ground → P.grade i ≤ N ∧ P.order i ≤ N ∧ Sect (P.oil i) b (P.order i) j Z a
   wage : 0≤a
   base : ∀ i∈P.ground,r≤ P.grade i

def groups (U:Config G f):= ∑ i∈P.ground, worn (P.oil i) (gStep β) (P.order i) (P.grade i) U
def cloaked (U:Config G f):= ∑ i∈P.ground,masked B.threshold Finset.univ (worn (P.oil i) (gStep β) (P.order i) (P.grade i)) U
def proofE (y:ℝ×Xs)(z:Y):= ∑ i∈P.ground,matte F ρ (P.oil i) (P.grade i) (P.order i) y z
lemma part (V:Config G f)(hv:flags B.threshold V=∅): cloaked B β P V= groups β P V:=Finset.sum_congr rfl (fun i _=> masked_eq _ _ _ _ (by simp [Healthy,hv]))
end Eden
section singer
variable (P:Eden f G α)
def skys (j N:ℕ) (D u A C:ℝ):= ∑ i∈ Finset.range (N+1), ∑ m∈Finset.range (N+1), |skyFees j (j+i) m D u A C|
lemma skyFeeBudget {p q f H:ℝ→ℝ} (hp:Reserve G L p)(hq:Reserve G L q)(hf:Reserve G L f)(h:Reserve G L H)(j N:ℕ) : Reserve G L fun t=>skys j N (p t) (q t) (f t) (H t):=
    Reserve.sum _ _ fun _ _=> Reserve.sum _ _ fun _ _=> (reserve_sky hp hq hf h ..).absolute
lemma earnUp {i k m :ℕ} {u v w b:ℝ} (j:ℕ)(hz:i≤ m)(hy:k≤ m): skyFees j (j+i) k u v w b ≤ skys j m u v w b:= by
   let U i k:= |skyFees j (j+i) k u v w b|
   apply (le_abs_self _).trans
   refine le_trans (Finset.single_le_sum (fun k _=> show 0≤U i k from abs_nonneg _) (Finset.mem_range.mpr (show k< m+1 by omega))) (Finset.single_le_sum (f:=fun i=> ∑ k∈Finset.range (m+1), U i k) ?_ (Finset.mem_range.mpr (show i< m+1 by omega))) -- remove A
   exact fun _ _=> Finset.sum_nonneg fun _ _=> abs_nonneg _

def fort (G:Gauge)(L:Side)(n:ℕ)(t A:ℝ):= A*(1+2* Delay.fineMonitor G L t)^n
theorem fortBudget {p:ℝ→ℝ}(hp:Reserve G L p) (n:ℕ): Reserve G L fun t=>fort G L n t (p t):=
   hp.mul (((Reserve.const _).add ((Reserve.const _).mul Reserve.monitoring)).pow _)

variable (hO:Eden.Culture P N k B.threshold (fineCost G k Z) A (r:ℕ)) (hZ:PaintSupply G k Z)
variable (hw:Weather T F Θ k' ρ B β d t a W u C K O k x L) (hc:Climate G L t d u C β)(hy:j+N≤k)
include hO hw hc hy hZ
lemma eden : Playing F ρ β (P.proofE ρ) (P.cloaked B β) x D' e' u A' (N*skys j N D' u A C) (N*(g^r*fort G L N t A)) j (j+N) := by
   let f':=fort G L N t A; let J:= g^r*f'; let s' := skys j N D' u A C
   have h i (hi:i∈P.ground): Playing F ρ β (matte F ρ (P.oil i) (P.grade i) (P.order i)) (masked B.threshold Finset.univ (worn (P.oil i) g (P.order i) (P.grade i))) x D' e' u A' s' J j (j+N):=by
      obtain ⟨ha,hb,hp⟩:= hO.enroll i hi
      refine raise ρ β (coverage T F Θ k' ρ B (P.oil i) hw hc hZ hp (show j+P.order i≤ k by omega) _) (earnUp j hb ha) ?_ (by omega)
      have ht:= mul_nonneg (pow_nonneg hc.g_pos.le r) hO.wage; have hh:0< betaF G t L:=hw.patch ▸ (by have hx:=hw.feed.height; exact lt_of_lt_of_le (by norm_num : 0<(1:ℝ)) hx.le) -- inspect .height
      have hβ:= Aux.lane T B hw.feed hw.patch; have he:0≤ (2:ℝ)*Delay.fineMonitor G L t:= mul_nonneg (by norm_num) (Delay.monitor_pos ..).le
      have hpP : (gStep β)⁻¹ * B.threshold ≤ (2:ℝ)*Delay.fineMonitor G L t:= by
        rw [show B.threshold=_ from hw.feed.received.temp,hw.patch]; exact warm_ratio β hβ hh
      refine (mul_le_mul (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hc.g_pos.le (hw.paint.distance.le.trans hw.paint.core.small) (show r ≤ P.grade i from (by exact_mod_cast hO.base i hi))) hO.wage) ((pow_le_pow_left₀ (mul_nonneg (inv_pos.mpr hc.g_pos).le B.threshold_pos.le) (hpP.trans (le_add_of_nonneg_left zero_le_one)) _).trans (pow_le_pow_right₀ (le_add_of_nonneg_right he) hb)) (pow_nonneg (mul_nonneg (inv_pos.mpr hc.g_pos).le B.threshold_pos.le) _) ht).trans_eq ?_
      unfold J f' fort; rw [mul_assoc]
   have hh := concert ρ β P.ground (fun _=>s') (fun _=>J) h
   have he:P.ground.card ≤ N:= hO.occupancy
   apply raise ρ β hh _ _ le_rfl
   · simp only [Finset.sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast he) (by unfold s' skys; positivity)
   simp only [Finset.sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast he) (by unfold J f' fort; have h:=Delay.monitor_pos G L t; have hp:=hO.wage; have ht:=hc.g_pos; positivity)
end singer
end YM.RemainderComparison.Herbal
