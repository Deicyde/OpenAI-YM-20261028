import YM.RemainderComparison.WickReps.Manor
import YM.RemainderComparison.WickReps.Median

/-! # Compactly aligned vacuum patch (representation costs AFTER alignment,
 treating each occurrence before masks exactly once). No coefficients assumed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.WickReps
open Function Filter Lattice RG Pressure Tree Wilson MeasureTheory ProbabilityTheory Finset
open Push Push.AbsoluteSums Animals Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Coat Blaze March Poll Brush Blaze.Frond
open PhysicalNext PhysicalNext.Repeat Song Push.Uniform Sienna Fare Lapis Boulevard Metric Lantern Slide Trio
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration
open YM.RemainderComparison.Aux Portal
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{n c C f L : Side} {Y:Stars→Side} {P:BudgetPoint}{r z k w m p:ℕ}{a b β v R e x:ℝ}

namespace Manor
variable {α:Type*}{ι J J' θ:Type} (T:Manor G c ι α J)(u:α)(s:Finset J)
lemma tidied {P:BudgetPoint} {i:J}{X:Support c} {root} (hp:T.Sees P root i)(hv:T.halls i⊆X): Trio.Tidy P X (T.wet P u i):=by
   by_cases h:T.total i
   · rw [show T.wet P u i= fun _=> T.solvent u i 1 from funext fun V=> (if_pos h).trans (hp.stall u h V)]; exact Trio.tidy_const ..
   rw [show T.wet P u i=masked P.threshold (T.halls i) (T.solvent u i) from funext fun _=> if_neg h]; exact Trio.tidy_mask _ (hp.angle u) hv

structure Basis (s: Finset J) (r:ℕ) where
   support : Site c→ J→ℝ
   sto x i : 0 ≤ support x i
   account i (hx:i∈s): ∑ x, support x i=1
   location x i (hx:i∈s) : support x i ≠ 0→ T.halls i ⊆ neighbors r x

variable (P : BudgetPoint) (B : T.Basis s r)
def sector (x:Site c)(V:Config G c):ℝ:= ∑ i∈s,B.support x i*T.solvent u i V
def porous (x:Site c)(V:Config G c):ℝ:= ∑ i∈s,B.support x i*T.wet P u i V
local notation "G₀" => T.sector u s B
local notation "M₀" => T.porous u s P B
lemma onSector (x: Site c) (U:Config G c)(hp: Healthy P.threshold (neighbors r x) U): M₀ x U= G₀ x U:=by
    refine sum_congr rfl fun i hi=>?_ ; by_cases hv:B.support x i=0
    · rw [hv,zero_mul,zero_mul]
    exact congr_arg (_ *·) (onView _ U (hp.mono_left (B.location x i hi hv)))
lemma unitStake (x i)(h:i∈s): B.support x i ≤ 1:=(B.account i h) ▸ Finset.single_le_sum (f:=fun x:Site c=> B.support x i) (fun j _=>B.sto j _) (mem_univ x)
variable {σ C₀:ℝ} {root:ι→Support c}(h:T.Templary (s:Set J) root P σ C₀)
include h
lemma networks (x: Site c)(he : r ≤ k): P.Regular (neighbors r x) (G₀ x) ∧ Tidy P (neighbors k x) (M₀ x):=by
   have hg i (hp:i∈s):T.Sees P root i:=(h.grants.choose_spec.2.1 i hp).1
   have hv i (hp:i∈s)(hy:B.support x i ≠0):T.halls i ⊆ neighbors r x:= B.location x i hp hy
   constructor
   · rw [show G₀ x= ∑ i∈s, B.support x i • T.solvent u i from funext fun V=> by unfold sector; simp]; apply Meadow.regularA s; intro i hi; by_cases h:B.support x i=0
     · rw [h,zero_smul]; exact CouplingShape.reg_const (0:ℝ)
     exact CouplingShape.reg_scale _ (CouplingShape.reg_extend ((hg i hi).angle u) (hv i hi h))
   refine Trio.tidy_sum _ _ _ _ fun i hi=>?_; by_cases h:B.support x i=0
   · rw [h]; simp_rw [zero_mul]; exact Trio.tidy_const ..
   exact Trio.tidy_scale _ _ (T.tidied u (hg i hi) ((hv i hi h).trans (Corona.halo_mono he Subset.rfl)))
lemma coupons (x:Site c)(V:Config G c)(hg:0≤ σ): ‖M₀ x V‖≤ ballCost r * C₀:=by
   obtain ⟨f,hf,hp,hB⟩:= h.grants; let q i j:= if T.port i=j then f i * Real.exp (σ*coverNumber P.B (T.halls i)) else 0
   have hQ i j:0 ≤ q i j:= (hB j).1 _; let X:= neighbors r x
   calc _ ≤ ∑ i∈s,∑ j∈X,q i j:= by
          unfold porous; refine (norm_sum_le ..).trans (sum_le_sum (fun i hi=>?_))
          by_cases he:B.support x i=0
          · rw [he,zero_mul,norm_zero]; exact sum_nonneg fun j _=>hQ _ _
          rw [norm_mul, Real.norm_of_nonneg (B.sto x i)]
          apply le_trans ((mul_le_of_le_one_left (norm_nonneg _) (T.unitStake s B x i hi)).trans (wet_le u V (hp i hi|>.1) ((hp i hi).2 u)))
          apply le_trans _ (single_le_sum (f:=fun j=>q i j) (fun _ _=>hQ _ _) (show T.port i∈X from B.location x i hi he (T.call i)))
          unfold q; rw [if_pos rfl]; exact le_mul_of_one_le_right (hf i) (Real.one_le_exp (mul_nonneg hg (by positivity)))
        _ ≤ (ballCost r:ℝ)*C₀:= by
          rw [sum_comm]; apply le_trans (sum_le_sum (fun j _=> budget_sum (hB j) s)); rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast (neighbors_card r x)) (budget_nonneg (hB x))
-- algebra generic mark-free vacuum investment. Offer compatible and AUX charts separately required before this layer
variable (Q:∀ i:Stars,(Y i).val=2*(w+i.val)) (fa:∀ i:Stars, Offer G (Y i))
local notation "O"=> Trio.ornament Q fa
def currencies (z :ℕ) (x : Site c) : Config G c→ℝ:=fun U=> M₀ x U-G₀ x 1- Trio.unearned P Q z (Trio.rip fa) x U
local notation "S₀" => T.currencies u s P B Q fa z
omit h
lemma garnered (z:ℕ) (U:Config G c): ∑ i∈s,T.wet P u i U= ∑ x:Site c,G₀ x 1 + ∑ x:Site c,masked P.threshold (neighbors z x) (Trio.ornament Q fa x) U + ∑ x:Site c,T.currencies u s P B Q fa z x U:=by
   unfold currencies Trio.ornament; rw [Trio.parade, ← sum_add_distrib, ← sum_add_distrib]; have he x:G₀ x 1 +Trio.unearned P Q z (Trio.rip fa) x U+(M₀ x U-G₀ x 1- Trio.unearned P Q z (Trio.rip fa) x U)=M₀ x U:=by ring
   simp_rw [he,porous]; rw [Finset.sum_comm]; apply sum_congr rfl; intro i hi; rw [← sum_mul,B.account i hi,one_mul]
variable (hσ:0 ≤ σ)(haze : Sensible P r (sector T u s B) fa)(hr:0<r)(hr' :2*r≤ w)(he:2*z≤k)(hc: 4*r+16≤c.val)(hw:w+4≤ z) (hp:∀ i j,P.Regular univ (fa i j)) (x:Site c)
def salary (Y:Stars→Side) (a r: ℝ)(p:Stars→ℝ):= a*r+a*r+∑ i:Stars,|ray i| * ((Fintype.card (Site (Y i)):ℝ)*(p i+p i)) -- Y hidden
include h hσ haze hr hr' he hc hw hp
lemma region (p:Stars→ℝ)(hv:∀ i x (V:Config G (Y i)),flags P.threshold V=∅→‖fa i x V‖ ≤ p i):
    Tidy P (neighbors k x) (S₀ x)∧∀ V,(‖S₀ x V‖ ≤ salary (Y:=Y) (ballCost r) C₀ p)∧ (Healthy P.threshold (neighbors k x) V → S₀ x V=0):= by
   have hg : r ≤ k:=by omega
   let s i:= Trio.unearned P Q z (Trio.rip fa) x i
   constructor
   · refine Trio.tidy_sub P (v:=s) (u:=M₀ x - fun _=> G₀ x 1) (Trio.tidy_sub P (T.networks u _ P B h x hg).2 (Trio.tidy_const ..)) (Trio.tidy_sum _ _ _ _ fun i _=> Trio.tidy_scale _ _ ?_)
     exact Trio.tidy_sum _ _ _ _ fun j _=> Trio.tidy_mask _ (Trio.unit_m P Q z fa hp hw _ i j) (Trio.patch Q z hw i j x he) -- inspect
   intro V; constructor
   · have h₁ : Healthy P.threshold (neighbors r x) (1:Config G c):=by unfold Healthy; rw [Boulevard.smoky (P:=P) (show (1:Config G c)∈ Boulevard.sunny P from (by intro i; simpa [Gauge.chord,faceValue,square,travel,Lattice.Step.read,posDir,negDir] using P.threshold_pos))]; simp
     have hw' := T.onSector u _ P B x 1 h₁
     exact (norm_sub_le ..).trans (add_le_add ((norm_sub_le ..).trans (add_le_add (T.coupons u _ P B h x V hσ) (hw' ▸ T.coupons u _ P B h x 1 hσ))) (Trio.stipends P V Q z fa p (fun i V hv' x=> hv i x V hv') hw x))
   intro hV; have hQ:= WickReps.gazing P Q z (Trio.rip fa) V x hw hr' he hc hV (fun i=> stillA (G₀ i)) (WickReps.stratus P fa (G₀) haze) hr; unfold currencies; rw [hQ,T.onSector u _ P B x V (hV.mono_left (Corona.halo_mono hg Subset.rfl))]; exact sub_self _
end Manor
end YM.RemainderComparison.WickReps
