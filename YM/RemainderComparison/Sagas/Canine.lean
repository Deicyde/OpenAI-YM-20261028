import YM.RemainderComparison.Sagas.Book
/-! True lengths leak.Paid.Electron. At either input or output actual.Support mass BEFORE uploading Halo portfolios.F;
 Require height metadata.Annotation.Progress.D._. Can be supplied uniformly for
   all orders simultaneously from the canonical path bounds. This class can be applied
 also to projection deviations represented as eNat after changing masks/support with covariance proof./
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Sagas
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson MeasureTheory ProbabilityTheory Finset
open Push Push.AbsoluteSums Animals Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Coat Blaze March Poll Brush Blaze.Frond
open PhysicalNext PhysicalNext.Repeat Song Push.Uniform Sienna Fare Lapis Boulevard Metric Lantern Slide
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration
open Height Input Org Supply Pane Push.PriceCompiler ThroughLaunch Bid Planned.JetPort
open YM.RemainderComparison.Aux Portal Herbal
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{c f L:Side}{α:Type*}
variable (p:BudgetPoint)(β:ℝ)
namespace Packet
variable (Q:Packet G c α)
local notation "dπ"=> Wages.grade Q.rank p.power p.order
variable (x:Site c)(a:α)
-- Quoted Heal needed for chart only on Lumi
variable {ξ:ℝ}
lemma income (hx:0<ξ) : Q.rent p ≤ turnFee p*Wages.startup G Q.rank p.power p.order * momentPrice (Q.lengthW p) ξ * Real.exp (ξ*Q.length):=by
   unfold Packet.rent; rw [mul_assoc (turnFee p *_ ) (momentPrice ..)]; exact mul_le_mul_of_nonneg_left (spendMoment _ hx (Nat.cast_nonneg _)) (Packet.fare_aux Q p) -- named

-- stage.Caps BEFORE L and Ω.P boasts.R θ.S exponential in p power/order allowed here.Supported.
variable (G)
open Time
-- no variation at count.Jark Anti.If suppression under rank.A.Ac.Use g≤1. Env Mark.Oil α x.
def bonds (F:RG.Stage) (ε : ℝ) (i:ℕ):= turnFee (Time.probe F)*Wages.startup G i F.power F.order * momentPrice (Wages.grade i F.power F.order) ε
def tariff (F:RG.Stage)(ε :ℝ)(k:ℕ):= ∑ i∈ range (k+1),|bonds G F ε i|
lemma tolls (F:RG.Stage)(ε:ℝ)(k:ℕ): 0≤tariff G F ε k:= sum_nonneg (fun _ _=> abs_nonneg _)
variable {αP d t b η:ℝ}{n k:ℕ}
variable (F:RG.Stage)(h:Same F p)(hb:0<β)(hX: gStep β≤1)(he:0<ξ)(hs: Q.rank≤k)(hg:n ≤ Q.grade)
variable (hδ:0≤ b) (hN:(coverNumber p.B Q.postage.support:ℝ) ≤ αP+d*(Q.length:ℝ)) -- `d t radius` positive.R.Art.SE B included. verified.Memory
local notation "ℒ" => Real.exp (t*Q.length) * Real.exp (b* coverNumber p.B Q.postage.support)
local notation "χ" => Real.exp (b*αP)

def music (F:RG.Stage)(e t α:ℝ)(n k:ℕ) (β τ:ℝ) := gStep β^n * (1+ (τ/gStep β))^k * tariff G F e k * Real.exp (t*α)
local notation "W₀"=> Packet.music G F ξ b αP n k β p.threshold
include h hb he hδ hs hN hX hg
lemma glow (hd : t + b*d + ξ ≤ η): Q.eats β p* (ℒ) ≤ W₀*(Q.weight*Real.exp (η*Q.length)):=by
    let u:ℝ:= Q.length; let C:=gStep β; let T:= tariff G F ξ k; let v':= p.threshold/C; let w:=Q.weight
    have ha : p.threshold>0:=p.threshold_pos; have hz:0<C:= (Fare.gS β hb).1
    have hu:0≤u:=Nat.cast_nonneg _; have hC :0≤ v':= div_nonneg ha.le hz.le
    have he': turnFee p*Wages.startup G Q.rank p.power p.order * momentPrice (Q.lengthW p) ξ ≤ T :=by
       refine le_trans ?_ ((le_abs_self (bonds G F ξ _)).trans (Finset.single_le_sum (f:=fun i=> |bonds G F ξ i|) (fun i _=>abs_nonneg _) (mem_range.mpr (show Q.rank<k+1 by omega))))
       unfold bonds Packet.lengthW turnFee; rw [h.1,h.2.1]; exact le_rfl
    have hR : Q.rent p ≤ T * Real.exp (ξ*u):= (income p Q he).trans (mul_le_mul_of_nonneg_right he' (Real.exp_pos _).le)
    have hp : v'^Q.rank ≤ (1+v')^k:= (pow_le_pow_left₀ hC (le_add_of_nonneg_left zero_le_one) Q.rank).trans (pow_le_pow_right₀ (by linarith) hs)
    have hℓ : ℒ ≤ χ* Real.exp ((η-ξ)*u) := by rw [← Real.exp_add,← Real.exp_add]; exact Real.exp_monotone (by change t*u+_≤_; nlinarith only [mul_le_mul_of_nonneg_left hN hδ,mul_le_mul_of_nonneg_right hd hu])
    have hE : 0 ≤rent Q p:=mul_nonneg (Packet.fare_aux Q p) (pow_nonneg (by positivity) _)
    have hh : 0≤T:=tolls ..; have hw:0≤w:= Q.suspension
    change C^Q.grade * (v'^Q.rank)* Q.rent p*w*(ℒ) ≤ _
    calc
       _ ≤ C^n * ((1+v')^k)*(T*Real.exp (ξ*u))*w*(χ*Real.exp ((η-ξ)*u)) := mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul (pow_le_pow_of_le_one hz.le hX hg) hp (pow_nonneg hC _) (pow_nonneg hz.le _)) hR hE (mul_nonneg (pow_nonneg hz.le _) (pow_nonneg (by linarith) _))) hw) hℓ (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) (by positivity) -- precedence
       _ = _ :=by unfold music; rw [show η*(Q.length:ℝ)=ξ*u+(η-ξ)*u from by unfold u; ring,Real.exp_add]; change _= C^n*(1+v')^k*T*χ*(w*_); ring
end Packet
end YM.RemainderComparison.Sagas
