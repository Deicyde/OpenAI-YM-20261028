import YM.RemainderComparison.Cadenza.Sheriff
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Cadenza
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson MeasureTheory ProbabilityTheory Finset
open Push Push.AbsoluteSums Animals Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Coat Blaze March Poll Brush Blaze.Frond
open PhysicalNext PhysicalNext.Repeat Song Push.Uniform Sienna Fare Lapis Boulevard Metric Lantern Slide
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration
open Height Input Org Supply Pane Push.PriceCompiler ThroughLaunch Bid Planned.JetPort
open YM.RemainderComparison.Aux Funk Herbal
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {P:Teller G} {Q:ConnectedActivityE6.Target G P} {p:Patch} {L : Side} {K:KernelChoices} {j n r : ℕ}
variable {q o w : ℝ→ℝ}{W μ:ℝ} {A:ConnectedActivityE6.Target.Order G W}
open Brim
open PhysicalNext JointLoad Heir
variable (Q:ConnectedActivityE6.Target G P) (A:ConnectedActivityE6.Target.Order G W)
variable {P' B:BudgetPoint} (p:Patch)(r:Rays)(s:Songbook G p.L)
variable {M: RG.Stage}{x η:ℝ}
/-! # Actual step allowances before other transport costs

The K reclosure uses a genuine retained seed existential, not charging
 `s` by truncated EXP path tails. Covers alpha callbacks at all C actual
 supports. Money functions post-L. Probe derivatives conditional on AP
 instruction, not monetary condition varying with fields beyond SCAPE prices. -/
variable (t : Scrollwork G p.L) (E' : RG.Stage)(D : Quarry)
local notation "G'"=>Funk.Platform
local notation "Ψ"=>D.layer p s t E' r
local notation "Y'" => D.gold
local notation "Γ"=>r.rank
namespace Expenditure
open WickReps Trio
local notation "W'" => E'.order
local notation "P'" => E'.power
local notation "Z'" => t.z
local notation "U'" => t.halo
local notation "K'" => t.k
local notation "J" => s.post D.d D.Z D.R D.charge

def cooker (x:ℝ):= Apo.skyFare E'.order r.p r.title (D.R x) (D.cost x) (D.view x) (s.post D.d D.Z D.R D.charge x) (t.siteBill x)

def ledger (k m z:ℕ):= 2^k*((1+(z:ℝ))^(m*k))
def seat (x:ℝ):= ((∑ i:Stars, |Slide.ray i|) * (ledger E'.order E'.power (t.z x)*(2*cooker p r s t E' D x)))*Real.exp (r.σ*((t.ℓ+t.ℓ+1)^4:ℕ))
def rise (p g k z:ℕ):ℝ:= ((1+((k+z:ℕ):ℝ))^g)^p

def airs (x:ℝ):= Manor.tribute t.ℓ (t.k x) (r.σ+1) (Breeze.areaBudget (t.halo x) r.k (s.kernel x))
def bandPay (x:ℝ):= (rise E'.order E'.power (t.k x) (t.z x)*(ledger E'.order E'.power (t.z x)*cooker p r s t E' D x))*airs p r s t x

lemma shares {Y:BudgetPoint}(hp:Temper Y E' x G p.L)(β:ℝ) : Funk.paymentA (t.z x) t.ℓ r.σ (Funk.wages' (D.layer p s t E' r x) (D.gold x) Y β x) Y=(gStep β)^(r.p+1)*seat p r s t E' D x ∧
   WickReps.burse Y (t.k x) (t.z x) (Funk.wages' (D.layer p s t E' r x) (D.gold x) Y β x)* Manor.tribute t.ℓ (t.k x) (r.σ+1) (Breeze.areaBudget (t.halo x) r.k (s.kernel x)) = gStep β^(r.p+1)*bandPay p r s t E' D x:=by
   have hx:Funk.wages' (D.layer p s t E' r x) (D.gold x) Y β x=(gStep β)^(r.p+1)*cooker p r s t E' D x:=by unfold Funk.wages' Funk.crown; rw [hp.order]; rfl
   rw [hx]; constructor
   · unfold seat ledger Funk.paymentA WickReps.warmth Trio.oroW Trio.tilt -- order
     rw [← Finset.sum_mul,hp.order,hp.power]; ring
   unfold bandPay rise airs WickReps.burse Trio.tilt ledger; rw [hp.order,hp.power]; ring

lemma tribute (m : ℕ)(a :ℝ){v:ℝ→ℕ}{f:ℝ→ℝ}(h:Reserve G L fun x=> (v x:ℝ))(hf:Reserve G L f) : Reserve G L (fun x=>Manor.tribute m (v x) a (f x)):= (Reserve.const _).mul ((Reserve.ball _ h).mul hf)

local notation "Ce" => cooker p r s t E' D
variable {qZ:ℝ}(hD:D.Financed G p.L qZ)(hz:0<D.Z)(hd:0<D.d)
include hD hz hd
lemma cooking : Reserve G p.L (cooker p r s t E' D):=
   (Portal.posture_charge r.title r.p E'.order hD.afford hD.peso hD.beams (s.etudes D.d D.Z D.R D.charge hD.afford hD.fees hz hd).2).add (t.sites_paid.mul (Reserve.const _))
lemma seating : Reserve G p.L (seat p r s t E' D):=by
   have h:=cooking p r s t E' D hD hz hd
   have hi:Reserve G p.L fun x=> ledger E'.order E'.power (t.z x):= (Reserve.const _).mul (((Reserve.const _).add t.capped).pow _)
   exact ((Reserve.const _).mul (hi.mul ((Reserve.const 2).mul h))).mul (Reserve.const _)
lemma aria : Reserve G p.L (bandPay p r s t E' D):=by
   have ha : Reserve G p.L fun x=> rise E'.order E'.power (t.k x) (t.z x):=by unfold rise; push_cast; exact ((((Reserve.const _).add (t.keeled.add t.capped)).pow _).pow _)
   have ht: Reserve G p.L fun x=> ledger E'.order E'.power (t.z x):=(Reserve.const _).mul (((Reserve.const _).add t.capped).pow _)
   have he : Reserve G p.L fun x=> Breeze.areaBudget (t.halo x) r.k (s.kernel x):= ((((Reserve.ball _ t.board).mul s.sea|>.add (Reserve.const _)).pow _).mul (Reserve.const _))
   exact (ha.mul (ht.mul (cooking p r s t E' D hD hz hd))).mul (tribute _ _ t.keeled he)
omit hD hz hd

-- Exact unmarked leak.C. No sign assumption until paid using h.Composer
variable (A A' : ℝ →ℝ)
def signed (x:ℝ) :=
   let v:ℝ:= (ballCost (t.halo x):ℝ)*(A x+A' x)
   Real.exp ((r.σ+1)*((t.ℓ+t.ℓ+1)^4:ℕ))* ((ballCost (t.k x):ℕ)*(v+v+∑ i:Stars,|Slide.ray i| * ((((2*(t.n x+i.val):ℕ)^4:ℕ):ℝ)*(v+v)))) -- a unused
lemma remits (x :ℝ){Y:Stars→Side}(hx:∀ i:Stars,(Y i).val=2*(t.n x+i.val)): Funk.paymentB (t.halo x) (t.k x) t.ℓ Y (A x+A' x) (A x) (A' x) (r.σ+1) = signed p r t A A' x:=by
   unfold Funk.paymentB Manor.salary signed; simp_rw [site_card, hx]

private lemma added (P:Finset Stars)(f:Stars→ℝ→ℝ) (h:∀ i,Rate G L qZ (f i)): Rate G L qZ (fun x=>∑ i∈P, f i x):=by
   induction P using Finset.induction with
   | empty=> simp only [sum_empty]; apply ((h (0:Stars)).compare _); filter_upwards with x; rw [abs_zero]; exact abs_nonneg _
   | insert i a hi ih=> simp only [sum_insert hi]; exact (h _).add ih
lemma salary' (q:ℝ)(hA:Rate G p.L q A) (hB:Rate G p.L q A') : Rate G p.L q (Expenditure.signed p r t A A'):=by
   have hv := (Reserve.ball _ t.board).rate.mul (hA.add hB); rw [zero_add] at hv
   have h (i: Stars): Rate G p.L 0 (fun x=> (((2*(t.n x+i.val):ℕ)^4:ℕ):ℝ)) := by
       push_cast; exact Reserve.rate (((Reserve.const _).mul (t.crimped.add (Reserve.const _))).pow _)
   have he:= added univ _ (fun i=> ((h i).mul (hv.add hv)).mul_left |Slide.ray i|); rw [zero_add] at he
   simpa only [Expenditure.signed,zero_add] using! (((Reserve.ball _ t.keeled).rate.mul ((hv.add hv).add he)).mul_left (Real.exp ((r.σ+1)*((t.ℓ+t.ℓ+1)^4:ℕ))))
end Expenditure
end YM.RemainderComparison.Cadenza
