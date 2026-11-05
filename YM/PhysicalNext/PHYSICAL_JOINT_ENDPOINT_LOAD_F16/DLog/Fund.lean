import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Corners
import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Parcel
import YM.PhysicalNext.PHYSICAL_JOINT_ENDPOINT_LOAD_F16.DLog.Color
import YM.SectorNext.VACUUM_NORMALIZATION.Bulk

/-!
# Post-L stock for the determinant labels

At committed orders & cover size & layout variant. Width is log chart
for *this particular* function, NOT entering replacing profiles or the
Rally for a whole promoted term. `small_span` and `thickness` before V.
Buy combined hK stage with this in client. Halo l a numerical number in
units of B (use e.g. ≥20 for dependencies, see Actual registration). `a`
a required exponent on complete B-cover, not a distance- or tree tax.
Doesn't sum a second set of labels for any tag changes, nor buy other
connected support growth costs.
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.EndpointLoadF16.DetLong
open Filter Function Set Lattice RG Wilson Pressure Tree Matrix
open Next.SectorChange
open FreeResolvent FreeResolvent.TestD FreeResolvent.Affine SelectedOrderedKernels
open AnalyticBridge AnalyticBridge.RelativeLogdet Physical Differential
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f} {P : Patch} {p : Teller G}
    {V : Config G c} {T : Tube G S} {s : S.Choices} {A : Stores S} {F : Forest S.ratio}
    {x a : ℝ} {B : Directions G c} {k n l j : ℕ}

structure Fund where
  C : ℝ -- ordinary A jet
  r : ℝ -- Deck curve neighbourhood
  σ : ℝ
  b₁ : ℝ -- Deck's own convergence exponent (not the one costing the letter lengths here)
  η : ℝ
  g : ℝ
  D : ℝ -- letter-base costs before off-center terms etc
  b : ℝ -- Speech rate
  b' : ℝ -- path Ticket rate
  d : ℝ -- HIT rate
  positive : 0<C ∧ 0<r ∧ 0<σ ∧ 0<b₁ ∧ 0<η ∧ 0<g ∧ 1≤D ∧ 0<b ∧ 0<b' ∧ 0<d

namespace Fund
variable (q : Fund)
def growth (k : ℕ) := faceBudget q.σ q.C q.η k
def width (G : Gauge) (k : ℕ) := min (radius G k/2) q.r
def letterFee (G : Gauge) (p k : ℕ) := scales G p k (q.growth k)
def micro (S : StepData c f) (x : ℝ) (k : ℕ) (w : Letter (Key G f) j) :=
    ticket (place S) (radiusB x) (q.growth k) q.D (currency q.b' (radiusB x)) w
def cost (S : StepData c f) (x : ℝ) (p k : ℕ) (w : Letter (Key G f) j) := q.letterFee G p k * q.micro S x k w
def baseTicket (G : Gauge) (p k : ℕ) := q.letterFee G p k * ((q.D+1)*q.D)

/-- Allows total under both determinant long classes: h-cost at scale ^k and Exp. -/
def myCost (k : ℕ) : ℝ := (2*((k:ℝ)+1))^k

def finalCost (G : Gauge) (p k : ℕ) := 4*q.letterFee G p k* Real.exp 1 * myCost k

lemma growing (k : ℕ) : 0 < q.growth k ∧ q.growth k ≤ q.σ := advert q.positive.2.2.1 q.positive.1.le q.positive.2.2.2.2.1 k
lemma amplitude (G : Gauge) (p k : ℕ) : 0<q.letterFee G p k := scales_pos ..
lemma coin : 1≤q.D := q.positive.2.2.2.2.2.2.1

lemma valid (G : Gauge) (k : ℕ) : 0<q.width G k := lt_min (half_pos (radius_pos ..)) q.positive.2.1


lemma myCost_high (k : ℕ) : 1 ≤ myCost k := one_le_pow₀ (by linarith only [Nat.cast_nonneg (α:=ℝ) k])

abbrev spoken (G : Gauge) (S : StepData c f) (l k : ℕ) (a x : ℝ) :=
  Stipend G S l k a q.σ q.C q.η 1 q.D q.b q.b' q.d (radiusB x)

/-- Specialize post-L. No purchase on a serialization of chain labels is
an input. Include cost overhead for x-local valuation of both long
classes' scalar Mayer factors, through k. -/
structure Stock (p : Teller G) (P : Patch) (l n k : ℕ) (a x : ℝ) : Prop where
  deck : Covariance.Deck G p P x q.C q.r k q.σ q.b₁ q.η q.g
  halo : 20 ≤ l
  expense : 0 ≤ a
  meters : Next.SectorChange.span P x ≤ radiusB x / 50
  buys {c f : Side} (S : StepData c f) : S.patch=P → q.spoken G S l k a x
  cover : q.finalCost G n k * currency q.d (radiusB x) ≤ currency (q.d/2) (radiusB x)

variable {q} (hq : q.Stock p P l n k a x) (hS : S.patch=P) (hT : p.Funds S T) (hL : 100*(1+radiusB x) ≤ c.val)
    (hV : A.flags=RG.flags (temp x) V)
    (hB : ‖B‖≤q.width G k)

structure Recital (q : Fund) (n k l : ℕ) (a x : ℝ) (A : Stores S) (T : Tube G S) (F : Forest S.ratio) (s : S.Choices) (V : Config G c)
    (B : Directions G c) : Prop where
  halo : 20 ≤ l
  paid : q.spoken G S l k a x
  scale_nn : 0≤a
  finite_support : Next.SectorChange.span S.patch x≤ radiusB x/50
  season : S.patch.Branches S.kernel G
  reach i : ‖B i‖ < radius G k
  authorized : Knew (marked G c (q.growth k)) (native c) (place S) (ray G c) ((paint G c).symm B) k q.σ q.C q.η 1
    (SelectedOrderedKernels.over (fun U => AFull T A F x U s) V)
  actual : (Rows.gram T x (increment V B) s (shots S x) A F).PosDef ∧ (fog A F T x (increment V B) s).PosDef
  combined : q.finalCost G n k * currency q.d (radiusB x) ≤ currency (q.d/2) (radiusB x)

include hq hS hT hL hV hB
lemma Stock.recite (s : S.Choices) (F : Forest S.ratio) : Recital q n k l a x A T F s V B := by
  have hi : ‖B‖ ≤ q.r := hB.trans (min_le_right ..)
  have hj : ‖B‖ < SelectedOrderedKernels.radius G k := (hB.trans (min_le_left ..)).trans_lt (half_lt_self (radius_pos G k))
  refine ⟨hq.halo,hq.buys S hS,hq.expense,hS.symm ▸ hq.meters,show S.patch.Branches S.kernel G from hT.knobs ▸ hT.kernel,
    fun i=> ?_, bought_here hq.deck hS hT hL hV hi F s (q.growing k).2,active_pos hq.deck hS hT hL hV hi F s,hq.cover⟩
  exact ((pi_norm_le_iff_of_nonneg (norm_nonneg B)).mp le_rfl i).trans_lt hj

omit hq hS hT hL hV hB

lemma Recital.maestro (h : Recital q n k l a x A T F s V B) :
    let e := q.growth k
    let H := SelectedOrderedKernels.over (fun U => AFull T A F x U s) V
    Speech (native c) (place S) (windows S x) (marked G c e) (ray G c) H ((paint G c).symm B) k e 1 q.D (currency q.b (radiusB x)) 1 ∧
      ∀ y, Aperture (place S) (radiusB x) (windows S x (G:=G)) (H y) := by
  intro e H
  exact ⟨h.paid.treasury h.authorized zero_le_one le_rfl (Eventually.of_forall (fun y => canons T A F x (increment V (paint G c y)) s))
    (Mark.position_move _ _ (q.growing k).1.le), fun y=> furnished T s (increment V (paint G c y)) h.season A F h.finite_support⟩
end Fund

theorem stores (G : Gauge) (P : Patch) (p : Teller G) (hP : P.Branches p.bind G) (n k l : ℕ) (hl : 20 ≤ l) (a : ℝ) (ha : 0≤a) :
    ∃ q : Fund, ∀ᶠ x in atTop, q.Stock p P l n k a x := by
  obtain ⟨r,hr,C₀,C,s₀,σ,b₀,b₁,e₀,η,g₀,g,hC₀,hC,hs,hσ,hb₀,hb₁,he,hη,hg₀,hg,hx⟩ := Covariance.coverall P G p hP k
  obtain ⟨D,b,b',d,hD,hb,hb',hd,h⟩ := march_future G P hσ hC.le hη k (U:=1) le_rfl (show 1≤l by omega) ha
  let q : Fund:=⟨C,r,σ,b₁,η,g,D,b,b',d,hC,hr,hσ,hb₁,hη,hg,hD,hb,hb',hd⟩
  refine ⟨q,?_⟩
  filter_upwards [hx,h,small_span P,Work.E01.radiusB_tendsto.eventually (currency_eventual (half_lt_self hd) (q.finalCost G n k))] with x hx hh he hD
  exact ⟨hx.2,hl,ha,he,@hh,hD⟩

end YM.PhysicalNext.EndpointLoadF16.DetLong
