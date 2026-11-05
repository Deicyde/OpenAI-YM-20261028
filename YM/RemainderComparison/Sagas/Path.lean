import YM.RemainderComparison.Portal.Wire
import YM.RemainderComparison.Herbal.Chart
/-! # Polar.RG02 seam as structural jet plus authentic LONG displacement estimates
Use monomer as any rooted account label. In CPPT, Y link factors are station
potential legs at offsets, prefixes (ℕ-index) occupied exactly once.Winding defects from kin and stencil registration must be paid separately unless assigned
true length by kernel analysis. Ownership of wallets left explicit. Presentation
of jet contraction itself (propagators, spin bases etc) does not come from this
interface. No equality of actual densities with desired series assumed; this identity
is on finite polynomial coefficients in E. Need authenticate both germs and this
identification independently of closeness.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Sagas
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson MeasureTheory ProbabilityTheory Finset
open Push Push.AbsoluteSums Animals Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Coat Blaze March Poll Brush Blaze.Frond
open PhysicalNext PhysicalNext.Repeat Song Push.Uniform Sienna Fare Lapis Boulevard Metric Lantern Slide
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration
open Height Input Org Supply Pane Push.PriceCompiler ThroughLaunch Bid Planned.JetPort
open YM.RemainderComparison.Aux Portal Herbal
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E]
variable {G:Gauge}{ι:Type} {L:Side} {A' v Δ:ℝ}
set_option quotPrecheck false
local notation "Y"=> (E →L[ℝ] ℝ)

/-- one polynomial monomial with derivative orders absorbed in legs and coeff -/
structure Link (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E] where
    coeff : ℝ
    arity : ℕ
    legs : Fin arity→ (E →L[ℝ] ℝ)
    -- put stencil data in real registration.M.Payload.Weight. Not redefining lengths by scaled values.
    length : ℕ
namespace Link
variable (Q:Link E)(t:ℝ)(x:E)

def earns := |Q.coeff| *∏ i, ‖Q.legs i‖
def toll := Q.earns*Real.exp (t*Q.length)
def spin := Q.coeff*∏ i, Q.legs i x
lemma income : 0 ≤ Q.earns:= mul_nonneg (abs_nonneg _) (prod_nonneg fun _ _=> norm_nonneg _)
lemma pays : 0 ≤ Q.toll t:= mul_nonneg (income _) (Real.exp_pos _).le
end Link
variable {m k j:ℕ} (F:ℕ→ι→Link E)(X Z:ℝ×E→ℝ) {δ:ℝ}
-- NOTE ℓ may include high-weight terms also at non-wound discrepancy. Use only genuine source-support/active R.Ph estimates.Direction x at boundary.P.Frame.R.
/-- Defect enumeration. Use before requesting precision. Linear projection
    or compiling stencil in unit normalization.Sensor leases.
  Coef is ABI exact equality from RG02. Allows infinite coefficient sums
  over length. Uses ∑ over tails only. -/
structure Ledgered (F:ℕ→ι→Link E)(X Z:ℝ× E→ℝ)(N:ℕ)(η B : ℝ)(p r:ℕ): Prop where
    bills (i) : i ≤ p → SumBudget (fun z=> (F i z).toll η) B
    arities i z : i≤p → (F i z).arity≤r
    coeff i : i≤p →∀ v:E, Trace.coefficient X i v - Trace.coefficient Z i v = ∑' z: {z//N ≤ (F i z).length}, (F i z.val).spin v

lemma mul_allows {F G:E→ℝ} {k:ℕ} {x:E}{A B:ℝ}(hf: Allows k F x A)(hg:Allows k G x B) : Allows k (fun u=> F u * G u) x (2^k*A*B):=by
    convert hf.bilinear (ContinuousLinearMap.mul ℝ ℝ) hg (ContinuousLinearMap.opNorm_mul_le ..) using 1
    · rfl
    ring
variable (j)

def area (x:ℝ):= (2:ℝ)^j*(1+|x|)
lemma booked {δ} : 1 ≤ area j δ:=one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) (le_add_of_nonneg_right (abs_nonneg _)) -- fix
lemma acts (x:E) (Q:Link E) (h:‖x‖ ≤1+|δ|): Allows j Q.spin x (area j δ ^ (Q.arity) * Q.earns):=by
    let v:=1+|δ|; have hv:1≤v:= le_add_of_nonneg_right (abs_nonneg _)
    have hQ(i): Allows j (fun x=>Q.legs i x) x (v*‖Q.legs i‖):= by
       apply Uniform.allows_linear (le_mul_of_one_le_left (norm_nonneg (Q.legs i)) hv) ((ContinuousLinearMap.le_opNorm (Q.legs i) x).trans ((mul_le_mul_of_nonneg_left h (norm_nonneg _)).trans_eq (mul_comm _ _)))
    let g p (x:E):= ∏ i∈p,Q.legs i x
    have hp(p:Finset (Fin Q.arity)): Allows j (g p) x (area j δ ^ (p.card) * ∏ i∈p, ‖Q.legs i‖):=by
       induction p using Finset.induction_on with
       | empty => simpa only [Finset.card_empty,pow_zero, Finset.prod_empty,mul_one,g] using! (allows_const (n:=j) x (show ‖(1:ℝ)‖≤1 by simp))
       | insert i s hi hs=>
          unfold g; simp_rw [prod_insert hi, card_insert_of_notMem hi]
          refine (mul_allows (hQ i) hs).mono ?_ -- j implicit?
          apply le_of_eq; unfold v; rw [pow_succ]; unfold area; ring
    convert (hp univ).smul Q.coeff using 1
    · rfl
    unfold Link.earns; rw [Finset.card_univ,Fintype.card_fin]; ring
variable {B R:ℝ}{N:ℕ}(ht:Ledgered F X Z N δ B k m)(hp:0≤δ)
include hp ht
-- PAX.Point Γ captures T cuts and contact.Internal Marker.P.
def pigment (d:ℝ)(m:ℕ):=Real.exp (- (d*m))
lemma reckons (x:E)(hx:‖x‖ ≤ R): JMatch X Z x k j ((area j R^m)* (Sagas.pigment δ N*B)):=by
    constructor; intro i hi; have hH:= ht.coeff i hi
    let t:= {z:ι|N ≤ (F i z).length}; let x' (z: t):=F i z.val
    let v:= area j R; let a:= Sagas.pigment δ N; have hb:1 ≤v:= booked j
    have he : SumBudget (fun z:t=> v^m * (x' z).earns) (v^m*(a*B)):=by
       apply Cost.scale _ _ (by positivity); let g z := (F i z).toll δ; have hV: SumBudget (fun z:t=> g z.val) B:= budget_pull (fun z:t=> z.val) Subtype.val_injective (ht.bills i hi)
       refine budget_mono (Cost.scale hV a (Real.exp_pos _).le) (fun i=>(x' i).income) fun q=>?_
       let M:=x' q; change M.earns ≤ Sagas.pigment δ N*(M.earns * Real.exp (δ*M.length))
       rw [mul_left_comm,Sagas.pigment,← Real.exp_add]; apply le_mul_of_one_le_right (M.income); exact Real.one_le_exp (by have hu:N ≤ M.length:=q.prop; nlinarith only [mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hu) hp])
    let s:= ball (0:E) (1+|R|)
    simp_rw [hH]
    apply Herbal.dons Metric.isOpen_ball (convex_ball (0:E) (1+|R|)|>.isPreconnected) he
    · intro z y hy; exact (Sagas.acts j y (x' z) ((mem_ball_zero_iff.mp hy).le)).mono (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hb (ht.arities i z.val hi)) ((x' z).income))
    apply mem_ball_zero_iff.mpr; exact (hx.trans (le_abs_self _)).trans_lt (lt_add_of_pos_left _ zero_lt_one)
end YM.RemainderComparison.Sagas
