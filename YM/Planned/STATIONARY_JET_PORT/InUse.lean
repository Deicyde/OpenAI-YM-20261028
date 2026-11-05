import YM.Planned.STATIONARY_JET_PORT.Compose
import YM.Planned.STATIONARY_JET_PORT.Pack
import YM.Push.STATIONARY_UNIFORM.Along


set_option warningAsError false

/-!
# The actual stationary branch and Hessian for matching

Spend the uniform prices in the native real variables of exactly the scene
step and EXACT selected path and predictions. Can be consumed anywhere in
this real-ball, finite-order regime. No strip claims, reperiodizations or
claims of recovering a fixed fraction of a width PER step. API here:

* `Counter.service`: give a Before purchase at order `N+3`. Sinusoidal
  matching (older interfaces) uses only VERY LOW orders on external fields,
  but notably needs at least the fourth derivatives of the full score
  (two Hessian slots already spent). This invoice can be run for any desired
  N, exports to order N+3 for the effective classical action, N+2 for the
  critical branch, and N+1 through the Hessian, its inverse and trace-log.
  Positivity & all orders on that service's FULL real domain (H also with
  off-shell joint derivatives through N+1 on safety). Shifts and restrictions
  keep the same domain (logdet norm factor (1+u)⁻¹ holds still!).
  Counting real color axes exactly `Scatter` / native α conventions. See
  additional consumers for old `Answer` port, physical directions & further
  packing/calculus.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.JetPort
open Push Push.Uniform Filter Function Set Metric Lattice Matrix RG Precision Tree Bid
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {c f : Side} {S : StepData c f} {B : Forest S.ratio}
    {p : Clip} {R : PathData G} {Q : KernelChoices} {μ C Λ : ℝ} {N j : ℕ}
    {A : Before G μ C j Q (N+3)}
    {g : In G c → AxisChart G B}

abbrev domain (Y : ChartPrices) := ball (0 : Positions (Primary c G)) Y.horizon
abbrev account (B : Forest S.ratio) (G : Gauge) := Uniform.address B G
def acq (t : S.Choices) (p : Clip) (R : PathData G) (y : Positions (Joint B G)) :=
    let v := paint B G y; hessian B t p R v.1 v.2
def inside (t : S.Choices) (p : Clip) (R : PathData G) (g : In G c → AxisChart G B) (y : Positions (Primary c G)) :=
    let x := tint G _ y; hessian B t p R x (g x)

lemma block_identity (t : S.Choices) (p : Clip) (R : PathData G) (v : Positions (Joint B G))
    (he : ContDiffAt ℝ ω (priced B t p R) v) :
    block (priced B t p R) v=acq (B:=B) t p R v := by
  -- reduce to physical coordinates on coarse and free legs; block includes
  -- accounting for additive reindexing from the supplied Uniform pack.
  let T := partSpace (Primary c G) (Key B G)
  obtain ⟨x,y,h⟩ : ∃ x y, meetVar (ι:=Primary c G) (τ:=Key B G) x y = v :=
    ⟨(T v).1,(T v).2,T.symm_apply_apply v⟩
  subst v; unfold acq; rw [paint_meet]; exact block_congr B t he

lemma along_block (t : S.Choices) (p : Clip) (R : PathData G) (g : In G c → AxisChart G B) :
    inside t p R g=acq (B:=B) t p R ∘ curve (Uniform.station g) := by
  funext x; unfold inside acq Function.comp curve Uniform.station
  dsimp only [Function.comp_def]; rw [paint_meet]; dsimp only; rw [(tint G _).apply_symm_apply]

-- Explicit tariffs relative to this ONE Before

def pathCost (Y : ChartPrices) (k : ℕ) := curveCost Y.coords Y.value Y.width Y.gap k
def pathRate (Y : ChartPrices) (N : ℕ) := responseRate Y.coords (N+3) Y.value Y.width Y.gap
def transit (Y : ChartPrices) (N : ℕ) := litSpan (N+1) (pathRate Y N) Y.width
def chargeBill (Y : ChartPrices) (N : ℕ) :=
  Y.value * machinist (N+1) Y.coords (pathCost Y (N+1)) Y.width
def classicalBill (Y : ChartPrices) (N : ℕ) := onShellCost Y.width Y.value Y.coords (N+3) Y.gap
def classicalRate (Y : ChartPrices) (N : ℕ) := weaker (N+3) (pathRate Y N)

-- sockets, every order up to indicated on this very same g. The accepted
-- older Interface needs only zero jets at normalized points & analytic germs;
-- exercising from this radius port doesn't authorize extra comparisons of
-- exponential width in momentum. Use Rate consumer for L-power verification.
structure Counter (Y : ChartPrices) (N : ℕ) (t : S.Choices) (p : Clip) (R : PathData G) (g : In G c → AxisChart G B) : Prop where
  off {v : Positions (Joint B G)} : v ∈ closedBall 0 Y.safety →
    BlockPack (account B G) (account B G ∘ Sum.inr) Y.coords N Y.width (Y.gap/2) Y.value (acq (B:=B) t p R) v
  carrier {x} : x∈domain Y → ContDiffAt ℝ ω (curve (Uniform.station g)) x ∧
    ∀ k ≤ N+2, 0<pathRate Y N ∧ 0<pathCost Y k ∧
      Envelope (account B G ∘ Sum.inl) (account B G) (pathRate Y N) k (curve (Uniform.station g)) x (pathCost Y k) ∧
      Envelope (account B G ∘ Sum.inl) (account B G ∘ Sum.inr) (pathRate Y N) k (Uniform.station g) x (pathCost Y k)
  classical {x} : x∈domain Y →
    let f y := tested B t p R (tint G _ y) (g (tint G _ y))
    ContDiffAt ℝ ω f x ∧ 0<classicalRate Y N ∧ 0<classicalBill Y N ∧
      Scatter (account B G ∘ Sum.inl) (classicalRate Y N) (N+3) f x (classicalBill Y N)
  alongShell {x} : x∈domain Y →
    BlockPack (account B G ∘ Sum.inl) (account B G ∘ Sum.inr) Y.coords N (transit Y N)
      (Y.gap/2) (chargeBill Y N) (inside t p R g) x

-- positivity of these tickets from actual curvature receipts
section Real
variable (hg : A.Service B p R g) (hp : R.Bounds p μ C Λ) (hK : Larger (G:=G) S) (hj : S.patch.J=j) (ht : S.kernel=Q)
    (t : S.Choices)
include hp hK hj ht
lemma Counter.background (v : Positions (Joint B G)) (hv : v∈closedBall 0 (A.tables p S.patch).safety) :
    let Y := A.tables p S.patch
    BlockPack (account B G) (account B G ∘ Sum.inr) Y.coords N Y.width (Y.gap/2) Y.value (acq (B:=B) t p R) v := by
  intro Y
  let α := account B G
  let F := priced B t p R
  have hr := (A.receipt B t hp hK hj ht).1
  obtain ⟨hf,hb⟩ := hr.born v (closedBall_subset_ball hr.reserveH_lt hv)
  change ContDiffAt ℝ ω F v at hf
  have he : block F =ᶠ[𝓝 v] acq (B:=B) t p R := (hf.eventually (by simp)).mono (fun k => block_identity t p R k)
  let b : Key B G → Joint B G := Sum.inr
  have hA : bornMatrix (block F) v := bornBlock b hf
  have hw : Cable α (α ∘ b) (α ∘ b) none Y.width (N+1) (block F) v Y.value := makeCable hf hb (by omega)
  refine establish hr.pos_a hr.pos_C (half_pos hr.pos_m) (fun i j => (hA i j).congr_of_eventuallyEq ?_) ?_ ?_
    (hw.germ he) (hr.mult.comp (Sum.inr_injective))
  · filter_upwards [he] with x hx; rw [← hx]
  · rw [← he.eq_of_nhds]; exact block_hermitian hf
  rw [← he.eq_of_nhds]; exact hr.snaps _ hv
include hg
/-- Extra analytic input, no open comparison or scheduled existence
assumptions. (Always builds the stated interface ON every funded/larger use.) -/
theorem Counter.service : Counter (A.tables p S.patch) N t p R g := by
  let Y := A.tables p S.patch
  let α := account B G; let β : Primary c G → Site f := α ∘ Sum.inl
  let γ : Key B G → Site f := α ∘ Sum.inr
  let Z := Uniform.station g; let F := curve Z
  have hr := (A.receipt B t hp hK hj ht).1
  have hd : 0<pathRate Y N := rate_pos hr
  have hv (k : ℕ) : 1 ≤ pathCost Y k := curveCost_ge hr k
  have hC (x) (hx : x ∈ domain (G:=G) (c:=c) Y) (k : ℕ) (hk : k ≤ N+2) : Envelope β α (pathRate Y N) k F x (pathCost Y k) :=
    envelopes hr (hg.series hx) (hg.pricing hx) (hg.entered hp hK hj ht hx t) (show k<N+3 by omega)
  have off {v : Positions (Joint B G)} (hv : v ∈ closedBall 0 Y.safety) := Counter.background (A:=A) (B:=B) hp hK hj ht t v hv
  refine ⟨fun {_} => off, fun {x} hx => ⟨along (hg.series hx),fun k hk =>
    ⟨hd,zero_lt_one.trans_le (hv _),hC x hx k hk,hg.coefficient hp hK hj ht (show k<N+3 by omega) hx⟩⟩,fun {x} hx => ?_,fun {x} hx => ?_⟩
  · obtain ⟨hh,he⟩ := hg.station_cost hp hK hj ht hx t
    refine ⟨hh,(show 0<classicalRate Y N from div_pos hd (by positivity)),?_,he⟩
    change 0 < classicalBill Y N
    have hw := count_pos (half_pos (show 0<Y.width from hr.pos_a))
    have he : (∑ i ∈ Finset.range (N+3), (Fintype.card (OrderedFinpartition i):ℝ)) = partitionsBill (N+2) := rfl
    unfold classicalBill onShellCost; rw [he]
    have H := (zero_lt_one.trans_le (partitionsBill_one (N+2))); have ht := (show 0<Y.value from hr.pos_C)
    have hl := zero_lt_one.trans_le (hv (N+3-1)); unfold pathCost at hl; positivity
  have he := off (hg.pricing hx)
  rw [along_block]
  have ht : 0 ≤ pathCost Y (N+1) := zero_le_one.trans (hv _)
  have H := hC x hx (N+1) (by omega)
  have hh : ContDiffAt ℝ ω F x := along (hg.series hx)
  refine establish (litSpan_pos hd hr.pos_a) (mul_pos hr.pos_C (machinist_pos ht hr.pos_a))
    (half_pos hr.pos_m) (fun i j => (he.smooth i j).comp (f:=F) x hh) he.herm he.pay
    (Cable.attach he.smooth hh he.coefficient H hr.pos_a hd hr.pos_C.le ht hr.mult) ?_
  exact hr.mult.comp (Sum.inr_injective)
end Real
end YM.Planned.JetPort
