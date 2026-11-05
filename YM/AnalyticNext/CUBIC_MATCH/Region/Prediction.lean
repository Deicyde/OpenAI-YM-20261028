import YM.AnalyticNext.CUBIC_MATCH.Region.Compass

set_option warningAsError false

/-!
# Mat terms of `noiseTaylor`, on their chosen references

Literal compensation as from the chart-tree proof. Read `S.patch`, root
shift and all weights and all colors. Sum at compatible widths. Repeated
periods/windings, no choosing s-dependent heads. No analytic through Plot.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CubicMatch
open Function Filter Lattice Laurent RG Wilson Precision Exterior Tree Tensor Bid Push Branch
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators
attribute [local instance] Gauge.frobInner

variable {G : Gauge} {μ : Type*} {c f : μ → Side}
  {θ C B : ℝ} {P : Patch} {K : KernelChoices} {V : ∀ p, Dir G (c p) → Dir G (f p)}

section simple
variable {F : GermRead G c G.Mat}

lemma shiftsTerm (h : RayReceipt c θ B C F) (d : Axis) : RayReceipt c θ (Real.exp θ*B) (Real.exp (θ*2)*C)
    (fun p x a v => F p (x+step d) a v) := by
  have hz (k : ℕ) (A : ℝ) (h : LocalRep c k θ A (makesTerm F k)) := h.translateSite (step d)
  simp only [Nat.cast_one,size_unit,mul_one,wrap_step] at hz
  refine ⟨fun _ _ _ => h.smooth ..,fun _ _ _ => h.initial .., ?_,?_⟩
  · have hx := hz 1 B h.first; rw [Nat.cast_one,mul_one] at hx
    refine hx.fits (fun p x a => ?_); unfold makesTerm; rw [add_comm]
  have hx := hz 2 C h.second; push_cast at hx; refine hx.fits (fun p x a => ?_); unfold makesTerm; rw [add_comm]

end simple

def bondFirst (T θ : ℝ) := hatOne T+T+Real.exp θ*hatOne T

def bondSecond (G : Gauge) (T θ : ℝ) := hatTwo G T+hatOne T*T+T^2+(hatOne T+T)*(Real.exp θ*hatOne T)+Real.exp (θ*2)*hatTwo G T

def receiveOne (G : Gauge) (T θ : ℝ) := aimSlope G*bondFirst T θ
def receiveTwo (G : Gauge) (T θ : ℝ) := aimSec G*bondFirst T θ*bondFirst T θ+aimSlope G*bondSecond G T θ

variable (eqs : ∀ p : μ,(f p).val=(c p).val*P.L.val)
  (t : ∀ p,(perform P K eqs p).Choices)
  (h : ScaleRead c f P.L (mainRoot eqs) V θ C) (he : P.Branches K G)
include h he



/-- Cost of compensating ray at one coarse edge. -/
def gaugeHop (G : Gauge) (T : ℝ) := 2 * G.colorScale⁻¹*T
def bearing (G : Gauge) := (Fintype.card G.ColorIndex : ℝ)
def expLin (G : Gauge) (A : ℝ) := G.colorScale*A
def expSquare (G : Gauge) (A : ℝ) := ‖sec (fun u => G.mat (G.lieExp u)) 0‖*A*A

def outerOne (G : Gauge) (T θ : ℝ) :=
    let A := expLin G (gaugeHop G T);
    A + expLin G (bearing G) + Real.exp θ*A
def outerTwo (G : Gauge) (T θ : ℝ) :=
    let A := expLin G (gaugeHop G T)
    let B := expSquare G (gaugeHop G T)
    let C := expLin G (bearing G)
    B+A*C+expSquare G (bearing G)+(A+C)*(Real.exp θ*A)+Real.exp (θ*2)*B

omit he in
lemma balancePayment (d : Axis) : RayReceipt c θ (outerOne G (journey G P.J C θ) θ) (outerTwo G (journey G P.J C θ) θ)
    (fun p x a v => G.mat (compensation (perform P K eqs p) a (V p a) v (x,d))) := by
  let T := journey G P.J C θ; let M p := perform P K eqs p
  let U := fun p (x : Site (c p)) (a : Dir G (c p)) (v : ℝ) => G.mat (rootTurn (psi (M p) (V p a)) v x)
  have he : RayReceipt c θ (expLin G (gaugeHop G T)) (expSquare G (gaugeHop G T)) U := by
    unfold U rootTurn; exact receiptExp (h.rootMotion eqs K).negative
  have hh : RayReceipt c θ (expLin G (bearing G)) (expSquare G (bearing G))
      (fun p x (a : Dir G (c p)) (v : ℝ) => G.mat (represent (v • a) (x,d))) := by
    simp_rw [Work.F03.represent_link, Pi.smul_apply]; exact receiptExp (one_address h.rate _)
  unfold compensation Lattice.gauge; simp_rw [G.mat_mul,G.mat_inv]; exact (he.mul hh).mul (shiftsTerm he d).back

def balanceOne (G : Gauge) (T θ : ℝ) := outerOne G T θ+receiveOne G T θ

def balanceTwo (G : Gauge) (T θ : ℝ) := outerTwo G T θ+outerOne G T θ*receiveOne G T θ+receiveTwo G T θ

def subsidy (G : Gauge) (T θ v : ℝ) := (Fintype.card Axis:ℝ)*v*(G.colorScale^2)⁻¹*(balanceOne G T θ * balanceTwo G T θ)

omit h he in
lemma subsidy_pos (hT : 0 ≤ C) {a : ℝ} (hv : 0≤a) : 0 ≤ subsidy G C θ a := by
  have hS := G.colorScale_pos.le; have hh := hatTwo_nonneg G hT
  have hm := aimSlope_nonneg G; have ha := aimSec_nonneg G
  unfold subsidy balanceOne balanceTwo outerOne outerTwo receiveOne receiveTwo bondFirst bondSecond expLin expSquare bearing gaugeHop hatOne
  dsimp only; positivity


end YM.CubicMatch
