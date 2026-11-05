import YM.PhysicalNext.ORDERED_AFFINE_2B.CompactResolvent
import YM.PhysicalNext.ORDERED_AFFINE_2B.SymTravel
import YM.PhysicalNext.ORDERED_AFFINE_2B.Till

/-!
# C^n and ORDERED first through n'th reads of each grouped symbol

Through the scalar post-L resource calendar associated to the single
physical V/Teller. Provision even in spectrum integrals and local paired
logs (in Lean these wrappers use particular shifted prices, not crossing
hard priceAll branches). Reuse computation with all the *actual ordered
left frames* inc noncommuting slots. All dips into declarations
refer to sector-local DERIVATIVES about eligible base data. No other
prescribed identities about functions differenced after regrouping.

`Symbol.cost` form uses the new grouped labels, prices compare INNER
atoms in `Atom G f`. Always cost the entire assignment halo. `Slot`
ρ grouping here is spatial and also index of channel, per signed
allowance. Bounds with Tour & service issuance below.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.OrderedAffine2B.SymBooks
open Function Filter Set Lattice RG Wilson Precision Tree Pressure Stores
open Next Next.SectorChange AnalyticBridge.GaussianFieldAlignment Orthogonal Tensor Whole Matrix
open Further Further.CurvedGaussianJets Jets Tracks Completion SymRows SymWhole SymFare SymTravel
open AnalyticBridge AnalyticBridge.Covariance Terrain  ProjectorNext.Equivariance
open MeasureTheory SectorNext.Vacuum Push.SectorMeasure Footprint
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {d j m q n : ℕ} {x : ℝ}
local notation "Coords" => Next.SectorChange.Prices

-- Declarative ordered reads on versions. Attach proof of C^n,
-- then actual left deriv eq always include rank zero.
def Symbol (V : Config G c) (n : ℕ) (F : Config G c → ℝ) (f : Word G c→ℝ) := HasOrderAt F V n ∧
    ∀ l : Word G c,l.length≤n → leftDerivs F l V=f l
lemma finite {α : Type} [Fintype α] {V : Config G c} (F : α→ Config G c→ℝ) (h : ∀ i, HasOrderAt (F i) V n) : Symbol V n (fun u=>∑ i, F i u) (fun l=>∑ i,leftDerivs (F i) l V) := by
  unfold Symbol; constructor
  · apply ContDiffAt.sum; exact fun i _ => h i
  intro l hl
  exact ChangeV.left_sum F l V Finset.univ (fun i _=> (h i).of_le (by exact_mod_cast hl))

lemma pieces {α β : Type} [Fintype β] [DecidableEq α] [DecidableEq β] {V : Config G c} (F : Run (α×β) d→ Config G c → ℝ)
    (p : Run α d) (he : ∀ i : Run β d,HasOrderAt (F (mix p i)) V n) : Symbol V n (fun v=>close p (fun j=> F j v)) (fun l=>close p (fun j=>leftDerivs (F j) l V)) := by
  let h (i : Run β d) := p (Fin.last d)=p 0 ∧ i (Fin.last d)=i 0
  let u (i : Run β d) (v : Config G c) := if h i then F (mix p i) v else 0
  -- match decidables while rewriting
  have H := finite (n:=n) u fun i=> by unfold u; split_ifs; exact he i; exact contDiffAt_const
  unfold Symbol; constructor
  · convert H.1 using 1; ext v; unfold close u h; congr!
  intro l hl; change leftDerivs (fun v=> close p _) l V = close p _
  rw [show (fun v=>close p (fun j=>F j v))=(fun v=> ∑ i,u i v) by funext; unfold u close h; congr!, H.2 _ hl]
  unfold close; refine Finset.sum_congr rfl fun i _=>?_ ; unfold u h; split_ifs; rfl; simp [Work.G07.left_const]


variable {A : Stores S} {F : Forest S.ratio} {k : S.Choices} {T : Tube G S} {V : Config G c}
  {σ : ℝ} {J : Tab} (h : J.Ships q n σ T F A k x V) (y : Bool)
include h

structure Ticket (W : Windows (Thing G f)) (V : Config G c) (n : ℕ) (C : Jets.Field G c (Thing G f)) (J : Tab) : Prop where
  one (i : Bond f) : Symbol V n (lap W C J.v i) (fun l=>∑ j : G.ColorIndex, Fsct.localLap W C J l V (i,j))
  two {d : ℕ} (p : Run (Bond f) (d+1)) : Symbol V n (correction W C p) (fun l=>close p (fun j=> leftDerivs (pushLog W C j) l V))
  pay {d : ℕ} (p : Run (Bond f) (d+2)) : Symbol V n (aside W C p) (fun l=>close p (fun j=> leftDerivs (mailed W C j) l V))
  yld {d : ℕ} {u : ℝ} (hu : 0≤u) (p : Run (Bond f) (d+2)) : Symbol V n (sailingFee W C u p) (fun l=>close p (fun j=> leftDerivs (sailing W C j u) l V))
  reservoir {d : ℕ} (p : Run (Bond f) (d+2)) (z : Coords G (Bond f)) : Symbol V n (trough W C z p) (fun l=>facing p z z (fun j=> leftDerivs (pushQuad W C j) l V)/2)


omit h

-- Similar short entries. Wages outside the F0.eta grouping to avoid
-- multiplying the rank of its frozen factors. These definitions full
-- supported even when called for tree links.

section chores
variable (T : Tube G S) (x : ℝ) (A : Stores S) (F : Forest S.ratio) (k : S.Choices)
    (χ : Chi) (d g : ℝ) (Y : LinkArray G (Frozen A x F))

def charge (i : Slots S) (U : Config G c) := ∑ j:G.ColorIndex,Fixed.debit T x A F k χ d Y g U (i,j)

end chores

variable {χ : Chi} {ε g s t C : ℝ} (hK : Fixed.Fees T x A F k χ ε V n s t C) (hg : 0<g)
    (Y : LinkArray G (Frozen A x F))
include hK hg


end YM.PhysicalNext.OrderedAffine2B.SymBooks
