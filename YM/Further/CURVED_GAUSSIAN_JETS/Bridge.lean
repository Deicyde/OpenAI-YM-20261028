import YM.Further.CURVED_GAUSSIAN_JETS.Units
import YM.SectorNext.VACUUM_NORMALIZATION.Ledger


/-!
# Reading the genuine sector column when a fluctuation substitution is supplied

Input not a symbolic Laplace equality with unspecified remainder:
`bill` and all branches/masks/K and scalar conventions spelled on same Rep
and same StepData at each V,A,t. Tree held; no independent tag resampling in
products. No log of the individual integrals. `swap` and `chart` intentionally
left as measure-change inputs; e.g. to prove one needs true chart coverage or
insert protective broad factors identically there. Never reimpose updated
cutoffs on just half of such an equality. Frozen variables retain THEIR
probability Haar. Euclidean substitution obligation before combining Haar
units, noise and any determinant extraction; no prefactor involving flat
TAG reference or identity completion at this port. No assumption of meaning
(e.g. closeness to stationary solution) from just giving D, F0, μ, C; pick the
very same size/metric and matrices as in further estimates. The added affine
square here has an exact counterterm inside, on all sectors, even if later
some paths there will be rolled into the distinguished output base.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 1024
noncomputable section
namespace YM.Further.CurvedGaussianJets
open RG Precision Wilson Push.SectorMeasure Presented SectorNext.Vacuum Next.Fluctuations.Sector
open MeasureTheory Matrix Lattice Tree Filter Pressure Pressure.Stores Function
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology
variable {G : Gauge} {c f : Side} {S : StepData c f} {F : Forest S.ratio}
  {x w : ℝ} (D : Allocation G S x w)

abbrev Ice {g : Ratio c f} {F : Forest g} (H : Finset F.Free) (G : Gauge) := H → G.El

def linkBits (H : Finset F.Free) (z : Vec (Bits H G)) (u : Soft H) : G.Color :=
  WithLp.toLp 2 (fun i : G.ColorIndex => z (u,i))

def configuration (V : Config G c) (H : Finset F.Free) (Y : Ice H G) (a : Vec (Bits H G)) : Config G f := F.drape
  fun i => if h : i∈H then Y ⟨i,h⟩ else G.lieExp (linkBits H a ⟨i,h⟩) * replica S.ratio V i.val

def density (R : Rep G f) (A : Stores S) (k : S.Choices) (V : Config G c) (U : Config G f) :=
    (D.bill A k U V * broad k U * post R.beta k V U) * stripped R U

def jac (J : ChartRatio G) (v : G.Color) := if v∈Metric.ball (0:G.Color) J.radius then J.J v else 0

structure SliceData (G : Gauge) (F : Forest S.ratio) (I : Type*) where
  holds : Finset F.Free
  rows : Ice holds G → Matrix I (Bits holds G) ℝ
  source : Ice holds G → Vec I
  center : Ice holds G → Vec (Bits holds G)
  cov : Ice holds G → Table (Bits holds G)

namespace SliceData
variable (J : ChartRatio G) (R : Rep G f) (A : Stores S) (k : S.Choices) (V : Config G c)
variable {I : Type*} [Fintype I] (P : SliceData G F I)

def paper (Y : Ice P.holds G) (a : Vec (Bits P.holds G)) :=
    (∏ i, J.scale * jac J (linkBits P.holds a i)) * density D R A k V (configuration V P.holds Y a)

def factor (G0 : Config G c → ℝ) (Y : Ice P.holds G) (a : Vec (Bits P.holds G)) :=
    (∏ i, jac J (linkBits P.holds a i)) * (Real.exp (G0 V + cost (P.rows Y) (P.source Y) R.beta a) *
      density D R A k V (configuration V P.holds Y a))

def takeLog (B : Table (Key F G)) (Y : Ice P.holds G) :=
    residualLog F J R.beta P.holds B (mount P.holds (gram (P.rows Y))) (mount P.holds (P.cov Y))

def cash (B : Table (Key F G)) (G0 : Config G c → ℝ) (g : ℝ) (Y : Ice P.holds G) (z : Vec (Bits P.holds G)) :=
    factor D J R A k V P G0 Y (P.center Y + g • z) * Real.exp (takeLog J R P B Y +
      tilt (P.rows Y) (P.source Y) R.beta g (P.cov Y) (P.center Y) z)

def received (B : Table (Key F G)) (G0 : Config G c → ℝ) (g : ℝ) :=
  ∫ Y : Ice P.holds G, (∫ z, cash D J R A k V P B G0 g Y z.ofLp ∂law (P.cov Y)) ∂(Measure.pi fun _ => G.probHaar)

/-- Exact measure change for the true integrands before expelling the vacuum
multipliers. `chart` includes support and iterated-integral concerns.
In `swap` the power g^card is the real scale Jacobian, then the Gaussian
is used with its ordinary inverse density before completing any sites or
combining exponents. These are INPUTS (companion task); identities of Bochner
integrals alone do not grant integrability/stability after truncation. -/
structure Change (g : ℝ) : Prop where
  chart : balance D F R.beta (stripped R) A k V = ∫ Y : Ice P.holds G, (∫ a : EuclideanSpace ℝ (Bits P.holds G),
    paper D J R A k V P Y a.ofLp) ∂(Measure.pi fun _ => G.probHaar)
  swap (Y : Ice P.holds G) : (∫ a : EuclideanSpace ℝ (Bits P.holds G), paper D J R A k V P Y a.ofLp) =
    let n := Fintype.card (Bits P.holds G)
    (g^n * (2*Real.pi)^((n:ℝ)/2) * Real.sqrt (P.cov Y).det) * ∫ z,
      paper D J R A k V P Y (P.center Y + g • z.ofLp) * Real.exp (quad (P.cov Y)⁻¹ z.ofLp / 2) ∂law (P.cov Y)

structure Design : Prop where
  pos (Y) : (gram (P.rows Y)).PosDef
  symm (Y) : (P.cov Y).IsHermitian
  short (Y) : ∃ q : ℝ, 0≤q ∧ q<1 ∧ Round.rowRate q (gram (P.rows Y)*P.cov Y-1)



omit [Fintype I] in
lemma open_paper (Y : Ice P.holds G) (a : Vec (Bits P.holds G)) : paper D J R A k V P Y a =
    J.scale ^ Fintype.card (Soft P.holds) * ((∏ i, jac J (linkBits P.holds a i)) * density D R A k V (configuration V P.holds Y a)) := by
  unfold paper; rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,mul_assoc]

lemma unit_cash (B : Table (Key F G)) (G0 : Config G c → ℝ) {g : ℝ} (hb : 0<B.det) (hβ : 0<R.beta) (hJ : LocalRatio J)
    (hg : 0<g) (he : R.beta*g^2=1) (h : P.Design) (Y : Ice P.holds G) (z : Vec (Bits P.holds G)) :
    let n := Fintype.card (Bits P.holds G)
    g^n * (2*Real.pi)^((n:ℝ)/2) * Real.sqrt (P.cov Y).det * (paper D J R A k V P Y (P.center Y + g • z) *
      Real.exp (quad (P.cov Y)⁻¹ z / 2)) = flatLine F J R.beta B * Real.exp (-G0 V) * cash D J R A k V P B G0 g Y z := by
  intro n
  have hg' : g^n * (2*Real.pi)^((n:ℝ)/2) = (2*Real.pi*g^2)^((n:ℝ)/2) := by
    rw [Real.mul_rpow (by positivity) (sq_nonneg g), ←Real.rpow_natCast_mul hg.le, show (↑(2:ℕ):ℝ)*((n:ℝ)/2) = (n:ℝ) by ring,
      Real.rpow_natCast, mul_comm]
  rw [hg', open_paper D J R A k V P, untilt (P.rows Y) (P.source Y) he (P.cov Y), Real.exp_add,cash, Real.exp_add,factor, Real.exp_add]
  obtain ⟨q,hq,hk,hh⟩ := h.short Y
  have hm := (regular_pays P.holds J hJ hβ hg he B hb (h.pos Y) (h.symm Y) hh hq hk).1
  change flatLine F J R.beta B * Real.exp (takeLog J R P B Y) = _ at hm
  have hneg : Real.exp (-G0 V) * Real.exp (G0 V) = 1 := by rw [← Real.exp_add, neg_add_cancel,Real.exp_zero]
  rw [show flatLine _ _ _ _ * _ * (_ * _) = ((flatLine F J R.beta B * Real.exp (takeLog J R P B Y)) *
      (Real.exp (-G0 V) * Real.exp (G0 V))) * ((∏ i, jac J (linkBits P.holds (P.center Y + g • z) i)) * Real.exp (cost _ _ _ _) * density D R A k V (configuration V P.holds Y _) * Real.exp (tilt _ _ _ _ _ _ _)) by ring,
      hm, hneg, mul_one]; dsimp only [n]; ring

theorem balance_cash (B : Table (Key F G)) (G0 : Config G c → ℝ) {g : ℝ} (hb : 0<B.det) (hβ : 0<R.beta) (hJ : LocalRatio J)
    (hg : 0<g) (he : R.beta*g^2=1) (h : P.Design) (hc : Change D J R A k V P g) :
    balance D F R.beta (stripped R) A k V = flatLine F J R.beta B * Real.exp (-G0 V) * received D J R A k V P B G0 g := by
  rw [hc.chart]; simp_rw [hc.swap]; unfold received
  rw [← integral_const_mul]; apply integral_congr_ae; filter_upwards with Y
  rw [← integral_const_mul,← integral_const_mul]; apply integral_congr_ae; filter_upwards with z
  exact unit_cash D J R A k V P B G0 hb hβ hJ hg he h _ _

end SliceData
open SliceData
variable {I : Type*} [Fintype I] (P : Stores S → S.Choices → Config G c → SliceData G F I)
  (J : ChartRatio G) (R : Rep G f) (B : Table (Key F G)) (G0 : Config G c → ℝ) {g : ℝ}



def paid := -wires c*Real.log (S.penaltyZ R.beta G) + nt F*Real.log (gaussLink J R.beta) - Real.log B.det / 2


variable (hb : 0<B.det) (hβ : 0<R.beta) (hJ : LocalRatio J)
    (hg : 0<g) (he : R.beta*g^2=1) (h : ∀ a k V,(P a k V).Design) (hc : ∀ a k V, Change D J R a k V (P a k V) g)
include hb hβ hJ hg he h hc





/-- Input compiler uses the actual transformed remainder after Gaussian
accounting. Coefficientwise atoms still a major reconstruction problem;
this interface is BEFORE first-gas/log/scalar normalization. Can thus feed
`office`/`traffic` which no longer need a v' hypothesis. -/
def compiler (X : ℕ → Support c) (b : BudgetPoint) (E : ℕ → Config G c → ℝ) (d : Activities G c)
    (atoms : Stores S → S.Choices → Finset ℕ → Finset ℕ → Config G c → ℝ)
    (hsum : ∀ a k V,Summable fun i : Finset ℕ × Finset ℕ => atoms a k i.2 i.1 V)
    (hre : ∀ a k V,received D J R a k V (P a k V) B G0 g = ∑' i : Finset ℕ × Finset ℕ, atoms a k i.2 i.1 V)
    (hatom : ∀ P Q V,(∑ a,∑ k, tagRef k * atoms a k P Q V) = d.gasOccurrence b Q V *
      ReLog.note X (ReLog.herald X b E V) (Finset.univ \ ReLog.pad d Q) P) : Counter D F J B G0 R X b E d where
  work a k P Q V := flatLine F J R.beta B * Real.exp (-G0 V) * atoms a k P Q V
  settle a k V := (hsum a k V).mul_left _
  scanned a k V := by
    rw [tsum_mul_left, ← hre, balance_cash D J R a k V (P a k V) B G0 hb hβ hJ hg he (h ..) (hc ..)]
  compiled T Q V := by rw [←hatom,Finset.mul_sum]; exact Finset.sum_congr rfl fun a _=> by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => mul_left_comm ..

end YM.Further.CurvedGaussianJets
