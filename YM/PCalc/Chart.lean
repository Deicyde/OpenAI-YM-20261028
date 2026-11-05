import YM.PREC.TreeMatch

/-!
# Slice chart, unclipped analytic functions (formal germ ports)

E a(B) taken from actual branch on specified tree. Hessian determinant later
uses physical color coords and DOES include Haar-chart relative ratios.
Keep exponent threshold and hard indicators out of these germs. To use the
series must prove receipt; nonnegative term & Wilson density do not extend
these sums across the whole contour family. These functions fix the readout
and stationary formulas over Cover-slot atoms here. No assertion they're
analytic or that Taylor matching is possible just from these defs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Precision
open Lattice Wilson RG Matrix Exterior Finset Tree Function
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff

variable {c f : Side} {S : StepData c f} {g : Ratio c f} {n : Side} {G : Gauge}

/-- no masks, links in physical orientations. -/
def uncut {m : ℕ} (A : ℕ → Atom G m) (U : Config G n) := ∑ x : Site n, ∑' i, (A i).unmasked U x
def quadratic (p : Clip) (R : PathData G) (U : Config G n) :=
    ∑ b : Face (Per n), (p.direct*G.price (faceValue U b) + ‖R.ell U b‖^2/2)

def mainTerm (p : Clip) (R : PathData G) (U : Config G n) :=
    Patch.average fun h : Signed => quadratic p R (pull h 0 U) + uncut R.cubic (pull h 0 U)+uncut R.quartic (pull h 0 U)

def secondTerm (p : Clip) (R : PathData G) (U : Config G n) := Patch.average fun h : Signed => quadratic p R (pull h 0 U)

def loop (R : PathData G) (U : Config G n) := Patch.average fun h : Signed => uncut R.loop (pull h 0 U)

/-- T_cp copy to internal/crossing, group version. Use Side c>1. -/
def replica (g : Ratio c f) (V : Config G c) : Config G f := fun e =>
    if g.parent (e.1+step e.2)=g.parent e.1 then 1 else V (g.parent e.1,e.2)

def linearCopy (g : Ratio c f) (b : Directions G c) : Directions G f := fun e =>
    if g.parent (e.1+step e.2)=g.parent e.1 then 0 else b (g.parent e.1,e.2)

def constantGauge (k : Site c → G.El) (g : Ratio c f) := k ∘ g.parent

lemma copied (g : Ratio c f) (h : Odd g.count.val) (V : Config G c) (k : Site c → G.El) :
    Lattice.gauge (constantGauge k g) (replica g V)=replica g (Lattice.gauge k V) := by
  funext e; unfold replica Lattice.gauge; split <;> rename_i he
  · simp [constantGauge,he]
  have h' := g.parents_hop h e.1 e.2
  split at h'
  · simp only [constantGauge,Function.comp_apply,if_neg he]; rw [h']
  exact False.elim (he h')

/-- use ℝ Color Product counting basis for derivative. `‖ ‖` induced Pi
sup norm unless explicitly changed, constants depending on dimension can't
be taken pre-L unless shape order receipt.
-/
abbrev AxisChart (G : Gauge) (B : Forest g) := B.Free → G.Color

def represent (b : fieldDir G n 1) : Config G n := RG.increment 1 (collect G b)

def lifting (B : Forest g) (V : Config G c) (a : AxisChart G B) : Config G f := B.drape
    (fun i => G.lieExp (a i) * replica g V i)

@[simp] lemma lifted (B : Forest g) (V : Config G c) : lifting B V 0=replica g V := by
  funext i; by_cases he : i∈B.trunks
  · have hh : replica g V i=1 := if_pos (B.trunk_internal (by simpa using he : (i.1,i.2)∈B.trunks))
    exact Eq.trans (B.on_tree _ ⟨i,he⟩) hh.symm
  have h : lifting B V 0 i=G.lieExp 0 * replica g V i := B.off_tree _ ⟨i,he⟩
  rw [h,G.mat_lieExp_zero,one_mul]

@[simp] lemma link_one : represent (0 : fieldDir G n 1)=1 := by
  funext i; change G.lieExp 0 * _ = (1:G.El); simp
@[simp] lemma replica_one (g : Ratio c f) : replica g (1:Config G c)=1 := by
  funext i; simp [replica]

lemma exp_copy (g : Ratio c f) (b : fieldDir G c 1) : RG.increment 1 (linearCopy g (collect G b)) = replica g (represent b) := by
  funext i; unfold RG.increment replica linearCopy; split <;> simp [RG.increment, represent]

def noiseTaylor (S : StepData c f) (V : Config G c) (U : Config G f) (r : S.Choices) :=
    S.kernel.penalty * ∑ e, G.price (V e * (S.prediction U r e)⁻¹)

def tested (B : Forest S.ratio) (t : S.Choices) (p : Clip) (R : PathData G) (x : fieldDir G c 1) (b : AxisChart G B) :=
    let V := represent x
    let U := lifting B V b
    mainTerm p R U + noiseTaylor S V U t

/-- The germ must stand on the REAL functions on active orientations. If
requiring complex perturbative disks implement extension and prove comparison. -/
def Critical (B : Forest S.ratio) (p : Clip) (R : PathData G) (f : fieldDir G c 1 → AxisChart G B) : Prop :=
    f 0=0 ∧ ContDiffAt ℝ ω f 0 ∧ ∀ t : S.Choices,
      ContDiffAt ℝ ω (Function.uncurry (tested B t p R)) 0 ∧
        ∀ᶠ x in nhds 0, HasFDerivAt (tested B t p R x) (0 : AxisChart G B →L[ℝ] ℝ) (f x)

def relative (B : Forest S.ratio) (W : Matrix (Body 1 f) (Body 1 c) ℝ) (b : fieldDir G c 1) : AxisChart G B :=
    fun x => WithLp.toLp 2 (fun i : G.ColorIndex =>
      (extracted S B W *ᵥ (parts G 1 b i)) (x.val.1, coord x.val.2) - (linearCopy S.ratio (collect G b)) x i)

def Guessed (B : Forest S.ratio) (W : Matrix (Body 1 f) (Body 1 c) ℝ) (ρ : fieldDir G c 1 → AxisChart G B) : Prop :=
    ∀ x : fieldDir G c 1, HasDerivAt (fun t : ℝ => ρ (t • x)) (relative B W x) 0

def PriceGap (B : Forest S.ratio) (p : Clip) (R : PathData G) (η : ℝ) := ∀ r, ∀ v : AxisChart G B,
    η*(∑ i : B.Free, ‖v i‖^2) ≤ iteratedFDeriv ℝ 2 (tested B r p R 0) 0 ![v,v]

/-- across same branch all T. These are pure Taylor matching, not implications
of calculus just because functions are defined. -/
def SameJet {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (j : ℕ) (f h : X → ℝ) :=
    ContDiffAt ℝ ω f 0 ∧ ContDiffAt ℝ ω h 0 ∧ iteratedFDeriv ℝ j f 0=iteratedFDeriv ℝ j h 0

def ClassicalMatch (B : Forest S.ratio) (p q : Clip) (R T : PathData G) (ρ : fieldDir G c 1 → AxisChart G B) := ∀ j, j≤4 → ∀ i : S.Choices,
    SameJet j (fun x => tested B i p R x (ρ x)) (fun x => mainTerm q T (represent x))

end YM.Precision
