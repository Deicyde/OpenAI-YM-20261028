import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Hop
import YM.Next.BOUNDARY.Decomposition
import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Reading

/-!
# Inputs to spatial-width growth (same window data at x)
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.WeightedGaussianMarginal45C.Venue
open AnalyticBridge.LocalGaussianLaws
open Filter Function Lattice RG RG.Patch Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Matrix
open Next.Fluctuations Next.SectorChange Motion Rows Push.SectorMeasure Presented Pressure.Stores Gaussian Tree Wisps Bid
open Assembly Current FreeResolvent Remote Lift Extra.Iteration.Scales MeasureTheory Local
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f}

/-- Additional spatial width at this standing x, chosen before x.
NOT an edit to the cut stencils or temperature x or gauges; additional
clearance/size assumptions at use. Log-size price with `clearanceFare`
still taken at x; multiplication by Tier cost is inside new post-L R. -/
def vista (tier : ℕ) (x : ℝ) := match tier with
  | 0 => radiusB x
  | k+1 => (k+2) * radiusB x
lemma vista_zero (x : ℝ) : vista 0 x=radiusB x := rfl
lemma vista_eq (k : ℕ) (x : ℝ) : vista k x=(k+1)*radiusB x := by cases k <;> simp [vista]
lemma vista_large (k : ℕ) (x : ℝ) : radiusB x ≤ vista k x := by rw [vista_eq]; exact Nat.le_mul_of_pos_left _ (k.succ_pos)

def Board (tier : ℕ) (x R : ℝ) {S : StepData c f} (A : Stores S) (T : Tube G S) (H : Bed) (o : Site c) (V : Config G c)
    (F : Forest S.ratio) (z : Site c → G.El) (v : Dir G c) : Prop :=
    (AgreeNear id o (vista tier x) (Lattice.gauge z V) (represent v) ∧ ‖v‖ ≤ R*clearanceFare x) ∧
    let J:= treeInverse G S F H.metric 0; let b := Local.portrait_head T F v
    J.PosDef ∧ ∀ (k : S.Choices) (q : Chi) (d : ℝ) (g : Assembly.Geometry) (Y : LinkArray G (Frozen A x F)),
      let a:=Local.portrait T A F k x (Lattice.gauge z V) g q d Y
      let Q:=Local.palette T A F k x (Lattice.gauge z V) g
      Q.PosDef ∧ ∀ (m : Type) [Fintype m] [DecidableEq m] (e : m ↪ In x A F (G:=G)), Local.lives m F A o (vista tier x/4) e →
        ∀ β : ℝ, 0<β → β ≤ 3*x →
        let g:=coupling β; let N : ℝ:=Fintype.card m; let P:=x^(1/128:ℝ)
        let l:= e.trans (loadLink A F x)
        let D:= Q.submatrix e e; let B:= J.submatrix l l
        let u:=g⁻¹ • (b ∘ l - a ∘ e)
        (∀ y, |Real.log (Density.replace D B u y)| ≤ x^(-(1/8):ℝ)*(P*N*(1+1^2)+(P^2+P)*Density.energy y)) ∧
        ∀ (L : (m→ℝ)→ℝ) (C : ℝ), Measurable L → (∀ y, |L y|≤C) →
          let X:=∫ z,L ((a+g • z)∘e)∂cloud Q
          X = (∫ z,Density.replace D B u z * L (b ∘ l+g • z)∂cloud B) ∧
            |X-(∫ z,L ((b+g • z)∘l)∂cloud J)| ≤ C*x^(-(1/16):ℝ)

def Account (tier : ℕ) (K D : ℕ) (E x : ℝ) (A : Stores S) (T : Tube G S) (H : Bed) (o : Site c) (V : Config G c)
    (F : Forest S.ratio) (z : Site c → G.El) (v : Dir G c) : Prop :=
    let J := treeInverse G S F H.metric 0; let b := Local.portrait_head T F v
    ∀ (k : S.Choices) (q : Chi) (d : ℝ) (s : Assembly.Geometry) (Y : LinkArray G (Frozen A x F)),
      let a := Local.portrait T A F k x (Lattice.gauge z V) s q d Y
      let Q := Local.palette T A F k x (Lattice.gauge z V) s
      ∀ (I : Type) [Fintype I] [DecidableEq I] (e : I ↪ In x A F (G:=G)), Local.lives I F A o (vista tier x/4) e →
        Fintype.card I ≤ K → ∀ β : ℝ, 0 < β → β ≤ 3*x →
        Readout K D E x Q J a b (coupling β) e (e.trans (loadLink A F x))







section reduce
variable {ti K D : ℕ} {E x R : ℝ} {A : Stores S} {T : Tube G S} {H : Bed} {o : Site c} {V : Config G c}
    {F : Forest S.ratio} {z : Site c → G.El} {v : Dir G c}


end reduce
end YM.PhysicalNext.WeightedGaussianMarginal45C.Venue
