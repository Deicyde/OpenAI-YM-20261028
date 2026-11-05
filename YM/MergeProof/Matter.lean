import YM.MergeProof.Biscuit
import YM.MergeProof.Straw

/-! Costs of Ward second section. schedule floor prospects. one real oriented equiv average. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Guard Local Next.Rank Edition Spindle Extra.Multi Motion
open PhysicalNext.Repeat.Legato.Bandage Cells Extraction Extraction.Lease Exponential Bid Next.Extract RelayDifference Opening
open Labels
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}(H:C.Makes)(B:Stock.Tabs C.path.levels){W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{ζ:ℕ→ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
    (h:Scrim C W u ψ φ δ ζ r D){f:Extraction.Order}
set_option quotPrecheck false
variable {N p d:ℕ}
-- sup refinement β^powers fixed
variable (V:SectionData (C.labels.level d)) (hV:V.Sound C.params)
-- b.Sent.V growth. label basis. moment b.B visit.

def storms (X Y : ℝ) (C:Family G) (N j):=X*Opening.seats C j N+ 2*Y*Opening.seats C j N
-- env b for basis. kappa*bad goes to zero by Delays even without ratio => budget can <=2 eventually independent of A (factor outsupport exp(A)).
lemma sanded (hG:G.Simple) (C:Family G)(d:ℕ)(x y:ℝ)(hu:0 ≤ x)(hv:0 ≤ y): ∀ᶠ i:ℕ in atTop,Real.sqrt (C.path.levels.clock.forcedAllowance i)* storms x y C i d≤1:=by
    let F:= C.labels.level d; let a:= x+2*y; let k:= Extra.Multi.BasisCost.slots F; let b(i:ℕ):=C.path.levels.clock.hatBeta i; let c:ℝ:= Fintype.card F.Index; have hw:0 ≤ a:=add_nonneg hu (mul_nonneg zero_le_two hv)
    filter_upwards [(wearBeta hG C.path.levels).eventually_ge_atTop (a*c),(wearBeta hG C.path.levels).eventually (Doors.stain_beats (k+1))] with i ht he
    let d':=b i; let f:=Real.sqrt (Doors.stain d'); have hd:1≤ d':=(C.path.levels.fits.delayed _).le
    let d₀:= C.path.levels.clock.threshold i; have hp:0 ≤ d₀⁻¹:=inv_nonneg.mpr (C.path.levels.budget i).threshold_pos.le; have hy:d₀⁻¹ ≤ d':= Doors.temp_cheap hd
    have hz:Opening.seats C d i ≤ c*d'^k:= (le_trans (Finset.sum_le_sum (s:=Finset.univ (α:=F.Index)) (g:=fun i=> d'^k) fun j _=> ((pow_le_pow_left₀ hp hy _).trans (pow_le_pow_right₀ hd (Finset.le_sup (f:=fun i=> (F.grades i).2) (Finset.mem_univ j))))) (le_of_eq (by simp [c])) )
    change f*_≤_; refine le_trans (mul_le_mul_of_nonneg_left ((show storms x y C i d = a * Opening.seats C d i by unfold a storms; ring).le) (Real.sqrt_nonneg _)) ?_ -- tactic syntax
    apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hz hw) (Real.sqrt_nonneg _))
    apply le_trans _ he
    rw [← mul_assoc a, pow_succ]; rw [mul_comm (b i ^ k) (b i)]; gcongr
-- setup.A posterior bound.p mark top.
def sphere (s:Stage) (p:ℕ) (b:ℝ) := 2 + Real.exp (81*s.supportExponent)* (b+s.columns+2*(p:ℝ))
-- positive practical gate
lemma sphere_pos (s:Stage)(p) {b}(h:0 ≤ b): 0 < sphere s p b:= add_pos_of_pos_of_nonneg zero_lt_two (mul_nonneg (Real.exp_pos _).le (add_nonneg (add_nonneg h (zero_le_one.trans s.columns_ge)) (mul_nonneg zero_le_two (Nat.cast_nonneg _))))
variable (hG:G.Simple)
end YM.MergeProof
