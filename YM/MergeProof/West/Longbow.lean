import YM.MergeProof.West.Cassia
import YM.Next.RANK.Foiling

/-!
# Numbers for a request through regular and tail epochs.
All gates before doing pushes. Use with Supplement (below) NOT asserting
feasibility yet. `Coup.Purse` can retain essentials (use even ShowHours).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes.West
open Function Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Relation Finset Marker
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
open MeasureTheory Cells Edition Filter
variable {G:Gauge}{N n p k q i d D:ℕ} {C:Family G} {R:Lead G C.S p}
   (B:Purse) (s:ℝ)
def cashFt (u:ℕ):= (1:ℝ)/(8*u)-B.era.coast.U
def loot (u:ℕ):= bill (cashFt B u) s
def rentFt (n:ℕ) := B.principal s ^ n* knox s
-- bounds enlarged to cover also raw moments for subsets 'outside'.
def quotaFt (n:ℕ):= rentFt B s n + ∑ i:modes (Fin n), coinRate (yolk (Fin n) i) (rentFt B s n)
def degrFt (n:ℕ) := n*B.taylor + ∑ i:modes (Fin n), lumpD (yolk (Fin n) i)*(n*B.taylor)
lemma deg_cost (T:modes (Fin n)) : lumpD (yolk (Fin n) T)*(n*B.taylor)≤degrFt B n:= (Finset.single_le_sum (fun i _=> Nat.zero_le (lumpD (yolk (Fin n) i)*(n*B.taylor))) (Finset.mem_univ T)).trans (Nat.le_add_left ..)
lemma deg_best (n:ℕ) : n*B.taylor ≤ degrFt B n:= Nat.le_add_right ..
lemma principal_ge : 1≤ B.principal s:= Glimmer.costed _ _ (zero_le_one.trans B.motion)
lemma knock : 1 ≤ knox s:= Glimmer.costed _ _ zero_le_one
lemma rent_buy (n:ℕ):1 ≤ rentFt B s n:= one_le_mul_of_one_le_of_one_le (one_le_pow₀ (principal_ge ..)) (knock _)
lemma quota_ge (n:ℕ) : rentFt B s n ≤ quotaFt B s n:= le_add_of_nonneg_right (sum_nonneg (fun _ _=> massX _ _ (zero_le_one.trans (rent_buy B s n))))
lemma quota_cost (T:modes (Fin n)): coinRate (yolk (Fin n) T) (rentFt B s n) ≤ quotaFt B s n:= by
    let r:= rentFt B s n; exact (Finset.single_le_sum (fun i _=> massX _ _ (zero_le_one.trans (rent_buy B s n))) (Finset.mem_univ T)).trans (le_add_of_nonneg_left (zero_le_one.trans (rent_buy B s n)))

def sheen (n:ℕ):= quotaFt B s n * Common.priced (torque s) (degrFt B n)
def proDue (u n:ℕ):= rentQ B.era.coast.Q (load B.era)*(loot B s u*sheen B s n)
def gym (n:ℕ) := gentility (knox s) (B.sends s) (quotaFt B s n) (degrFt B n) n
def bracelets (n:ℕ):= grater n (sheen B s n + 1) (gym B s n)
def blame (n:ℕ):= grater n (rentFt B s n) (rentFt B s n * knox s * B.sends s)
-- 'Receipt' census by m. omit temporal port here. 
structure Caff (B:Purse) (s:ℝ) (j u n:ℕ) : Prop where
    horizon : 6*n+3 ≤ B.horizon / (3+2*n)
    hikes : hike B.L (n*B.taylor) j ≤ knox s
    flare : 1-(B.goal:ℝ) ≤ -((u:ℝ)*B.era.coast.V)-2
    lit : (↑(2^n:ℕ):ℝ)*proDue B s u n ≤ bill (-4) s
    bytes : gym B s n≤1
    buys : (↑(2^n:ℕ):ℝ)*(rentQ B.era.coast.Q (load B.era)*bracelets B s n) ≤ B.demand s
    pastry : ∀ x:ℝ,x∈Set.Icc (s/2) s→
      let l:= Paint.trib B.era.coast.a x
      Real.exp l*Perch.gas B.era.coast x^2+n*Perch.bill (-2) s*rentQ B.era.coast.Q (load B.era+1) ≤ bill (-1) s
    awaken : Awakening (G:=G) B s n
    hiatus : blame B s n * Common.priced (knox s) (degrFt B n) + defect (knox s) (B.sends s) (quotaFt B s n) (degrFt B n) ≤ bill (-3/2) s
lemma cash_le (u : ℕ) (h : 2≤u): cashFt B u ≤ B.f:=by
    have he := B.hour
    have hf: ((2:ℕ):ℝ) ≤ u:=by exact_mod_cast h
    unfold cashFt; apply le_trans _ he.le; gcongr ?x - _
    push_cast at hf
    apply one_div_le_one_div_of_le (by norm_num : 0<(16:ℝ)); linarith
lemma one_loot (u:ℕ)(h:2≤u): loot B s u≤1:=(Glimmer.billed s (cash_le B u h)).trans (B.cash_le s)
lemma loaf (u:ℕ):0<loot B s u:=Real.exp_pos _
end YM.Next.Rank.Tapes.West
