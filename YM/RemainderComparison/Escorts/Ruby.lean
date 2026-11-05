import YM.RemainderComparison.Escorts.Leg
import YM.RemainderComparison.Sleet.Density
/-! # Paid costumes, single K rents and sum of MARK rentals at actual masks.
    Registration after readdress. Expense *before* tag factors.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Escorts
open Function Filter Finset Lattice Wilson RG Ovens Ovens.Pipes MeasureTheory Push Push.AbsoluteSums PhysicalNext.Repeat
open Merge Mosaic Mosaic.Verse Marker Jolt Flues Placement Progress.DirectedRecipe Animals
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{c:Side}{α:Type*}{I:Type} [Countable I]{q e:ℕ}{A:ℝ}
variable (T:I→Tile G α q e A) (a:α) (p:BudgetPoint)(o:I→Site c)
local notation "S" => tinge T p o
local notation "u"=> (Set.univ:Set I)
local notation "ρ"=> fun i:I=> neighbors e (o i)
local notation "ε"=> Escorts.jet o

def stipend (A:ℝ)(q:ℕ) (o:I→Site c): ℕ→ ℝ:= stuff (Escorts.jet o) fun _=>A*2^q
local notation "w"=> stipend A q o
variable (hA:0≤ A)
include hA
lemma stipulation (i:ℕ) : 0 ≤ stipend A q o i:= Rack.positive ε _ (fun _=>mul_nonneg hA (by positivity)) _
lemma bestowed i : 0 ≤ w i ∧∀ j:α,∀ U, ‖Scone.glow S j i U‖≤w i∧ ‖Scone.tinct S u j i U‖ ≤ w i:=by
    have hz:= Escorts.stipulation (q:=q) o hA i
    by_cases he:i∈ Set.range ε
    · obtain ⟨i,rfl⟩:=he; refine ⟨hz,fun b U=> ?_⟩
      have hp:Scone.tinct S u b (ε i) U=(S).glow b (ε i) U:= if_neg (show Verse.load u _≠0 from Escorts.ascends _ _ _ _)
      rw [hp,and_self,leaking]; unfold leak; by_cases h: Healthy p.threshold (ρ i) U
      · rw [masked_eq _ _ _ _ h,sub_self,norm_zero]; exact hz
      rw [masked_ne _ _ _ _ h,sub_zero]; unfold Tile.read; rw [Real.norm_eq_abs,stipend,stuffed]
      exact ((T i|>.stamp b).unmasked_bound ..).trans (mul_le_mul_of_nonneg_right ((T i).bound b) (by positivity))
    refine ⟨hz,fun b U=>?_⟩
    have hp : (S).glow b i U=0:= congr_fun (show (S).glow b i=0 from Progress.DirectedRecipe.blank _ _ he) _; rw [(S).ashes u hp,hp,norm_zero]; exact ⟨hz,hz⟩
omit hA
variable [Fintype I]
-- Fintype-induced Countable diamond.Prop irrelevance.
omit [Countable I] in
def blanket := Finset.univ.biUnion (fun i=>neighbors e (o i))
set_option quotPrecheck false
local notation "B" => blanket (e:=e) o
lemma banner {i:ℕ}(hp:(stipend A q o i)≠0) : (S).leg i⊆ B:=by
    by_cases h:i∈Set.range ε
    · obtain ⟨i,rfl⟩:=h; rw [(axle T p o i).1]; exact subset_biUnion_of_mem (ρ) (Finset.mem_univ i)
    exact (hp (Progress.DirectedRecipe.blank _ _ h)).elim
omit [Countable I] in
lemma blanket_size : (B).card ≤ Fintype.card I* Animals.ballCost e:=by
   unfold blanket; refine card_biUnion_le.trans ?_; simpa using (sum_le_sum (s:=Finset.univ) fun (i:I) _=> Animals.neighbors_card e (o i))
-- d.F.LE.P fraction * ψ integrated explicit.There is no factor p.supportExponent prospective larger. Heading stock sells all.Meta.Prop.Rates fields α.

def residualK (E:ℝ) (A:ℝ)(q n:ℕ) := (n:ℝ)* (Real.exp E * (A*2^q))
include hA
variable (hb:e≤p.B)
include hb
lemma federal : SumBudget (fun i=>p.mass ((S).leg i) (stipend A q o i)) (residualK p.supportExponent A q (Fintype.card I)):=by
    refine Local.sumBudget_pass ε _ (budget_finite (fun i=>mul_nonneg (Real.exp_nonneg _) (stipulation o hA _)) ?_) ?_
    · unfold residualK; refine le_trans (sum_le_sum (g:=fun _=> Real.exp p.supportExponent*(A*2^q)) (fun i _=>?_)) (le_of_eq (by simp))
      rw [(axle T p o i).1,stipend,stuffed]; unfold BudgetPoint.mass
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hA (by positivity)); apply Real.exp_monotone; apply mul_le_of_le_one_right p.exponent_pos.le; exact_mod_cast Sleet.cap_one _ (o i) p.B (fun j hj=> Tile.position hb hj)
    intro i he; rw [show w i=0 from Progress.DirectedRecipe.blank _ _ he,BudgetPoint.mass,mul_zero]
local notation "P₁" => residualK p.supportExponent A q (Fintype.card I)
lemma purchased (k:ℕ): Scone.Treasures S u k p.B p.supportExponent 0 P₁:=by
    refine ⟨0,w,fun _=>le_rfl,stipulation o hA,fun i=>?_,fun i=> ?_,fun i _ j V=> ?_⟩
    ·
      simp [SumBudget]
    · refine budget_mono (Escorts.federal T p o hA hb) (fun j=>?_) (fun j=>?_)
      · split; next=> apply mul_nonneg (stipulation o hA _) (Real.exp_pos _).le
        exact le_rfl
      split; next=> exact le_of_eq (mul_comm ..)
      exact (federal T p o hA hb).1 _
    split; next he => rw [chalk T p o i (show Jolt.dawn S u i from he) j]; simp
    next=> exact (bestowed T p o hA i|>.2 j V).1
omit hA hb
open Lacuna Ethereal
end YM.RemainderComparison.Escorts
