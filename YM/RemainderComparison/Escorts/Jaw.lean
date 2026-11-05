import YM.RemainderComparison.Escorts.Ruby
/-! # Joint ticket type before anomaly boost and pointer pledge. -/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Escorts
open Function Filter Finset Lattice Wilson RG Ovens Ovens.Pipes MeasureTheory Push Push.AbsoluteSums PhysicalNext.Repeat
open Merge Mosaic Mosaic.Verse Marker Jolt Flues Placement Progress.DirectedRecipe Animals Ethereal Lacuna
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{c:Side}{α:Type*}{I:Type} [Fintype I]{q e:ℕ}{A:ℝ}
variable (R:Rep G c) (T:I→Tile G α q e A) (a:α) (o:I→Site c)
local notation "A₀"=> R.activities
local notation "p"=> R.p
local notation "H"=> silver R I α
local notation "S" => tinge T p o
local notation "u"=> (Set.univ:Set I)
local notation "ρ"=> fun i:I=> neighbors e (o i)
local notation "C"=> fireplace H S
local notation "w"=> stipend A q o
local notation "ε"=> Escorts.jet o
variable (F:ℕ≃ (fireplace (Escorts.silver R I α) (tinge T R.p o)).Pellet)
set_option quotPrecheck false
local notation "D"=> Flues.flash H S p u F
local notation "B"=> Fintype.card I
variable {K δ x:ℝ}
-- Mark charge table.Power uses exact input budget exponent. pay for fixed α manifold HEADING after normalization.
-- enumeration for ACT.Live moving.
abbrev Markers (R:Rep G c)(T:I→Tile G α q e A)(o:I→Site c)(F:ℕ≃ (fireplace (Escorts.silver R I α) (tinge T R.p o)).Pellet):= {i:ℕ// ¬Jolt.phase (Flues.flash (silver R I α) (tinge T R.p o) R.p (Set.univ:Set I) F) Set.univ i}
local notation "Ω"=> Escorts.Markers R T o F

def extensionBill (E:ℝ)(A:ℝ)(q n e:ℕ)(K:ℝ):= (Real.exp (((n*Animals.ballCost e:ℕ):ℝ)*K)-1)*(Real.exp (Escorts.residualK E A q n)-1)
local notation "Bʼ" => extensionBill R.p.supportExponent A q B e

variable (hA:0≤ A)
include hA
variable (hb:e≤ R.p.B) (hk:R.activities.KBound R.p K)
omit hA in
lemma progress (i:Ω) : (F i.val).val.toRight.Nonempty:=by
    by_contra he; apply i.prop; apply (Jolt.stars ..).2; intro j hj; rcases j with j|j
    · change Verse.load u 0=0; simp [Verse.load]
    exact (he ⟨j,mem_toRight.mpr hj⟩).elim
structure Shapes (X₀:ℝ): Prop where
   earnings : ∃ b: (Ω)→ℝ, (∀ i,0 ≤ b i)∧ SumBudget (fun i=>(p).mass ((D).plane i.val) (b i)) X₀ ∧ (∀ i a V, ‖(D).glow a i.val V‖≤ b i) ∧
                  ∀ i,0<b i→ (D).score i.val ≠0 ∧ ∀ j∈(D).score i.val, neighbors e (o j) ⊆ (D).plane i.val
include hb hk
lemma proceeds : Escorts.Shapes R T o F (Bʼ K):=by
   obtain ⟨f,hf,hK⟩:= hk; let g (i:ℕ):= (∏ j∈(F i).val.toLeft,f j)*(∏ j∈(F i).val.toRight,w j)
   have hw i: 0 ≤ w i:= Escorts.stipulation o hA i -- lint
   have hp i:0 ≤ g i:= mul_nonneg (prod_nonneg fun _ _=> (hf _).1) (prod_nonneg fun _ _=>hw _)
   refine ⟨fun i=>g i.val,fun i=> hp _,?_,fun i a V=>?_ , fun i hi=>?_⟩
   · let X:= Escorts.blanket (e:=e) o; have hz:=(federal T p o hA hb)
     have hh:= Escorts.tabulated F f w p X (fun i=> (hf _).1) hw hK hz (fun _ he=> Escorts.banner T p o he)
     have h:= budget_pull (fun i:Ω=> i.val) Subtype.val_injective hh
     have he : 0 ≤ K:= budget_nonneg (hK 0)
     have hKp : (X.card:ℝ) ≤ ((B*Animals.ballCost e:ℕ):ℝ):= by exact_mod_cast (Escorts.blanket_size (e:=e) o)
     refine budget_loosen ?_ (mul_le_mul_of_nonneg_right (sub_le_sub_right (Real.exp_monotone (mul_le_mul_of_nonneg_right hKp he)) 1) (sub_nonneg.mpr (Real.one_le_exp (budget_nonneg hz))))
     convert h using 1; ext i; exact Eq.symm (congr_arg ((p).mass ((D).plane i.val)) (if_pos (Escorts.progress R T o F i))) -- linter
   · unfold Flues.flash; dsimp only; split; next he =>
       rw [norm_prod,Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight]; exact mul_le_mul (Finset.prod_le_prod (fun _ _=> norm_nonneg _) (fun j _=> (hf j).2 _)) (Finset.prod_le_prod (fun _ _=> norm_nonneg _) (fun j _=> (bestowed T p o hA j|>.2 a V).2)) (prod_nonneg fun _ _=> norm_nonneg _) (prod_nonneg fun _ _=> (hf _).1)
     next=> rw [norm_zero]; exact hp _
   refine ⟨fun hz=>i.prop (show Verse.load u ((D).score _)=0 from by rw [hz]; simp [Verse.load]),fun j hj=>?_⟩
   obtain ⟨k,hk,hk'⟩:= (Mosaic.holds _ (Flues.rune H S) j).mp hj; rcases k with k|k
   · exact (Multiset.notMem_zero _ hk').elim
   have he : w k≠0:= fun he=> ne_of_gt hi (by unfold g; change _ * (∏ j∈(F i.val).val.toRight, w j)=0; rw [Finset.prod_eq_zero (Finset.mem_toRight.mpr hk) he, mul_zero])
   have hz : k∈Set.range ε:= Classical.byContradiction fun hz=>he (Progress.DirectedRecipe.blank _ _ hz)
   obtain ⟨k,rfl⟩:=hz; change j∈ (S).glyph (ε k) at hk'; rw [(axle ..).2,Multiset.mem_singleton] at hk'; subst k
   rw [← show (C).patch (.inr (ε j))= neighbors e (o j) from (axle T p o j).1]; exact subset_biUnion_of_mem _ hk
omit hk hb hA

omit [Fintype I] in
lemma anchored (h:R.activities.KBound R.p K) (k:ℕ) : Yard.Pays H u k (p).B (p).supportExponent K:=by
   obtain ⟨f,hf,hB⟩:=h; refine ⟨f,fun i=> (hf i).1,fun x=>?_,fun i _ a V=>(hf i).2 _⟩
   convert hB x using 2 with j; unfold BudgetPoint.mass Yard.plane silver; dsimp only; change (if x∈(R.activities.forced j).support then _ else _) = _; split<;> ring

end YM.RemainderComparison.Escorts
