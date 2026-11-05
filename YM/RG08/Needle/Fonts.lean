import YM.RG08.Needle.Sites
/-!
# Recurring normalized full graph. One row per qualified joint letter
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Needle
open RG Laurent Lattice Wilson Bloch Exterior Precision Push.AbsoluteSums Finset Function Filter Matrix Work.F08 Next.Free
open UVExt.Paths Stationary Planned.PrimaryIntegral295 Place Shade Quire Source Source.Drops Labels Scores Scores.Pages Tall Vale Reflect Staffer Loom PowerSeries
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {I:Type} [Fintype I] {G:Gauge} {L c f p: Side}{w R A B:ℝ}{D d e j r n i k t:ℕ}{τ:ℕ}{F:Labels.Frame G d}
variable {T:Session (Letter F)} {A':Session I} {b : Letter F} {V U : BoardU D R G}
variable (P:Hol G)
abbrev ReadsU (F:Labels.Frame G d)(D:ℕ)(R:ℝ) := Letter F→BoardU D R G

def call (F:Labels.Frame G d)(V:BoardU D R G) : Native (Letter F) := fun b=> PowerSeries.mk fun j=> auditT P F V j b
def atlas (φ:ReadsU F D R) : Session (Letter F) := Matrix.of fun x y=> call P F (φ y) x
lemma atlas_fees (φ: ReadsU F D R)(v:Letter F)(u:Letter F) (i:ℕ): hot (atlas P φ) i v u= auditT P F (φ u) i v := by unfold hot atlas call; rw [Matrix.map_apply,Matrix.of_apply,coeff_mk]
structure Boards (φ:ReadsU F D R): Prop where
  rank (b:Letter F): Marvel (slot b) (φ b)
  paid (b:Letter F): Lank (φ b)
variable {φ: ReadsU F D R} {Q: Hol G} {X: SectionData F}
structure Genuine (p:Hol G)(φ:ReadsU F D R): Prop extends Boards φ where
  cost: atlas p φ=1
lemma atlas_points {φ:ReadsU F D R} (h:Genuine P φ)(v b:Letter F)(i:ℕ): auditT P F (φ v) i b= if i=0 ∧ b=v then 1 else 0 := by
  rw [← atlas_fees,h.cost,hot_one]; split_ifs with hx hy <;> simp [*,Matrix.one_apply] <;> tauto
lemma across_b (h:∀ p:ℕ,∃ W:BoardU D R G,Same V W p ∧ Marvel τ W) : Marvel τ V := by
  choose W H hp using h
  refine ⟨fun i r hx=> (hp i).cap i r (by rw [← H i i le_rfl]; exact hx),fun i r=> by rw [H i i le_rfl]; exact (hp i).hem i r,fun m φ i v w hv hw hg k=> ?_⟩
  let f V e:= large i (τ+e) (fun r=> plug φ R ∘ (V:BoardU D R G) e r)
  have hz p: arco m (f V) p k=arco m (f (W k)) p k:= by unfold arco Reflect.year; funext x; refine Finset.sum_congr rfl fun a ha=> ?_; unfold f; dsimp only; rw [H _ _ (mem_range_succ_iff.mp ha)]
  change Fit _ (arco m (f V) v k) (arco m (f V) w k); rw [hz,hz]; exact (hp k).wardrobe _ _ _ v w hv hw hg k
lemma stays (h:Boards φ)(ht:Dilation T): Boards (bureau φ T) := by
  refine ⟨fun b=> ?_,fun b=> ?_⟩
  · refine across_b (fun i=> ⟨_,edge_marks φ _ i,choir_array univ ?_⟩); intro a _
    refine choir_array (U:=fun j=> coeff j (T a b) • fem j (φ a)) (range _) ?_; intro j _
    by_cases he:hot T j a b=0
    · rw [show coeff j (T a b)=0 from he, zero_smul]; exact choir_none
    apply choir_weight
    apply stemmed (h.rank a)
    exact ht.stairs j a b he
  intro e r; unfold bureau; rw [edge_marks φ _ e e le_rfl]; exact (lank_tbl fun i _=>lank_tbl (X:=fun j=> coeff j (T i b) • fem j (φ i)) fun j _=> lank_wt (lank_fee (h.paid i) _) _) e r -- fix args
lemma tells (h: Boards φ) (M: Session (Letter F)) : atlas P (bureau φ M)=atlas P φ*M := by
  ext i j a; unfold atlas call bureau; rw [Matrix.mul_apply]; apply congr_arg (coeff a); simp only [Matrix.of_apply]
  rw [audit_funds P d _ φ (fun b=> wider (h.rank b) (slot_le b)) h.paid]; simp_rw [mul_comm (M _ _)]
lemma section_genuine (X:SectionData F)(hP:X.Sound P)(hB:Bid.pop X)(h:d≤D)(hp:1/2≤R):
    Genuine P (fun i:Letter F => startU X i h ((by norm_num : (0:ℝ)≤1/2).trans hp)) := by
  refine ⟨⟨fun i=>start_duty X i h _ hB P hP,fun i=>?_⟩,?_⟩
  · exact start_lank X i _ _
  let Q:ℝ:=R; let hv:0≤R:=(by norm_num:(0:ℝ)≤1/2).trans hp; let S:ReadsU F D R := fun i => startU X i h hv
  change atlas P S=1
  ext i j k; change hot (atlas P S) k i j = hot (1:Session (Letter F)) k i j; rw [atlas_fees, show auditT P F (S j) k i=_ from outfit X j P hP hB h hv _ _,hot_one]; split_ifs <;> simp_all [Matrix.one_apply]
lemma abstractMinor (h:Genuine P φ)(hP:X.Sound P)(hp: Bid.pop X)(hv:d≤D)(hx:1/2≤R) :
    let S := fun i:Letter F=> startU X i hv ((by norm_num : (0:ℝ)≤1/2).trans hx); let Y:=φ-S;
    Boards Y ∧ ∀ b,auditT P F (Y b)=0 := by
  intro S Y; have ht:=show Genuine P S from section_genuine P X hP hp hv hx
  constructor
  · refine ⟨fun b=>?_,fun b=>?_⟩
    · unfold Y; rw [Pi.sub_apply,sub_eq_add_neg,← neg_one_smul ℝ]; exact choir_plus (h.rank _) (choir_weight (ht.rank _) _)
    unfold Y; rw [Pi.sub_apply,sub_eq_add_neg,← neg_one_smul ℝ]; exact lank_add (h.paid _) (lank_wt (ht.paid _) _)
  intro i; ext j a; unfold Y; rw [Pi.sub_apply,audit_sub P (h.rank i) (ht.rank i) (h.paid i) (ht.paid i),Pi.sub_apply,Pi.sub_apply,atlas_points P h,atlas_points P ht]; exact sub_self _
end YM.RG08.Needle
