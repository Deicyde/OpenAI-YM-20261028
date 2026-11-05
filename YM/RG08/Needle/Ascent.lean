import YM.RG08.Needle.Soak
/-!
# Physical Chain independent formal one-mark recursion
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
open UVExt.Paths Stationary Planned.PrimaryIntegral295 Place Shade Quire Source Source.Drops Labels Scores Scores.Pages Tall Vale Reflect Staffer Loom PowerSeries Conductor
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G:Gauge} {L c f p: Side}{w R A B:ℝ}{D d e j r n i k t:ℕ}{τ:ℕ}{F:Labels.Frame G d}
-- include also for X without K trajectory-admission if transition data qualify on announced wing
variable (X: Chain)(ν:G.ColorIndex)(T:ChartRatio G)
def dance (N m : ℕ) : StripU G (X.S.block m) where
    cv:= Chain.curve G X N m
    tree:=Chain.predict G X N m
    song:= awakening ν (X.patch m) T X.kernel.penalty (X.album ν T N (m+1))
    scale:= Conductor.afternoons (Conductor.rootsRatio X ν T N (m+1) m)
lemma fairground (h:X.Wake G)(ht: LocalRatio T){m':ℕ}(he:m'<n) : Fair (dance X ν T n m') := by -- implicit m'
  have hC:=show Whole (Chain.curve G X n m') from (conditional_truth G (X.trees m') X.kernel (X.history n (m'+1)) (h m')).1
  have hm: Whole (Chain.predict G X n m') := (hC.prod ((probe_recites G (X.patch m') X.kernel).1.flipped)).weight _
  have he':= X.packing ν T h ht he
  have hp:= Gets_awake (X.patch m') T X.kernel ν he'.gets
  refine ⟨X.S.block_odd _,hC,hm,fun i j=> (hp.2 i j).1,fun i j=>(hp.2 i j).2,hp.1, ?_,?_⟩
  · unfold dance; simp only [afternoons]; simp [mat_zero]
  intro D R d τ V hr hM
  exact marvelled hM (h m') he'.gets hr (B:=X.metric n m') ⟨X.metric_whole ..,fun i=>X.metric_sym ..,fun i f h=> ⟨_,X.canonical n m' he h⟩⟩ he'.halt he'.opens ht ν (X.trees m') d
lemma demandPrint (K : KPrices X.kernel) (h:X.Wake G)(ht:LocalRatio T)(N m:ℕ)(he:m<N) : ∃ Z:Cross (X.flight N m).L (Candles G) (Loc G 1),
    Whole Z ∧ Speaks (painted G (Carrier.linesOf (X.flight N m) X.kernel.penalty)) Z (dance X ν T N m).tree := by
  obtain ⟨p,hp,hP⟩:=earn G X N m h he K; exact ⟨_,⟨_,_,K.positive _,hp⟩,hP⟩
variable (H:Hol G)(S:SectionData F) (hp:d≤D) (hR:1/2≤R)
-- No tests/orders optimized per cut. Joint orientation.

def stepboard (N m :ℕ) : ReadsU F D R:= if m<N then repose H (dance X ν T N m) (stepboard N (m+1)) else fun i: Letter F=> startU S i hp ((by norm_num : (0:ℝ)≤1/2).trans hR)
termination_by N-m
def dice (N m : ℕ) : Session (Letter F) := mapU H (dance X ν T N m) (stepboard X ν T H S hp hR N (m+1))
local notation "Φ" => stepboard X ν T H S hp hR
lemma step_top (N:ℕ): Φ N N=fun i : Letter F=> startU S i hp ((by norm_num:(0:ℝ)≤1/2).trans hR) := by rw [stepboard, if_neg (Nat.lt_irrefl _)]
lemma decks (K : KPrices X.kernel) (h:X.Wake G)(ht:LocalRatio T)(hs:S.Sound H)(hm:Bid.pop S)(N m : ℕ)(he:m≤N)(hB:d≤ X.J m): Genuine H (Φ N m) := by
  induction he using Nat.decreasingInduction with
  | self=> rw [step_top]; exact section_genuine H S hs hm hp hR
  | of_succ m he ih=>
    let Q:= X.flight N m
    have hZ:= fairground X ν T h ht he
    have hf: d≤ X.J (m+1):= hB.trans (X.mono m); have hu:= ih hf
    have hv:= issued H Q X.kernel.penalty X.kernel.penalty_pos (X.adm m) hf hZ hR hs hm hp (demandPrint X ν T K h ht N m he) hu
    rw [stepboard, if_pos he]; exact (fountain H hZ hR hu.toBoards hv).1
lemma dice_step (K: KPrices X.kernel) (h:X.Wake G)(ht:LocalRatio T)(hs:S.Sound H)(hm: Bid.pop S)(N m:ℕ)(he:m<N)(hB:d ≤ X.J (m+1)): let f:=Φ N (m+1);
    let v:=dice X ν T H S hp hR N m; Flash (X.S.block m) v ∧ uprise (dance X ν T N m) f=bureau (Φ N m) v := by
  intro f v; have hh:= fairground X ν T h ht he; have hx:=decks X ν T H S hp hR K h ht hs hm N (m+1) he hB
  have hy:=issued H (X.flight N m) X.kernel.penalty X.kernel.penalty_pos (X.adm _) hB hh hR hs hm hp (demandPrint X ν T K h ht N m he) hx
  refine ⟨hy,?_⟩; rw [stepboard, if_pos he]; exact (fountain H hh hR hx.toBoards hy).2
end YM.RG08.Needle
