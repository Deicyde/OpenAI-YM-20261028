import YM.RG08.Door.Ferry
/-!
# Algebra of predecessor bags. What really costs momentum and current H?
We use an *auxiliary* grade notion (stores out and matrix tickets with each rank).
Then pay triangle deterministically within announced demands. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Door
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels
open scoped BigOperators Topology Real
variable {G:Gauge}{E e r s d τ D j t i k m l n q:ℕ}{R C B A:ℝ}{F:Labels.Frame G d}{H:Hol G}
-- predecessors rectangular, unrestricted slot info at smaller e

def dag (e l r n m q:ℕ) := n < e ∨ (n=e ∧ (m<l ∨ (m=l∧ q>r)))
lemma below (h: awaits 1 e r i j) : dag e l r i l j := by unfold awaits at h; unfold dag; split_ifs at * <;> omega

variable {P:ReadsU F D R}{W U:Session (Letter F)}{b:Letter F}
abbrev realm (W:Session (Letter F))(P:ReadsU F D R)(e r:ℕ)(b k:Letter F) (n:ℕ) := hot W n k b • P k (e-n) r
def palms (W:Session (Letter F))(P:ReadsU F D R)(e r:ℕ)(b: Letter F) := ∑ k:Letter F, ∑ i∈ range (e+1), (if i=0 ∧ slot b=slot k then 0 else realm W P e r b k i)
lemma expose (e r:ℕ)(b:Letter F): bureau P W b e r=∑ k:Letter F,∑ i∈range (e+1),realm W P e r b k i := by
  unfold bureau; rw [edge_marks P _ e e le_rfl,Finset.sum_apply,Finset.sum_apply]; refine sum_congr rfl fun j _=>?_; unfold adapt; rw [Finset.sum_apply,Finset.sum_apply]; apply sum_congr rfl; intro i hi; simp only [Pi.smul_apply,footing (mem_range_succ_iff.mp hi)]; rfl
lemma exposure (e r:ℕ)(b: Letter F): bureau P W b e r= footnote (fun j=> P j e r) (singSl W) b univ + palms W P e r b := by
  rw [expose]; unfold footnote palms; rw [← sum_add_distrib]; apply sum_congr rfl; intro k _
  rw [sum_range_succ',sum_range_succ']; by_cases hx:slot k=slot b <;> simp [singSl,diagonalSl,hx,Ne.symm, realm]; exact add_comm ..
variable {I:Type}{y δ v:I→ℝ}
variable {X V:I→ReadsU F D R}{S:I→Session (Letter F)}

-- lower-l data and Dilation. Real one-model prices A and separate dig ν
lemma slot_zero {X:Session (Letter F)}(hp:Dilation X)(b i:Letter F)(he:slot b+n < slot i): hot X n i b=0 := not_ne_iff.mp (fun H=> (Nat.not_le.mpr he) (hp.stairs n i b H)) -- remove quotes
lemma ferns (h : Audience y)(b:Letter F)(hp: ∀ i,Dilation (S i))(hh:∀ i,Boards (X i))(hz:∀ j p i, dag e (slot b) r j (slot p) i → Tin y δ (fun a=>X a p j i) v)
    (ht: ∀ j i, (dag e (slot b) r j (slot b) (slot i) ∨ (j=e∧ slot i=r)) → Dig y 1 (fun a=> hot (S a) j i b)) : Tin y δ (fun i=>palms (S i) (X i) e r b) v := by -- use dslot
  unfold palms; refine Tin.additions univ (f:=fun k i=>∑ j∈range (e+1),_) h (fun k _=> Tin.additions (range (e+1)) (f:=fun (j:ℕ) (i:I)=> if j=0 ∧ slot b=slot k then 0 else realm (S i) (X i) e r b k j) h fun j hj=>?_)
  split
  · exact Tin.zero
  next hu=>
    have hhj:=mem_range_succ_iff.mp hj; by_cases hk:r≤slot k+ (e-j)
    swap; · simp only [realm,fun a=> show X a k (e-j) r=0 from not_ne_iff.mp (mt (((hh a).rank k).cap (e-j) r) hk), smul_zero]; exact Tin.zero
    by_cases hm:slot k≤ slot b+j
    swap; · simp_rw [realm, fun a=> slot_zero (n:=j) (hp a) b k (by omega),zero_smul]; exact Tin.zero
    refine Tin.scale (hz (e-j) k r ?_) (ht j k ?_).rates
    all_goals unfold dag; omega

lemma views (he: Audience y)(b:Letter F)(hx:∀ i,Boards (X i))(hv: ∀ k≤e,∀ i,∀ j,Tin y 1 (fun a=>X a i k j) v)
    (ht: ∀ j i, (dag e (slot b) r j (slot b) (slot i) ∨ (j=e∧ slot i=r)) → Dig y δ (fun a=> hot (S a) j i b)): Tin y δ (fun i=> bureau (X i) (S i) b e r) v := by
  simp_rw [expose]
  refine Tin.additions univ (f:=fun k i=>∑ j∈range _,_) he (fun k _=> Tin.additions _ (f:=fun j i=> realm (S i) (X i) e r b k j) he fun j hj=>?_)
  have hhj:= mem_range_succ_iff.mp hj
  by_cases hh:r≤slot k+(e-j)
  swap; · simp only [realm,fun a=> show X a k (e-j) r=0 from not_ne_iff.mp (mt (((hx a).rank k).cap (e-j) r) hh),smul_zero]; exact Tin.zero
  exact dig_scale (hv (e-j) (by omega) k r) (ht j k (by unfold dag; omega))
end YM.RG08.Door
