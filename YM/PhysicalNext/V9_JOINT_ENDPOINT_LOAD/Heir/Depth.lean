import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Museum
import YM.Planned.ATOM_REGULAR_ESTIMATE.Vest

/-! Translate E cover criteria to usable patches. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Lattice Wilson Pressure Precision RG Tree Bloch Exterior
open scoped BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {A : Stores S} {F : Forest S.ratio} {I : Type} {x : ℝ} {X : Support f} {Y : Support c}
  {B : BudgetPoint} {o : Site f} {r : ℕ}

def breadth (B : BudgetPoint) (X : Support f) := coverNumber B.B X * (4*B.B+2)+2*B.B+8
lemma close_enough (ho : o∈X) {p : Site f} (hp : p∈inspected X) : separation p o ≤ breadth B X := by
  obtain ⟨q,hq,he⟩ := Extra.Iteration.Shapes.inspect_dist X hp
  apply (separation_triangle p q o).trans; unfold breadth; have H := Corona.extent X B.B hq ho; omega

def Short (S : StepData c f) (B : BudgetPoint) (X : Support f) := (coverNumber B.B X)^3 < S.patch.L.val
lemma width_le (h : Short S B X) (he : B.B ≤ 2*radiusB x) : breadth B X ≤ 6*(1+radiusB x)*S.patch.L.val := by
  let L := S.patch.L.val; let r := radiusB x; let d := coverNumber B.B X
  have hd : d*3 ≤ L := by
    have hl := S.patch.coarse
    change d^3<L at h; change 3≤L at hl
    rcases show d≤1 ∨ 2≤d by omega with hh|hh; · omega
    have ht : 2^2 ≤ d^2 := Nat.pow_le_pow_left hh 2
    nlinarith only [h,Nat.mul_le_mul_right d ht]
  have hR : L≥2 := le_trans (by norm_num) S.patch.coarse
  unfold breadth; change d*(4*B.B+2)+2*B.B+8 ≤ 6*(1+r)*L
  calc
    _ ≤ d*(8*r+2)+4*r+8 := by gcongr d*?_+?_+8 <;> omega
    _ ≤ _ := by nlinarith only [hd,Nat.mul_le_mul_right (8*r+2) hd, Nat.mul_le_mul_right (4*r+8) hR]
lemma short_patch (h : Short S B X) (he : B.B ≤ 2*radiusB x) (ho : o∈X) {p : Site f} (hp : p∈inspected X) :
    separation (S.ratio.parent p) (S.ratio.parent o) ≤ 6*(1+radiusB x)+1 := by
  apply Nat.le_of_mul_le_mul_left _ S.ratio.count.property
  exact (Corona.foreshorten S.ratio p o).trans ((Nat.add_le_add_right ((close_enough ho hp).trans (width_le h he)) _).trans_eq (by change _ + S.patch.L.val=S.patch.L.val*_; generalize S.patch.L.val=V; ring))
lemma short_nonwrap (h : Short S B X) (he : B.B ≤ 2*radiusB x) (ht : 100*(1+radiusB x) ≤ c.val) (ho : o∈X) : Nonwrapping X o := by
  intro p hp
  apply (Nat.mul_le_mul_left 10 ((close_enough ho (Finset.mem_union_left _ hp)).trans (width_le h he))).trans_lt
  rw [S.sizes]; calc
    _ = 60*(1+radiusB x)*S.patch.L.val := by ring
    _ < _ := Nat.mul_lt_mul_of_pos_right (by omega) S.patch.L.property
lemma roomy (h : 100*(1+radiusB x)≤c.val) : 2*(reach x+1)<c.val := by unfold reach; omega

def Walled (S : StepData c f) (X : Support f) (Y : Support c) (x : ℝ) (r : ℕ) := Y ⊆ halo (r*radiusB x) (X.image S.ratio.parent)
def scope (B : BudgetPoint) (X : Support f) (r : ℕ) (x : ℝ) := r*radiusB x+breadth B X+1
lemma scope_inside (h : Walled S X Y x r) (B : BudgetPoint) (ho : o∈X) (z : Site c) (hz : z∈Y) : separation z (S.ratio.parent o) ≤ scope B X r x := by
  obtain ⟨p,hp,he⟩ := halo_spec.mp (h hz); obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hp
  apply (separation_triangle _ (S.ratio.parent p) _).trans; rw [separation_comm z]; rw [scope,Nat.add_assoc]; apply Nat.add_le_add he
  exact (Work.E04.parent_separation S.ratio p o).trans (Nat.add_le_add_right (close_enough ho (Finset.mem_union_left _ ‹p∈X›)) 1)

def headCount (G : Gauge) (L : Side) (p : ℕ) := (p+p+1)^4 * Fintype.card (Co L (Axis × G.ColorIndex))

namespace Museum
variable (M : Museum F x A X Y I) [Fintype I]
include M
lemma viewed (h : Walled S X Y x r) (B : BudgetPoint) (ho : o∈X) (G : Gauge) : Fintype.card (I×G.ColorIndex) ≤ headCount G S.patch.L (scope B X r x) := by
  let U := halo (scope B X r x) ({S.ratio.parent o}:Support c)
  let v (j : I×G.ColorIndex) := (splitCo S.ratio (Axis × G.ColorIndex)) ((M.address j.1).1, (M.address j.1).2, j.2)
  have hv (j : I×G.ColorIndex) : (v j).1=S.ratio.parent (M.address j.1).1 := congrArg Prod.fst (split_co S.ratio _)
  let a j : (↥U) × Co S.patch.L (Axis × G.ColorIndex) := (⟨(v j).1,halo_spec.mpr ⟨_,Finset.mem_singleton_self _,by
    rw [hv,separation_comm]; exact scope_inside h _ ho _ (M.stores j.1 (halo_subset _ _ (Finset.mem_singleton_self _)))⟩⟩,(v j).2)
  have hS : Fintype.card (I×G.ColorIndex) ≤ Fintype.card ((↥U) × Co S.patch.L (Axis × G.ColorIndex)) := Fintype.card_le_of_injective a (by
    rintro ⟨i,j⟩ ⟨y,z⟩ hi
    obtain ⟨hh,hq⟩ := Prod.mk.inj hi
    have he := (splitCo S.ratio _).injective (show v (i,j)=v (y,z) from Prod.ext (congrArg Subtype.val hh) hq)
    obtain ⟨hy,hH,rfl⟩ := Prod.mk.inj he |>.imp_right Prod.mk.inj
    exact Prod.ext (M.address_inj (Prod.ext hy hH)) rfl)
  rw [Fintype.card_prod (α:=↥U),Fintype.card_coe] at hS
  exact hS.trans (Nat.mul_le_mul_right _ (show U.card ≤ _ by simpa using Corona.halo_size ({S.ratio.parent o}:Support c) (scope B X r x)))
end Museum
end YM.PhysicalNext.JointLoad.Heir
