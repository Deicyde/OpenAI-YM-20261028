import YM.Next.MAXWELL.Team

/-! # At caps ≤4 and 5 -/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory
open MvPolynomial hiding monomial
open scoped ContDiff Topology BigOperators ComplexOrder InnerProductSpace
variable {G : Gauge} {j l d : ℕ}

private lemma splits_one (p : Slot G →₀ ℕ) (hp : p≠0) : ∃ i q, p=q+Finsupp.single i 1 := by
  classical
  obtain ⟨i,h⟩ : p.support.Nonempty := by simpa using hp
  have ht : Finsupp.single i 1 ≤ p := by
    intro x; by_cases he : x=i
    · subst x; rw [Finsupp.single_eq_same]; exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp h)
    simp [Ne.symm he]
  exact ⟨i,p-Finsupp.single i 1,(tsub_add_cancel_of_le ht).symm⟩

lemma weight_next (p : Slot G →₀ ℕ) (i : Slot G) : degree (p+Finsupp.single i 1)=degree p+i.1+2 := by
  unfold degree; rw [map_add,Finsupp.weight_single,one_smul]; unfold scaleW; omega

def Teams (G : Gauge) (j l : ℕ) := Submodule.span ℂ {u | ∃ (p : Flavor j) (q : Flavor l), u=team G p q}

lemma in_team (G : Gauge) (p : Flavor j) (q : Flavor l) : team G p q ∈ Teams G j l := Submodule.subset_span ⟨p,q,rfl⟩

lemma team_swap (G : Gauge) (p : Flavor j) (q : Flavor l) : team G p q=team G q p := by unfold team; simp_rw [show ∀ i : G.ColorIndex, bit p i * bit q i=bit q i*bit p i from fun i => mul_comm ..]
lemma swapped_teams (G : Gauge) (j l : ℕ) : Teams G j l=Teams G l j := by
  unfold Teams; congr 1; ext p; constructor <;> (rintro ⟨a,b,rfl⟩; exact ⟨b,a,team_swap ..⟩)

lemma team_fit (h : j+l+4 ≤ d) : Teams G j l ≤ shellSector G d := by
  rw [Teams,Submodule.span_le]; rintro v ⟨p,q,rfl⟩; exact team_label p q h

private lemma binary (p q : Slot G) (h : G.Simple) : moyenne G (X p* X q) ∈ Teams G p.1 q.1 := by
  classical
  rw [← symbol_coordinate p,← symbol_coordinate q]; simp_rw [divide,Finset.sum_mul,Finset.mul_sum,map_sum];
  apply Submodule.sum_mem; intro i _; apply Submodule.sum_mem; intro j _
  obtain ⟨t,ht⟩ := duet (flavor_pick (coordinateLeg p) _) (flavor_pick (coordinateLeg q) _) i j h; rw [ht]
  exact Submodule.smul_mem _ (t:ℂ) (in_team G _ _)

def BottomOnly (G : Gauge) := Submodule.span ℂ ({1} : Set (WickPol G))

private lemma low_range (V : Submodule ℂ (WickPol G)) (h : G.Simple) (hd : d ≤ 5) (hv : 1 ∈ V)
    (hp : 4 ≤ d → Teams G 0 0 ≤ V) (hk : 5 ≤ d → Teams G 0 1 ≤ V) : shellSector G d ≤ V := by
  classical
  intro p hP; obtain ⟨H,W⟩ := sector.mp hP
  rw [← paints_self W]
  rw [lowerCap,MvPolynomial.restrictSupport_eq_span] at H
  refine Submodule.span_induction (p := fun p _ => moyenne G p ∈ V) ?_ ?_ ?_ ?_ H
  · rintro p ⟨x,hx,rfl⟩; change degree x ≤ d at hx
    by_cases ht : x=0
    · subst x; change moyenne G 1∈ V; rw [paints_self (fun u => map_one _)]; exact hv
    obtain ⟨i,p,rfl⟩ := splits_one _ ht
    rw [weight_next] at hx
    by_cases ht : p=0
    · subst p; simp only [zero_add];
      change moyenne G (X i)∈V; rw [← symbol_coordinate, solo _ h]; exact Submodule.zero_mem _
    obtain ⟨j,p,rfl⟩ := splits_one _ ht
    rw [weight_next] at hx
    by_cases ht : p=0
    · subst p; simp only [zero_add]
      rw [show MvPolynomial.monomial _ 1=X (R:=ℂ) j * X i by rw [X,X,MvPolynomial.monomial_mul,one_mul]]
      apply (show Teams G j.1 i.1 ≤ V from ?_) (binary j i h)
      by_cases he : j.1=0
      · by_cases H : i.1=0
        · rw [he,H]; exact hp (by omega)
        have hi : i.1=1 := by omega
        rw [he,hi]; exact hk (by omega)
      rw [swapped_teams, show j.1=1 by omega, show i.1=0 by omega]; exact hk (by omega)
    obtain ⟨k,p,rfl⟩ := splits_one _ ht
    rw [weight_next] at hx; omega
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
  intro t y _ hy; rw [map_smul]; exact Submodule.smul_mem _ _ hy

lemma unit_fits : BottomOnly G ≤ shellSector G d := by
  rw [BottomOnly,Submodule.span_le]; rintro u h
  obtain rfl : u=(1:WickPol G) := h
  exact ⟨Labels.unit G d, map_one reduceEq⟩
lemma unit_mem (G : Gauge) : 1 ∈ BottomOnly G := Submodule.subset_span rfl



lemma low_support (h : G.Simple) : shellSector G 4=BottomOnly G ⊔ Teams G 0 0 := by
  apply le_antisymm (low_range _ h (by omega) ((show BottomOnly G ≤ BottomOnly G ⊔ Teams G 0 0 from le_sup_left) (unit_mem G)) (fun _ => le_sup_right) (by omega));
  exact sup_le unit_fits (team_fit (by omega))

lemma five_support (h : G.Simple) : shellSector G 5=shellSector G 4 ⊔ Teams G 0 1 := by
  rw [low_support h]
  refine le_antisymm (low_range _ h (by omega) ?_ ?_ ?_) ?_
  · exact (show BottomOnly G ⊔ Teams G 0 0 ≤ BottomOnly G ⊔ Teams G 0 0 ⊔ Teams G 0 1 from le_sup_left) ((show BottomOnly G ≤ BottomOnly G ⊔ Teams G 0 0 from le_sup_left) (unit_mem G))
  · exact fun _ => le_trans le_sup_right le_sup_left
  · exact fun _ => le_sup_right
  exact sup_le (sup_le unit_fits (team_fit (by omega))) (team_fit (by omega))

/-- Turn every coordinate's sign. -/
def oppositeFrame : Signed := ⟨Equiv.refl _,fun _ => true⟩

lemma whole_axis (x : E4) : Ortho.move oppositeFrame.ortho x = -x := by
  ext i
  rw [Signed.ortho_move]; simp [oppositeFrame,Signed.act]

lemma upside_form {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (A : Solution F j) :
    solutionTurn oppositeFrame.ortho A=(-1:ℝ)^j • A := by
  have ht : oppositeFrame.ortho⁻¹ = oppositeFrame.ortho := (map_inv Signed.inclusionO oppositeFrame).symm
  apply asWave_inj; rw [rot_wave]; funext a b x
  unfold fieldTurn; rw [ht, whole_axis]
  have hv (i l) : oppositeFrame.ortho.val i l = if i=l then -1 else 0 := by
    simp [Signed.ortho, Signed.matrix,oppositeFrame,eq_comm]
  simp only [hv,ite_mul,mul_ite,neg_mul,one_mul,neg_neg, zero_mul,mul_zero,ite_smul,one_smul,zero_smul]
  simp
  rw [← neg_one_smul ℝ x]; exact Tensor.homogeneous ..

lemma inversion (p : Probe G j) : reflectPol oppositeFrame.ortho (symbol j p)=
    (↑((-1:ℝ)^j):ℂ) • symbol j p := by
  apply equalPol; intro A; rw [reflects_eval,map_smul, symbol_test,symbol_test,
    show oppositeFrame.ortho⁻¹ = oppositeFrame.ortho from (map_inv Signed.inclusionO _).symm,upside_form, map_smul]; simp

lemma picture_zero (h : G.Simple) (p : WickPol G) (hp : p ∈ shellSector G 4) :
    reflectPol oppositeFrame.ortho p = p := by
  rw [low_support h,Submodule.mem_sup] at hp
  obtain ⟨x,hx,y,hy,rfl⟩ := hp; rw [map_add]; congr 1
  · obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hx; rw [map_smul,map_one]
  induction hy using Submodule.span_induction with
  | mem x h => obtain ⟨a,b,rfl⟩ := h; simp [team,map_sum,bit,map_mul,inversion]
  | zero => exact map_zero _
  | add x y _ _ ha hb => rw [map_add,ha,hb]
  | smul t x _ hv => rw [map_smul,hv]

lemma picture_five (p : WickPol G) (hp : p ∈ Teams G 0 1) :
    reflectPol oppositeFrame.ortho p = -p := by
  induction hp using Submodule.span_induction with
  | mem x h => obtain ⟨a,b,rfl⟩ := h; simp [team,map_sum,bit,map_mul,inversion]
  | zero => simp
  | add x y _ _ ha hb => rw [map_add,ha,hb,neg_add]
  | smul t x _ hv => rw [map_smul,hv,smul_neg]


end YM.Maxwell.Free
