import YM.Next.MAXWELL.Steps

/-! # Only two interpolation constants before cross-seed -/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory Wick
open scoped ContDiff Topology BigOperators InnerProductSpace ComplexOrder
variable {G : Gauge}

def permFrame (s : Equiv.Perm Axis) : Signed := ⟨s,fun _ => false⟩

def menu (i a b z : Axis) := parity z i * parity z a * parity z b

def Rays (x : Flavor 1) (f : Axis → ℝ) := ∀ z, actFlavor (Signed.reflect z) 1 x = f z • x

lemma rays_shift (i a b) : Rays (shift i a b) (menu i a b) := by
  intro z; simpa [tilt,Signed.mirror,parity,Signed.reflect, menu] using tilt_step (Signed.mirror z) i a b
lemma meal_price (i a b z : Axis) : menu i a b z=1 ∨ menu i a b z= -1 := by unfold menu parity; split_ifs <;> simp

def coop (a : Axis) (w : ℝ) : Module.End ℝ (Flavor 1) := (1/2:ℝ) • (LinearMap.id + w • actFlavor (Signed.reflect a) 1)
def coOp (f : Axis → ℝ) := (coop 3 (f 3)).comp ((coop 2 (f 2)).comp ((coop 1 (f 1)).comp (coop 0 (f 0))))
lemma coop_at (z : Axis) (u : Flavor 1) {g : Axis → ℝ} (h : Rays u g) (hg : g z=1 ∨ g z = -1) (w : ℝ) (hw : w=1 ∨ w = -1) :
    coop z w u = (open scoped Classical in if w=g z then u else 0) := by
  classical
  simp only [coop,LinearMap.add_apply,LinearMap.smul_apply,h z, LinearMap.id_apply]
  rcases hw with H | H <;> rcases hg with he | he <;> rw [H,he] <;>
    simp only [if_pos,one_smul,neg_smul,add_neg_cancel,smul_zero,← two_smul ℝ u,smul_smul] <;> norm_num
  rw [← add_smul]; norm_num
lemma parity_plate (f g : Axis → ℝ) (u : Flavor 1) (h : Rays u g) (hp : ∀ z, f z=1 ∨ f z = -1) (hq : ∀ z,g z=1 ∨ g z = -1) :
    coOp f u = (open scoped Classical in if f=g then u else 0) := by
  classical
  by_cases hh : f=g
  · subst g; simp [coOp,coop_at _ _ h (hq _) _ (hp _)]
  rw [if_neg hh]; unfold coOp; simp only [LinearMap.comp_apply]
  have ht (z) := coop_at z _ h (hq z) (f z) (hp z)
  rw [ht]
  -- use classical locally matching open scoped
  split_ifs with hw₀; swap; simp
  rw [ht]; split_ifs with hw₁; swap; simp
  rw [ht]; split_ifs with hw₂; swap; simp
  rw [ht]; split_ifs with hw₃
  exact (hh (funext fun i => by fin_cases i <;> assumption)).elim
  rfl

lemma trays (f : Axis → ℝ) (u : Flavor 1) (h : Rays u f) (hf : ∀ z, f z=1 ∨ f z = -1) :
    u∈Submodule.span ℝ {p : Flavor 1|∃ i a b : Axis,a<b ∧ f=menu i a b ∧ p=shift i a b} := by
  classical
  let V := Submodule.span ℝ {p : Flavor 1|∃ i a b : Axis,a<b ∧ f=menu i a b ∧ p=shift i a b}
  suffices hv : coOp f u∈ V by simpa [parity_plate f f u h hf hf] using hv
  have hp : ⊤ ≤ V.comap (coOp f) := by
    rw [← shift_span, Submodule.span_le]; rintro p ⟨i,a,b,he,rfl⟩
    change coOp f _∈ V; rw [parity_plate _ (menu i a b) _ (rays_shift i a b) hf (meal_price i a b)]
    split_ifs with h
    · exact Submodule.subset_span ⟨_,_,_,he,h,rfl⟩
    exact Submodule.zero_mem _
  exact hp (Submodule.mem_top (x:=u))

/-- test labels before using multiplication by zero. -/
def Conveyor (f : Axis → Flavor 0 →ₗ[ℝ] Flavor 1) := ∀ a (s : Signed) x,
    actFlavor s.ortho 1 (f a x) = tilt s a • f (s.perm a) (actFlavor s.ortho 0 x)

lemma Conveyor.serves {f : Axis → Flavor 0 →ₗ[ℝ] Flavor 1} (h : Conveyor f) (a i j : Axis) :
    Rays (f a (cell i j)) (menu a i j) := by
  intro z; rw [Signed.reflect,h _ (Signed.mirror z), tilt_one,map_smul,smul_smul]
  have ht b : tilt (Signed.mirror z) b = parity z b := by simp [parity,tilt,Signed.mirror]
  simp only [ht,menu,mul_assoc]; rfl

lemma Conveyor.runs {f : Axis → Flavor 0 →ₗ[ℝ] Flavor 1} (h : Conveyor f) (s : Equiv.Perm Axis) (x : Axis) (a b : Axis) :
    actFlavor (permFrame s).ortho 1 (f x (cell a b))=f (s x) (cell (s a) (s b)) := by
  rw [h _ (permFrame s),tilt_one]; simp [tilt,permFrame]

lemma bus (s : Equiv.Perm Axis) (i a b : Axis) : actFlavor (permFrame s).ortho 1 (shift i a b) = shift (s i) (s a) (s b) := by
  rw [tilt_step]; simp [tilt,permFrame]

set_option maxHeartbeats 500000 in
lemma track_near (i a b : Axis) (ht : a < b) (h : menu 0 0 1=menu i a b) :
    (i=0 ∧ a=0 ∧ b=1) ∨ (i=2 ∧ a=1 ∧ b=2) ∨ (i=3 ∧ a=1 ∧ b=3) := by
  have H := And.intro (congr_fun h 0) (And.intro (congr_fun h 1) (congr_fun h 2))
  clear h
  fin_cases i <;> fin_cases a <;> fin_cases b <;> simp [Axis] at ht ⊢ <;> simp [menu,parity,Axis] at H <;> norm_num at H

set_option maxHeartbeats 500000 in
lemma track_far (i a b : Axis) (ht : a < b) (h : menu 0 1 2=menu i a b) :
    (i=0 ∧ a=1 ∧ b=2) ∨ (i=1 ∧ a=0 ∧ b=2) ∨ (i=2 ∧ a=0 ∧ b=1) := by
  have H := And.intro (congr_fun h 0) (And.intro (congr_fun h 1) (congr_fun h 2))
  clear h
  fin_cases i <;> fin_cases a <;> fin_cases b <;> simp [Axis] at ht ⊢ <;> simp [menu,parity,Axis] at H <;> norm_num at H

section classification
variable (f : Axis → Flavor 0 →ₗ[ℝ] Flavor 1) (h : Conveyor f)
include h
lemma near_cell : ∃ a : ℝ, f 0 (cell 0 1)=a • shift 0 0 1 := by
  let P := menu 0 0 1
  let p := f 0 (cell 0 1)
  let s := Equiv.swap (2:Axis) 3
  let J := actFlavor (permFrame s).ortho 1
  let T := (1/2:ℝ) • (LinearMap.id (M:=Flavor 1) (R:=ℝ) + J)
  have hs : T p=p := by
    have ht : J p=p := by rw [show J p=_ from Conveyor.runs h s 0 0 1]; simp [s,Equiv.swap_apply_def,Axis,p]
    simp only [T, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply,ht,← two_smul ℝ p,smul_smul]
    norm_num
  let V := Submodule.span ℝ ({shift 0 0 1} : Set (Flavor 1))
  have hv : shift 0 0 1∈ V := Submodule.subset_span rfl
  have he : shift 2 1 2 + shift 3 1 3 = shift 0 0 1 := by
    have hh := free_shift 1
    rw [Fin.sum_univ_four,show shift 1 1 1=0 by rw [shift,cell_center,map_zero],shift_skew 2,shift_skew 3,add_zero,add_assoc,← neg_add] at hh
    exact ((add_neg_eq_zero ..).mp hh).symm
  have hp : Submodule.span ℝ {q : Flavor 1|∃ i a b : Axis,a<b ∧ P=menu i a b ∧ q=shift i a b} ≤ V.comap T := by
    rw [Submodule.span_le]; rintro q ⟨i,a,b,hw,hK,rfl⟩; change T _∈ V
    suffices hh : shift i a b + J (shift i a b)∈V from V.smul_mem (1/2:ℝ) hh
    unfold J; rw [bus]; rcases track_near _ _ _ hw hK with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩
    · simpa [s,Equiv.swap_apply_def,Axis] using (Submodule.add_mem V hv hv : shift 0 0 1 + shift 0 0 1 ∈ V)
    · simpa [s,Equiv.swap_apply_def,Axis, he] using hv
    simpa [s,Equiv.swap_apply_def,Axis,add_comm (shift 3 1 3),he] using hv
  have hw : p∈ V := hs ▸ (show T p∈ V from hp (trays P p (Conveyor.serves h 0 0 1) (meal_price 0 0 1)))
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hw; exact ⟨a,ha.symm⟩

lemma far_cell : ∃ a : ℝ, f 0 (cell 1 2)=a • shift 0 1 2 := by
  let P := menu 0 1 2
  let p := f 0 (cell 1 2)
  let s := Equiv.swap (1:Axis) 2
  let J := actFlavor (permFrame s).ortho 1
  let T := (1/2:ℝ) • (LinearMap.id (M:=Flavor 1) (R:=ℝ) - J)
  have hs : T p=p := by
    have ht : J p= -p := by rw [show J p=_ from Conveyor.runs h s 0 1 2]; simp [s,Equiv.swap_apply_def,Axis,p,cell_skew 2 1];
    simp [T,ht,← two_smul ℝ p,smul_smul]
  let V := Submodule.span ℝ ({shift 0 1 2} : Set (Flavor 1))
  have hv : shift 0 1 2∈ V := Submodule.subset_span rfl
  have he : shift 1 0 2 - shift 2 0 1 = shift 0 1 2 := by
    have hh := bianchi_shift 0 1 2
    rw [shift_skew 1] at hh
    rw [add_right_comm,← sub_eq_add_neg,sub_eq_zero] at hh
    rw [← hh,add_sub_cancel_right]
  have hp : Submodule.span ℝ {q : Flavor 1|∃ i a b : Axis,a<b ∧ P=menu i a b ∧ q=shift i a b} ≤ V.comap T := by
    rw [Submodule.span_le]; rintro q ⟨i,a,b,hw,hK,rfl⟩; change T _∈ V
    suffices hh : shift i a b - J (shift i a b)∈V from V.smul_mem (1/2:ℝ) hh
    unfold J; rw [bus]; rcases track_far _ _ _ hw hK with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩
    · simpa [s,Equiv.swap_apply_def,Axis,shift_skew 0 2 1] using (Submodule.add_mem V hv hv : shift 0 1 2 + shift 0 1 2 ∈ V)
    · simpa [s,Equiv.swap_apply_def,Axis, he] using hv
    simpa [s,Equiv.swap_apply_def,Axis,← neg_sub (shift 1 0 2),he] using hv
  have hw : p∈ V := hs ▸ (show T p∈ V from hp (trays P p (Conveyor.serves h 0 1 2) (meal_price 0 1 2)))
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hw; exact ⟨a,ha.symm⟩

lemma classification (c : G.ColorIndex) (hb : ∀ p q z,z≠0 → fare c (f 0 p) q z = fare c (f 0 q) p z) :
    ∃ a : ℝ, ∀ i, f i = a • feed (basis i) 0 := by
  obtain ⟨a,ha⟩ := near_cell f h
  obtain ⟨b,hK⟩ := far_cell f h
  let z := basis 0+basis 2
  have hz : z≠0 := cross_seed_ne
  have he : a=b := by
    have hh := hb (cell 0 1) (cell 1 2) z hz
    rw [ha,hK,← fare_pair c _ _ hz, ← fare_pair c _ _ hz,map_smul,map_smul,LinearMap.smul_apply,LinearMap.smul_apply,fare_pair,fare_pair,show fare c (shift 0 1 2) (cell 0 1) z = _ from shifts_sym c _ _ 0 hz, ← show shift 0 0 1=feed _ _ _ from rfl] at hh
    apply mul_right_cancel₀ (show fare c (shift 0 0 1) (cell 1 2) z≠0 from by rw [cross_seed]; have := normal_pos; positivity)
    exact hh
  subst b
  have hk (s : Equiv.Perm Axis) (hm : s 0=0) (a' b' : Axis) (hv : f 0 (cell a' b')= a • shift 0 a' b') :
      f 0 (cell (s a') (s b')) = a • shift 0 (s a') (s b') := by
    have ht := Conveyor.runs h s 0 a' b'
    rw [hm, hv,map_smul,bus,hm] at ht; exact ht.symm
  have ht : f 0 = a • feed (basis 0) 0 := by
    refine LinearMap.ext_on cell_span ?_; rintro x ⟨i,l,hi,rfl⟩
    change f 0 (cell i l) = a • shift 0 i l
    have hh : f 0 (cell 1 3)= a • shift 0 1 3 := by simpa [Equiv.swap_apply_def,Axis] using hk (Equiv.swap 2 3) (by decide) _ _ hK
    have h₂ : f 0 (cell 2 3)= a • shift 0 2 3 := by simpa [Equiv.swap_apply_def,Axis] using hk (Equiv.swap 1 2) (by decide) _ _ hh
    have h₁ : f 0 (cell 0 2)= a • shift 0 0 2 := by simpa [Equiv.swap_apply_def,Axis] using hk (Equiv.swap 1 2) (by decide) _ _ ha
    have h₃ : f 0 (cell 0 3)= a • shift 0 0 3 := by simpa [Equiv.swap_apply_def,Axis] using hk (Equiv.swap 1 3) (by decide) _ _ ha
    fin_cases i <;> fin_cases l <;> simp [Axis] at hi <;> assumption
  refine ⟨a,fun i => LinearMap.ext fun p => ?_⟩
  let q := Equiv.swap 0 i
  let k := permFrame q
  let s := k.ortho
  let v := actFlavor s⁻¹ 0 p
  have hm : actFlavor s 0 v=p := act_inv_f s p
  have hh : k.perm 0=i := Equiv.swap_apply_left _ _
  have he := h 0 k v
  change actFlavor s 1 _ = _ at he
  rw [hm,hh,show tilt k 0=1 from rfl,one_smul,ht,LinearMap.smul_apply,map_smul,step_go,heads,hh,show tilt k 0=1 from rfl,one_smul,hm] at he
  exact he.symm
end classification
end YM.Maxwell.Free
