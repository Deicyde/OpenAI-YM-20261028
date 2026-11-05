import YM.RG08.Ballast.Beads

/-! # Vacuum kernel symmetrization on positions

Images still actual cover displacements; uniqueness uses ALL coordinates of the
period lines, not the coefficient read at one period.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG Laurent Lattice Wilson Bloch Next.Free Push.AbsoluteSums Finset Function Filter
open UVExt.Paths Stationary
open scoped Topology ContDiff Classical
variable {α β ι : Type} {r : ℕ} {w w' C A B : ℝ} {m : Side}

def firstDot (b : Beads α r) : Cover := match r with
  | 0 => 0
  | _+1 => (b 0).1

def centerDot (b : Beads α r) : Beads α r := fun i => ((b i).1-firstDot b,(b i).2)
def CenterDot (b : Beads α r) := firstDot b=0
def ordered (p : Shale α r) := ∀ i,p i≠0 → CenterDot i
lemma center_centers (b : Beads α r) : CenterDot (centerDot b) := by cases r <;> simp [firstDot,CenterDot,centerDot]

def centralize (p : Shale α r) : Shale α r := pool p centerDot
variable {F H : Shale α r}
lemma central_price (hw : 0≤w) (hp : Glow F ((r+1 : ℕ)*w) C) : Glow (centralize F) w C := by
  apply Charge.poolage centerDot (ling_one hw)
  apply hp.mono (fun i => (ling_pos w (centerDot i)).le) _ le_rfl
  intro i
  have he : size (firstDot i) ≤ girth i := by
    cases r; · simp [firstDot,size]
    exact single_le_sum (f:=fun j => size (i j).1) (fun _ _=> Nat.zero_le _) (mem_univ (0:Fin _))
  have hc : girth (centerDot i) ≤ (r+1)*girth i := by
    calc
      _ ≤ ∑ j,(size (i j).1+size (-firstDot i)) := sum_le_sum fun j _=> by rw [show (centerDot i j).1= (i j).1+(-firstDot i) by unfold centerDot; simp only [sub_eq_add_neg]]; exact size_add ..
      _ = girth i+r*size (firstDot i) := by simp [sum_add_distrib,girth,size]
      _ ≤ girth i+r*girth i := by gcongr
      _ = _ := by ring
  apply Real.exp_le_exp.mpr
  have hh : (girth (centerDot i) : ℝ) ≤ r*(girth i : ℝ)+girth i := by
    rw [add_mul, one_mul] at hc; exact_mod_cast hc
  push_cast; nlinarith only [mul_le_mul_of_nonneg_left hh hw]
lemma central_order (p : Shale α r) : ordered (centralize p) := fun _ he =>
  by_contra fun h => he (pool_eq_zero centerDot fun b hb => (h (hb ▸ center_centers b)).elim)
lemma shale_total_sum (s : Finset ι) {F : ι→Shale α r} (h : ∀ i∈s,Summable (F i)) : Summable (∑ i∈s,F i) := by
  rw [show (∑ i∈s,F i)=_ from (funext fun b=>Finset.sum_apply b s F : (∑ i∈s,F i)=(fun b=>∑ i∈s,F i b))]; exact summable_sum h

def rewind (f : Shale α r) (s : Equiv.Perm (Fin r)) : Shale α r := pool f (fun b => b ∘ s.symm)
abbrev amplitude (r : ℕ) := (Fintype.card (Equiv.Perm (Fin r)):ℝ)
def pitch (f : Shale α r) : Shale α r := (amplitude r)⁻¹ • ∑ s,rewind f s
def score (f : Shale α r) : Shale α r := centralize (pitch f)
lemma rewind_summable (h : Summable F) (s) : Summable (rewind F s) :=
  (h.hasSum.tsum_fiberwise (fun b => b ∘ s.symm)).summable
lemma pitch_summable (h : Summable F) : Summable (pitch F) := (shale_total_sum univ fun i _ => rewind_summable h i).mul_left _
lemma score_summable (h : Summable F) : Summable (score F) :=
  ((pitch_summable h).hasSum.tsum_fiberwise centerDot).summable
lemma rewind_cost (s) (h : Glow F w A) (hw : 0≤w) : Glow (rewind F s) w A := by
  apply Charge.poolage (fun b => b ∘ s.symm) (ling_one hw)
  exact h.mono (fun b => (ling_pos w (b ∘ s.symm)).le) (fun b => Real.exp_le_exp.mpr
    (le_of_eq (congr_arg _ (show (girth (fun i => b (s.symm i)):ℝ)=girth b from by
      congr 1; exact Equiv.sum_comp s.symm (fun i => size (b i).1))))) le_rfl
lemma score_price (h : Glow F ((r+1 : ℕ)*w) A) (hw : 0≤w) : Glow (score F) w A := by
  have he : 0 < amplitude r := by unfold amplitude; positivity
  have hu : ‖(amplitude r)⁻¹‖*(amplitude r*A)=A := by rw [Real.norm_eq_abs,abs_of_nonneg (inv_pos.mpr he).le,inv_mul_cancel_left₀ he.ne']
  apply central_price hw
  have hh := Charge.sums (w:=ling ((r+1:ℕ)*w)) (fun i => (ling_pos _ i).le) (s:=univ) (fun i _ => rewind_cost i h (by positivity))
  simpa only [sum_const,card_univ,nsmul_eq_mul,hu,pitch] using hh.scale (amplitude r)⁻¹

variable [Fintype α]

def Tunable (F : Shale α r) := Summable F ∧ ordered F ∧ ∀ m, Tensor.Sym (recital F m)
lemma recital_central (hf : Summable F) (m : Side) : recital (centralize F) m= recital F m := by
  ext1 v
  unfold centralize; rw [recital_pool _ hf, recital_eval v hf]
  have hv : (∑' j,∑ z,F j*rosary v z (centerDot j))=∑ z,∑' j,F j*rosary v z (centerDot j) :=
    Summable.tsum_finsetSum (s:=univ) (fun z _=> sum_bounded hf fun i => rosary_bill v z (centerDot i))
  rw [← hv, ← (Summable.tsum_finsetSum (s:=univ) (fun z _=>bead_summable F v hf z))]; apply tsum_congr; intro b
  refine Fintype.sum_equiv (Equiv.addRight (-wrap _ (firstDot b))) _ _ (fun z => ?_)
  congr 1; apply prod_congr rfl; intro i _
  congr 1; simp [centerDot,silks]; abel
lemma recital_score (hf : Summable F) (m : Side) : recital (score F) m = Tensor.symmetrize (recital F m) := by
  rw [score,recital_central (pitch_summable hf),pitch,recital_scale _ (shale_total_sum _ (fun i _=>rewind_summable hf i)),recital_sum _ _ (fun i _ => rewind_summable hf i),Tensor.symmetrize]
  congr 1; apply sum_congr rfl; intro s _; ext1 v
  change _= recital F m (v ∘ s)
  rw [rewind,recital_pool _ hf,recital_eval _ hf]; apply sum_congr rfl; intro z _; apply tsum_congr; intro b
  congr 1; refine Fintype.prod_equiv s.symm _ _ (fun k => ?_)
  rw [comp_apply,s.apply_symm_apply]; rfl
lemma score_tunable (h : Summable F) : Tunable (score F) :=
  ⟨score_summable h,central_order (pitch F), fun m => by rw [recital_score h]; exact Tensor.symmetrize_sym _⟩
lemma stanza_score (h : Summable F) (m : Side) : stanza (score F) m=stanza F m := by
  unfold stanza; rw [recital_score h]; exact funext fun i => Tensor.symmetrize_diagonal _ i

lemma Tunable.zero (α : Type) [Fintype α] (r : ℕ) : Tunable (0:Shale α r) := by
  exact ⟨summable_zero,fun _ h => (h rfl).elim, fun m => by rw [recital_zero]; exact fun _ _=>rfl⟩
lemma Tunable.add (h : Tunable F) (g : Tunable H) : Tunable (F+H) := by
  refine ⟨h.1.add g.1,fun i hi=>?_,fun m v s=>?_⟩
  · by_contra hh; apply hi; rw [Pi.add_apply, not_ne_iff.mp (mt (g.2.1 i) hh), not_ne_iff.mp (mt (h.2.1 i) hh), add_zero]
  rw [recital_add h.1 g.1]; rw [_root_.add_apply,h.2.2 m v s,g.2.2 m v s,_root_.add_apply]
lemma Tunable.scale (a : ℝ) (h : Tunable F) : Tunable (a • F) := by
  refine ⟨h.1.mul_left _,fun i hi => h.2.1 i fun hr => hi ?_,fun m v s => ?_⟩
  · simp [hr]
  rw [recital_scale _ h.1,_root_.smul_apply,h.2.2 m v s,_root_.smul_apply]
lemma Tunable.neg (h : Tunable F) : Tunable (-F) := by simpa using h.scale (-1)
lemma Tunable.sub (h : Tunable F) (g : Tunable H) : Tunable (F-H) := by rw [sub_eq_add_neg]; exact h.add g.neg
lemma Tunable.sum {F : ι→Shale α r} (s : Finset ι) (h : ∀ i∈s, Tunable (F i)) : Tunable (∑ i∈s,F i) := by
  induction s using Finset.induction_on with
  | empty => rw [sum_empty]; exact Tunable.zero ..
  | insert i s hi ih => rw [sum_insert hi]; exact (h _ (mem_insert_self ..)).add (ih (fun _ hj => h _ (mem_insert_of_mem hj)))
end YM.RG08
