import YM.RG08.Germ.Squares
import YM.RG08.Wallet.Bind

/-! # Alphabet and transfers (Park: all fine residues + coarse log)

Tree restriction when evaluating Gaussian only. All calculations unmasked.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG Laurent Lattice Wilson Exterior Precision Bloch Next.Free Work.F08 Push.AbsoluteSums Finset Function Filter
open Stationary Analysis UVExt.Paths Matrix Tree
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius InnerProductSpace Classical
variable {c f m L : Side} {α β : Type} {G : Gauge}
variable {σ η B C : ℝ} {r : ℕ}
section park
-- pack/unpack with actual proof chart
variable (G)
def lodgeP (g : Ratio c f) (x : Link G f) (u : Link G c) : Alley G g :=
    fun v=> v.2.elim (fun j=> x ((splitCo g _).symm (v.1,j))) (fun j=> u (v.1,j))
lemma lodge_f (g : Ratio c f) (x : Link G f) (u : Link G c) : fineL G g (lodgeP G g x u)=x := by
  ext1 i
  change x ((splitCo g _).symm (splitCo g _ i))= _; rw [Equiv.symm_apply_apply]
lemma lodge_c (g : Ratio c f) (x : Link G f) (u : Link G c) : coarseL G g (lodgeP G g x u)=u := rfl
lemma lodge_undo (g : Ratio c f) (x : Alley G g) : lodgeP G g (fineL G g x) (coarseL G g x)=x := by
  ext1 a; rcases a with ⟨a,i|i⟩; unfold lodgeP fineL; simp only [Sum.elim_inl,ContinuousLinearMap.pi_apply]; rw [Equiv.apply_symm_apply]; rfl
  rfl
end park
section draw
-- Insert a single alphabet left
variable [Fintype α] [Fintype β] [DecidableEq α]
def skylight (α β : Type) [DecidableEq α] : Row α (α⊕β) := fun i j t=> j.elim (fun a=> unitRow α i a t) (fun _ => 0)
omit [Fintype α] [Fintype β] in
lemma skylight_price : (skylight α β).strip σ 1 := by intro i j; rcases j with j|j; exact strip_unit _ _; simp [Width,SumBudget,skylight]
lemma skylight_in (x : PAC (α⊕β) m) (i : Co m α) : ((skylight α β).acts m *ᵥ x) i=x (i.1,.inl i.2) := by
  have ht (j : Co m α) : (skylight α β).acts m i (j.1,Sum.inl j.2)=(1:Matrix (Co m α) _ ℝ) i j := by rw [← acts_unit]; rfl
  have hp (z : Site m) (j : β) : (skylight α β).acts m i (z,Sum.inr j)=0 := by simp [Row.acts,skylight]
  unfold Matrix.mulVec dotProduct; rw [Fintype.sum_prod_type]; simp_rw [Fintype.sum_sum_type];
  simp only [hp,zero_mul,sum_const_zero, add_zero];
  let v (j : Co m α) := x (j.1,Sum.inl j.2)
  have he z j : (skylight α β).acts m i (z,.inl j) * x (z,.inl j)=(1:Matrix (Co m α) _ ℝ) i (z,j)*v (z,j) := by rw [show (skylight _ _).acts _ _ _ =_ from ht (z,j)]
  simp_rw [he]; rw [← Fintype.sum_prod_type (f:=fun p=> (1:Matrix (Co m α) _ ℝ) i p*v p)]; exact (show (1*ᵥ v) i=v i by rw [one_mulVec])

end draw

def gemL (L : Side) (F : Pot G r) := scrollL (grapes L F) (skylight _ (Loc G 1))
lemma gem_price (F : Pot G r) (hp : Glow F σ C) (hx : 0≤η) (he : (r+1:ℕ)*η≤L.val*σ) :
    Glow (gemL L F) η ((Fintype.card (Park G L):ℝ)^r*((L.val:ℝ)^4*(Real.exp (4*((r+1:ℕ)*η))^r*C))) := by
  have h := scroll_price (skylight _ (Loc G 1)) (grapes_glow L hp (by positivity) he) hx zero_le_one skylight_price
  simpa only [one_pow,mul_one,gemL] using h
lemma gem_tune (F : Pot G r) (L : Side) (h : Summable F) : Tunable (gemL L F) :=
    scroll_tune (grapes_summable L h) ⟨_,_,one_pos,skylight_price⟩
lemma gem_light (F : Pot G r) (h : Summable F) (g : Ratio c f) (x : Alley G g) : stanza (gemL g.count F) c x = stanza F f (fineL G g x) := by
  rw [gemL,scroll_play (grapes_summable _ h) ⟨_,_,one_pos,skylight_price⟩,grapes_stanza g _ h] -- whole mk exists
  congr 1; funext i; unfold carriesG; rw [skylight_in]; rfl
lemma gem_less {F H : Pot G r} (f : Summable F) (h : Summable H) (L : Side) : gemL L (F-H)=gemL L F-gemL L H := by
  simp only [gemL,grapes_sub _ f h,scroll_less (grapes_summable _ f) (grapes_summable _ h) (show Whole (skylight _ (Loc G 1)) from ⟨_,_,one_pos,skylight_price⟩)]

-- mean in this chart

def scan {α β : Type} [DecidableEq β] (A : Row α β) := stackRows A (unitRow β)
lemma scan_fee [DecidableEq β] {A : Row α β} (h : A.strip σ B) : (scan A).strip σ (max B 1) := strip_stack h strip_unit
lemma scan_moves [DecidableEq β] {A D : Row α β} (h : (A-D).strip σ B) (hp : 0 ≤ B) : (scan A-scan D).strip σ B := by
  intro i j; rcases i with i|i
  · exact h i j
  simp [scan,stackRows,Width,SumBudget,hp]
lemma scan_whole [DecidableEq β] {A : Row α β} (h : Whole A) : Whole (scan A) := by obtain ⟨w,D,hv,H⟩:=h; exact ⟨_,_,hv,scan_fee H⟩
lemma scan_at (g : Ratio c f) (A : Cross g.count (Loc G 1) (Loc G 1)) (v : Link G c) :
    (scan A).acts c*ᵥ v=lodgeP G g (installed g A *ᵥ v) v := by
  ext1 x; obtain ⟨i,j|j⟩:=x
  · unfold lodgeP; dsimp only; apply sum_congr rfl; intro a _; simp only [installed, Matrix.submatrix_apply,Equiv.apply_symm_apply]; rfl
  · apply Eq.trans _ (congr_fun (one_mulVec v) (i,j)); rw [← acts_unit]; rfl
end YM.RG08
