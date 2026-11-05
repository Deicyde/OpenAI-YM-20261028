import YM.RG08.Pivot.Cache

set_option autoImplicit false
noncomputable section
namespace YM.RG08.Pivot
open Function Filter Lattice Wilson RG Exterior Precision Next.Free
open Laurent Bloch Matrix Work.F08 Tree FreeResolvent Stationary Finset
open UVExt.Paths Drift Scores Loom Shade Quire Tall Vale Analysis
open scoped Topology BigOperators Classical
variable {A : Type}[Fintype A][DecidableEq A]
variable {r n l : ℕ}

lemma stair_compare (P Q : Matrix A A ℝ)(V:Cupboard A) (ht:∀ i,Tensor.Sym (V i)) (n r:ℕ):
    terraces (P+Q) V n r= ∑ i∈wheel n, terraces P (terraces Q V i.2) i.1 r := by
  let f (b:ℕ×ℕ)(r:ℕ):= terraces P (terraces Q V b.2) b.1 r
  induction n generalizing r with
  | zero=> simp [terraces,wheel]
  | succ n IH =>
    apply smul_right_injective (CupA A r) (show ((n+1:ℕ):ℝ)≠0 by positivity)
    rw [terraces]; dsimp only; rw [smul_smul,mul_inv_cancel₀ (by positivity),one_smul,IH,burs_pledge]; symm
    calc
      (↑(n+1:ℕ):ℝ) • ∑ i∈wheel (n+1),f i r=∑ i∈wheel (n+1), ((i.1:ℝ)+(i.2:ℝ)) • f i r := by
        rw [Finset.smul_sum]; exact sum_congr rfl fun _ hi=> congr_arg (fun q:ℝ=> q • _) (by exact_mod_cast (mem_antidiagonal.mp hi).symm)
      _ = ∑ i∈wheel n, (↑(i.1+1:ℕ):ℝ) • f (i.1+1,i.2) r + ∑ i∈wheel n,(↑(i.2+1:ℕ):ℝ) • f (i.1,i.2+1) r :=by
        simp only [wheel,add_smul,sum_add_distrib]; rw [Finset.Nat.sum_antidiagonal_succ (f:=fun i => (i.1:ℝ) • f i r), Finset.Nat.sum_antidiagonal_succ' (f:=fun i => (i.2:ℝ) • f i r)]; simp only [Nat.cast_zero,zero_smul,zero_add]
      _ = _ := by
        rw [← Finset.sum_add_distrib]; refine sum_congr rfl fun i hi=>?_
        rw [show f (i.1+1,i.2) r= _ from (by change terraces _ _ (_+1) r= (↑(i.1+1:ℕ):ℝ)⁻¹ • bur P (f i (r+2)); rw [terraces] : f _ r=(↑(i.1+1:ℕ):ℝ)⁻¹ • bur P (f i (r+2))), smul_smul,mul_inv_cancel₀ (by positivity),one_smul,bur_change]; congr 1
        have hv : terraces Q V (i.2+1) = (↑(i.2+1:ℕ):ℝ)⁻¹ • (fun r=> bur Q (terraces Q V i.2 (r+2))) := funext fun i=>by simp only [terraces,Pi.smul_apply]
        unfold f; dsimp only; rw [hv,t_cost,t_right,smul_smul,mul_inv_cancel₀ (by positivity),one_smul]; exact terraces_sym Q V ht i.2
lemma stair_merge (P Q:Matrix A A ℝ)(V:Cupboard A)(h:∀ i,Tensor.Sym (V i)) (hn:Ceils V n) :
    harvestL (P+Q) V n r=harvestL P (harvestL Q V n) n r := by
  change _=∑ i∈ range (n+1), terraces P (harvestL Q V n) i r
  rw [show (∑ i∈ range (n+1),terraces P (harvestL Q V n) i r) =∑ i∈range (n+1),∑ j∈range (n+1), terraces P (terraces Q V j) i r from
    sum_congr rfl fun i _=> t_collect P (terraces Q V) (range (n+1)) i r]
  rw [triangle_sum (fun i j => terraces P (terraces Q V j) i r)]; swap
  · intro x y hp; have hy (i a):a+2*(i+y)+2*x>n → terraces P (terraces Q V y) (i+x) a=0 := fun h=> by
      clear hp; revert h; generalize hz:i+x=z; intro h
      rw [show a+2*(i+y)+2*x=a+2*(z+y) by omega] at h
      clear i x hz; induction z generalizing a with
      | zero=> simp only [terraces]; exact stairs_zeros Q V y hn (by omega)
      | succ i ih=> rw [terraces, ih (a+2) (by omega),bur_home,smul_zero]
    have he : ¬ _:= mt (hy 0 r) (show terraces P (terraces Q V y) (0+x) r≠0 by simpa using hp); omega
  simp_rw [← stair_compare P Q V h]; exact sum_subset (range_mono (by omega)) (fun i _ hi=> stairs_zeros _ _ i hn (by have he:=mt Finset.mem_range.mpr hi; omega))

-- Preserve Sober through all tensor cuts
def CoastT (M : Matrix A A ℝ) (F:CupA A r) : Prop := ∀ i : Fin r,∀ w : Fin r→A→ℝ,∀ x:A→ℝ, F (update w i (M*ᵥ x))=F (update w i x)

lemma bur_stay {M : Matrix A A ℝ} (P:Matrix A A ℝ){W:CupA A (r+2)} (h: CoastT M W) : CoastT M (bur P W) := by
  intro i w v; rw [bur_eval,bur_eval]; congr 1
  exact sum_congr rfl fun a _ => sum_congr rfl fun b _=> by simp_rw [Fin.cons_update, h i.succ.succ]
lemma terraces_stay {M : Matrix A A ℝ} (P:Matrix A A ℝ) (V:Cupboard A) (h:∀ i,CoastT M (V i)) (n r : ℕ) : CoastT M (terraces P V n r) := by
  induction n generalizing r with
  | zero=> rw [terraces]; exact h r
  | succ i ih=> rw [terraces]; exact fun x w v=> congr_arg ((↑(i+1:ℕ):ℝ)⁻¹ • ·) (bur_stay P (ih (r+2)) x w v)
lemma hic {M : Matrix A A ℝ} (P:Matrix A A ℝ) {V:CupA A (r+2)} (h: CoastT M V):
    bur (M*P*Mᵀ) V=bur P V := by
  ext1 v; rw [bur_wander,bur_eval]; congr 1
  refine sum_congr rfl fun i _=> sum_congr rfl fun j _=> ?_; congr 1
  let W v' v'': Fin (r+2) → A→ℝ:= Fin.cons v' (Fin.cons v'' v)
  have hs (a b : A→ℝ) : V (W (M*ᵥ a) b) = V (W a b):= by simpa only [W,Fin.update_cons_zero] using h 0 (W a b) a
  have hh (a b : A→ℝ) : V (W a (M*ᵥ b))=V (W a b) := by
    have he:= h (0:Fin (r+1)).succ (W a b) b; unfold W at *; rw [← Fin.cons_update,← Fin.cons_update, Fin.update_cons_zero,Fin.update_cons_zero] at he; exact he
  exact (hs _ _).trans (hh ..)
lemma terraces_equal {M : Matrix A A ℝ} {P Q : Matrix A A ℝ}(hv : M*P*Mᵀ=M*Q*Mᵀ)(V:Cupboard A)(h:∀ i,CoastT M (V i)) (n r : ℕ) : terraces P V n r=terraces Q V n r := by
  induction n generalizing r with
  | zero=> simp_rw [terraces]
  | succ i ih=> rw [terraces,ih,← hic (M:=M) (P:=P) (terraces_stay Q V h i (r+2)),hv, hic Q (terraces_stay Q V h i (r+2)),terraces]
end YM.RG08.Pivot
