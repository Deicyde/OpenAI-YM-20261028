import YM.RG08.Pivot.Clams

set_option autoImplicit false
noncomputable section
namespace YM.RG08.Pivot
open Function Filter Lattice Wilson RG Exterior Precision Next.Free
open Laurent Bloch Matrix Work.F08 Tree FreeResolvent Stationary Finset
open UVExt.Paths Drift Scores Loom Shade Quire Tall Vale Analysis
open scoped Topology BigOperators Classical
variable {A B Q I : Type}[Fintype A][DecidableEq A][Fintype B][DecidableEq B]
variable {r k n : ℕ}
private lemma slider (a b c d : A)(F:CupA A (r+4))(h:Tensor.Sym F)(v : Fin r→A→ℝ):
    F (Fin.cons (zpk a) (Fin.cons (zpk b) (Fin.cons (zpk c) (Fin.cons (zpk d) v))))=F (Fin.cons (zpk c) (Fin.cons (zpk d) (Fin.cons (zpk a) (Fin.cons (zpk b) v)))) := by
  let u:Fin (r+4) → A→ℝ := Fin.cons (zpk a) (Fin.cons (zpk b) (Fin.cons (zpk c) (Fin.cons (zpk d) v)))
  let i:Fin (r+4):=0; let j:Fin (r+4):=Fin.succ (0:Fin (r+3)); let k:Fin (r+4):=(0:Fin (r+2)).succ.succ; let l:Fin (r+4):=(0:Fin (r+1)).succ.succ.succ
  let σ: Equiv.Perm (Fin (r+4)):= (Equiv.swap i k).trans (Equiv.swap j l)
  refine ((h u σ).symm).trans (congr_arg F (funext fun x=>?_))
  have he : j≠k:=by unfold j k; simp only [Fin.succ_inj, ne_eq]; exact Ne.symm (Fin.succ_ne_zero _)
  have h1:l≠k:=by unfold l k; simp only [Fin.succ_inj, ne_eq, Fin.succ_ne_zero, not_false_eq_true]
  cases x using Fin.cases with
  | zero=> change u ((Equiv.swap j l) ((Equiv.swap i k) i))=zpk c; rw [Equiv.swap_apply_left,Equiv.swap_apply_of_ne_of_ne he.symm h1.symm]; rfl
  | succ x=> cases x using Fin.cases with
    | zero=> change u ((Equiv.swap j l) ((Equiv.swap i k) j))=zpk d; rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) he, Equiv.swap_apply_left]; rfl
    | succ x=> cases x using Fin.cases with
      | zero=> change u ((Equiv.swap j l) ((Equiv.swap i k) k))=zpk a; rw [Equiv.swap_apply_right,Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _|>.symm) (Fin.succ_ne_zero _|>.symm)]; rfl
      | succ x=> cases x using Fin.cases with
        | zero=> change u ((Equiv.swap j l) ((Equiv.swap i k) l))=zpk b; rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) h1, Equiv.swap_apply_right]; rfl
        | succ x=>
          unfold Function.comp σ u i j k l
          simp only [Equiv.trans_apply, Fin.succ_inj, Equiv.swap_apply_of_ne_of_ne, Fin.succ_ne_zero, ne_eq, not_false_eq_true, Fin.cons_succ]
lemma bur_comm (P Q:Matrix A A ℝ)(V:CupA A (r+4))(h:Tensor.Sym V): bur P (bur Q V)=bur Q (bur P V) := by
  ext1 v; rw [bur_eval,bur_eval]; simp_rw [bur_eval, Finset.mul_sum]
  let f (u v' : A×A) := batting r * (P u.1 u.2 * (batting (r+2) * (Q v'.1 v'.2 * V (Fin.cons (zpk v'.1) (Fin.cons (zpk v'.2) (Fin.cons (zpk u.1) (Fin.cons (zpk u.2) v)))))))
  rw [show (∑ i,∑ j,∑ k,∑ l,batting r * (P i j * (batting (r+2) * (Q k l * V (Fin.cons (zpk k) (Fin.cons (zpk l) (Fin.cons (zpk i) (Fin.cons (zpk j) v))))))))=∑ u: A×A,∑ p:A×A,f u p from by simp_rw [Fintype.sum_prod_type]; rfl]
  rw [Finset.sum_comm]; simp_rw [Fintype.sum_prod_type]; refine sum_congr rfl fun i _=>sum_congr rfl fun j _=> sum_congr rfl fun k _=> sum_congr rfl fun l _=>?_
  unfold f; rw [slider _ _ _ _ V h v]; ring

-- Wick layers per ANCHORED symbol, before theory transfer
def terraces (P:Matrix A A ℝ)(V:Cupboard A)(u:ℕ) (r : ℕ) : CupA A r := match u with
    | 0 => V r
    | n+1 => (↑(n+1:ℕ):ℝ)⁻¹ • bur P (terraces P V n (r+2))
def harvestL (P:Matrix A A ℝ)(V:Cupboard A)(L:ℕ)(r:ℕ): CupA A r:= ∑ i∈range (L+1), terraces P V i r
omit [DecidableEq A] in
def Ceils (V:Cupboard A)(L:ℕ) := ∀ i:ℕ,L < i→V i=0
lemma stairs_zeros (P:Matrix A A ℝ)(V:Cupboard A){j r}(n:ℕ)(h:Ceils V j)(he:j< r + 2*n) : terraces P V n r=0:= by
    induction n generalizing r with
    | zero=> rw [terraces,h r (by omega)]
    | succ i ih=> rw [terraces,ih (by omega),bur_home,smul_zero]
lemma stays_ceils (P:Matrix A A ℝ){V:Cupboard A}(h:Ceils V n)(L:ℕ) : Ceils (harvestL P V L) n:= fun i hi=> sum_eq_zero fun j _=> stairs_zeros P _ j h (by omega)
lemma terraces_sym (P:Matrix A A ℝ)(V:Cupboard A)(h:∀ i,Tensor.Sym (V i))(n r : ℕ): Tensor.Sym (terraces P V n r):= by
    induction n generalizing r with
    | zero=> rw [terraces]; exact h _
    | succ i ih=>rw [terraces]; exact fun x y=> congr_arg ((↑(i+1:ℕ):ℝ)⁻¹ • ·) (bur_sym P (ih _) x y)
lemma t_right (P Q:Matrix A A ℝ)(V:Cupboard A)(hv:∀ i,Tensor.Sym (V i)) (n r : ℕ):
    terraces P (fun r=> bur Q (V (r+2))) n r=bur Q (terraces P V n (r+2)):= by
  induction n generalizing r with
  | zero=> simp_rw [terraces]
  | succ n ih=> rw [terraces, ih, bur_comm P Q _ (terraces_sym P V hv n (r+4)),terraces,bur_cust]
lemma t_cost (P:Matrix A A ℝ)(c:ℝ)(V:Cupboard A)(n r): terraces P (c•V) n r=c•terraces P V n r:= by
  induction n generalizing r with
  | zero=> simp_rw [terraces]; rfl
  | succ n ih=> rw [terraces,ih,bur_cust,terraces,smul_comm]
lemma t_collect (P:Matrix A A ℝ)(V:I→ Cupboard A) (S : Finset I)(n r) : terraces P (fun r => ∑ i∈S,V i r) n r=∑ i∈ S, terraces P (V i) n r := by
    induction n generalizing r with
    | zero=> simp_rw [terraces]
    | succ n ih=>simp_rw [terraces]; rw [ih,burs_pledge,Finset.smul_sum]
lemma h_cost (P:Matrix A A ℝ)(c:ℝ)(V:Cupboard A)(n r): harvestL P (c•V) n r=c•harvestL P V n r:= by simp_rw [harvestL,t_cost,Finset.smul_sum]
lemma h_collect (P:Matrix A A ℝ)(V:I→ Cupboard A) (S : Finset I)(n r) : harvestL P (fun r => ∑ i∈S,V i r) n r=∑ i∈ S, harvestL P (V i) n r := by simp_rw [harvestL,t_collect]; exact Finset.sum_comm
lemma terraces_swap (P: Matrix B B ℝ)(M:Matrix A B ℝ)(V:Cupboard A)(n r):
    terraces P (fun r=> twistV M (V r)) n r=twistV M (terraces (M*P*Mᵀ) V n r):= by
    induction n generalizing r with
    | zero=> simp_rw [terraces]
    | succ n ih=> simp_rw [terraces]; rw [ih,bur_turns,twist_cost]
lemma harvest_swap (P: Matrix B B ℝ)(M:Matrix A B ℝ)(V:Cupboard A)(n r):
    harvestL P (fun r=> twistV M (V r)) n r=twistV M (harvestL (M*P*Mᵀ) V n r):= by simp_rw [harvestL,terraces_swap,twist_for]

end YM.RG08.Pivot
