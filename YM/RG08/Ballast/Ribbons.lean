import YM.RG08.Ballast.Grapes

/-! # Row substitution does not forget the lifted positions -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG Laurent Lattice Wilson Bloch Next.Free Work.F08 Push.AbsoluteSums Finset Function
open UVExt.Paths Stationary Matrix
open scoped Topology ContDiff Classical
variable {α β ι : Type} {r : ℕ} {w η C A B : ℝ} {L c f : Side}

lemma budget_fin_prod (p : Fin r → ℝ) {X : Fin r → ι → ℝ} (h : ∀ i, SumBudget (X i) (p i)) :
    SumBudget (fun v : Fin r → ι => ∏ i,X i (v i)) (∏ i, p i) := by
  induction r with
  | zero => refine budget_finite (fun _ => by simp) (by simp)
  | succ r ih =>
    let Z := Fin.consEquiv (fun _ : Fin (r+1) => ι)
    have hx v : Z.symm v=(v 0,fun i => v i.succ) := by apply Z.injective; rw [Z.apply_symm_apply]; ext i; refine Fin.cases ?_ (fun j=>?_) i <;> rfl
    have hu := budget_pull Z.symm Z.symm.injective (budget_prod (h 0) (ih _ (fun i=> h i.succ)))
    simp only [hx] at hu; simp_rw [Fin.prod_univ_succ (n:=r)]; exact hu -- cost product simp again?
lemma tsum_fin_prod (p : Fin r → ι → ℝ) (hp : ∀ i,Summable (p i)) :
    ∑' b : Fin r→ι, (∏ i, p i (b i))=∏ i, ∑' j,p i j := by
  induction r with
  | zero => simp [tsum_fintype]
  | succ r ih =>
    let f (i : Fin r → ι) := (∏ j,p j.succ (i j))
    have hh (i : Fin r) : SumBudget (fun j => ‖p i.succ j‖) (∑' j, ‖p i.succ j‖) := ⟨fun _=> norm_nonneg _, (hp _).norm,le_rfl⟩
    have he : Summable (fun i => ‖f i‖) := by
      have hx := budget_fin_prod _ hh; simp_rw [f,norm_prod]; exact hx.2.1
    let Z := Fin.consEquiv (fun _ : Fin (r+1) => ι)
    rw [← Z.tsum_eq]; simp_rw [Fin.prod_univ_succ (n:=r)]; rw [← ih (fun i => p i.succ) (fun i => hp i.succ)]
    exact (tsum_mul_tsum_of_summable_norm (hp 0).norm he).symm

variable [Fintype β]
lemma row_fitter {T : Row α β} (h : T.strip w A) (x : α) : SumBudget
    (fun i : Cover × β => Real.exp (w*size i.1)*‖T x i.2 i.1‖) (Fintype.card β*A) := by
  have hb (i : β) := h x i
  let f (b : β × Cover) := Real.exp (w*size b.2)*‖T x b.1 b.2‖
  have hg : Summable f := (summable_prod_of_nonneg (fun i=> (h x i.1).1 i.2)).mpr ⟨fun i => (h x i).2.1,.of_finite⟩
  let E := Equiv.prodComm Cover β
  apply budget_pull E E.injective (w:=f) ⟨fun i=>(h x _).1 i.2,hg,?_⟩
  rw [hg.tsum_prod,tsum_fintype]
  simpa using sum_le_sum (s:=univ) (f:=fun i : β => ∑' j,f (i,j)) (fun i _=> (h x i).2.2)
lemma row_money {T : Row α β} (h : T.strip w A) (hv : 0≤w) (x : α) (v : PAC β c) z :
    Summable (fun i : Cover × β => T x i.2 i.1*v (z+wrap c i.1,i.2)) := by
  have hh : Charge (fun i : Cover×β=> Real.exp (w*size i.1)) (fun i=> T x i.2 i.1) (Fintype.card β*A) := row_fitter h x
  exact sum_bounded (hh.summable (fun i=> Real.one_le_exp (by positivity))) (fun _=> norm_le_pi_norm v _)
lemma row_expand {T : Row α β} (h : T.strip w A) (hv : 0≤w) (x : α) (v : PAC β c) z :
    (T.acts c *ᵥ v) (z,x)=∑' i : Cover × β, T x i.2 i.1*v (z+wrap c i.1,i.2) := by
  let t (j : Cover×β) := T x j.2 j.1*v (z+wrap c j.1,j.2)
  have hr : Summable (fun i : β × Cover => t (i.2,i.1)) := (show Summable t from row_money h hv x v z).prod_symm
  rw [← (Equiv.prodComm β Cover).tsum_eq (f:=t)]; change _=∑' i:β×Cover, t (i.2,i.1); rw [show ∑' i:β×Cover, t (i.2,i.1)=_ from hr.tsum_prod,tsum_fintype]; unfold Matrix.mulVec dotProduct; rw [Fintype.sum_prod_type,sum_comm]
  exact sum_congr rfl fun i _ => sift_action ((h x i).summable hv) c z (fun j => v (j,i))

def flicker (K : Fin r → Row α β) (i : Beads α r × Beads β r) := ∏ j, K j (i.1 j).2 (i.2 j).2 (i.2 j).1
def fieldsAt (i : Beads α r × Beads β r) (j : Fin r) : Cover × β := ((i.1 j).1+(i.2 j).1,(i.2 j).2)
def ribbon (F : Shale α r) (K : Fin r→Row α β) : Shale β r := pool (leads F (flicker K)) fieldsAt

theorem grow_cost (F : Shale α r) (K : Fin r→Row α β) {p : Fin r→ℝ}
    (h : Glow F w C) (hv : 0≤w) (hh : ∀ i, 0≤p i) (hk : ∀ i, (K i).strip w (p i)) :
    Charge (fun i=> ling w (fieldsAt i)) (leads F (flicker K)) (((Fintype.card β:ℝ)^r*∏ i,p i)*C) := by
  apply leads_cost _ h; swap; · exact mul_nonneg (by positivity) (prod_nonneg (fun i _=> hh i))
  intro i
  have he := budget_fin_prod _ fun j => row_fitter (hk j) (i j).2
  simp only [Finset.prod_mul_distrib,prod_const,card_univ,Fintype.card_fin] at he
  rw [mul_comm _ (ling w i)]
  apply budget_mono (budget_scale (ling_pos w i).le he) (fun j => mul_nonneg (ling_pos _ _).le (norm_nonneg _)); intro b
  rw [flicker, norm_prod, ling_as (fieldsAt _)]
  exact (mul_le_mul_of_nonneg_right (ling_bead_sum _ i (fun j => (b j).1) hv) (prod_nonneg fun _ _=> norm_nonneg _)).trans_eq (mul_assoc ..)
theorem ribbon_price (F : Shale α r) (K : Fin r→Row α β) {p : Fin r→ℝ}
    (h : Glow F w C) (hv : 0≤w) (hh : ∀ i, 0≤p i) (hk : ∀ i, (K i).strip w (p i)) :
    Glow (ribbon F K) w (((Fintype.card β:ℝ)^r*∏ i,p i)*C) :=
  Charge.poolage fieldsAt (ling_one hv) (grow_cost _ _ h hv hh hk)
lemma strands [Fintype α] (F : Shale α r) (K : Fin r→Row α β) {p : Fin r→ℝ}
    (h : Glow F w C) (hv : 0≤w) (hh : ∀ i, 0≤p i) (hk : ∀ i, (K i).strip w (p i)) (c : Side) (v : Fin r → PAC β c) :
    recital (ribbon F K) c v= recital F c (fun i => (K i).acts c *ᵥ v i) := by
  have hh := (grow_cost F K h hv hh hk).summable (fun i=> ling_one hv (fieldsAt i))
  rw [ribbon,recital_pool _ hh,recital_eval _ (h.summable (ling_one hv))]; refine sum_congr rfl fun z _ => ?_
  have he := sum_bounded hh (g:=fun i=> rosary v z (fieldsAt i)) (fun i => rosary_bill v _ _)
  rw [he.tsum_prod]; apply tsum_congr; intro i
  unfold rosary silks; dsimp only; simp_rw [row_expand (hk _) hv]; rw [← tsum_fin_prod _ (fun j=>row_money (hk j) hv _ _ _),← tsum_mul_left]; apply tsum_congr; intro j
  rw [leads,flicker,mul_assoc, Finset.prod_mul_distrib]; congr 2; exact prod_congr rfl fun k _=> by simp only [fieldsAt,map_add,add_assoc]
end YM.RG08
