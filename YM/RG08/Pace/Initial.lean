import YM.RG08.Pace.Hush
import YM.RG08.Gaussian.TreeInverse
import YM.RG08.Gaussian.Regroup
import YM.RG08.Ballast.Jets
import YM.RG08.Ballast.Ribbons

/-! # Input/output quadratic at the fixed point convention -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG Laurent Lattice Wilson Exterior Precision Bloch Next.Free Push.AbsoluteSums Finset Function Filter
open Stationary UVExt.Paths Matrix
open scoped Topology ContDiff
variable {α : Type} {w τ C A B : ℝ} {G : Gauge} {r n : ℕ} {m : Side}

-- avoid a score with width cost if symmetric
private def octoRaw {α : Type} (z : α) (b : Cover×α) : Beads α 2 := ![(0,z),b]
private def octo {α : Type} (R : Row α α) (z : α) := pool (fun i : Cover×α=> R z i.2 i.1) (octoRaw z)
def clipQ {α : Type} [Fintype α] (R : Row α α) : Shale α 2 := ((1/2:ℝ) • ∑ i,octo R i)
def quad (G : Gauge) (M : KRow) := clipQ (colored G M)
private lemma octo_price [Fintype α] (R : Row α α) (z : α) (hs : R.strip w A) : Charge
    (fun x : Cover×α => ling w (octoRaw z x)) (fun i=> R z i.2 i.1) (Fintype.card α*A) := by
  have he x : ling w (octoRaw z x)=Real.exp (w*size x.1) := by
    unfold ling girth; rw [Fin.sum_univ_two]; simp [octoRaw,size]
  unfold Charge; simp_rw [he]; exact row_fitter hs z
private lemma octo_sub [Fintype α] (R S : Row α α) (z : α) (hs : Whole R) (hh : Whole S) :
    octo (R-S) z= octo R z- octo S z := by
  obtain ⟨w,C,hp,h⟩ := hs; obtain ⟨σ,D,hq,h'⟩ := hh
  exact pool_minus (octoRaw z) ((octo_price R z h).summable (fun i=> ling_one hp.le _)) ((octo_price S z h').summable (fun i=> ling_one hq.le _))
private lemma sym_pair_hits (s : Equiv.Perm (Fin 2)) : s=Equiv.refl _ ∨ s=Equiv.swap 0 1 := by decide +revert
lemma clipQ_tunable [Fintype α] (R : Row α α) (h : R.strip w C) (hw : 0 ≤ w) (he : ∀ c, (R.acts c)ᵀ=R.acts c) :
    Glow (clipQ R) w (‖(1/2 : ℝ)‖*((Fintype.card α)*(Fintype.card α*C))) ∧ Tunable (clipQ R) ∧
    ∀ m (v : Fin 2 → PAC α m), recital (clipQ R) m v= (1/2:ℝ)*(dotProduct (v 0) ((R.acts m)*ᵥ v 1)) := by
  have hv (z : α) := (octo_price R z h).summable (fun i=> ling_one hw (octoRaw _ i))
  have hh (i : α) : Glow (octo R i) w (Fintype.card α*C) := Charge.poolage (octoRaw i) (ling_one hw) (octo_price R i h)
  have hx := Charge.sums (w:=ling w) (fun i => (ling_pos _ _).le) (s:=univ) (fun i _=> hh i)
  have ha : Glow (clipQ R) w (‖(1/2:ℝ)‖*((Fintype.card α)*(Fintype.card α*C))) := by
    simp only [sum_const,card_univ,nsmul_eq_mul] at hx; exact hx.scale _
  have ht (m : Side) (v : Fin 2→PAC α m) : recital (clipQ R) m v= (1/2:ℝ)*(dotProduct (v 0) (R.acts m*ᵥ v 1)) := by
    rw [clipQ,recital_scale _ (hx.summable (ling_one hw)),recital_sum _ _ (fun i _=> (hh i).summable (ling_one hw)),_root_.smul_apply,_root_.sum_apply,smul_eq_mul]
    congr 1; unfold dotProduct octo; rw [Fintype.sum_prod_type,sum_comm]; apply sum_congr rfl; intro i _
    rw [recital_pool _ (hv i)]; apply sum_congr rfl; intro z _; rw [row_expand h hw, ← tsum_mul_left]; apply tsum_congr; intro b; unfold rosary; rw [Fin.prod_univ_two]; simp [silks,octoRaw]; ring
  refine ⟨ha,⟨ha.summable (ling_one hw),?_,fun m v s=>?_⟩,ht⟩
  · intro i hi; by_contra hy; apply hi
    have he z : octo R z i=0 := pool_eq_zero _ (fun j hj=> (hy (by rw [← hj]; exact rfl)).elim)
    simp [clipQ,Finset.sum_apply,he]
  rw [ht,ht]; rcases sym_pair_hits s with hS | hS
  · rw [hS]; rfl
  rw [hS]; congr 1; change dotProduct (v 1) _=dotProduct (v 0) _
  change dotProduct (v 1) (R.acts m*ᵥ v 0)=_
  rw [Matrix.dotProduct_mulVec,← Matrix.mulVec_transpose,he,dotProduct_comm]

lemma quad_matches (G : Gauge) (M : KRow) (h : M.strip w C) (hw : 0 ≤ w) (he : ∀ c, (M.acts c)ᵀ=M.acts c) :
    let Q := quad G M
    Glow Q w (‖(1/2 : ℝ)‖*((Fintype.card (Loc G 1))*(Fintype.card (Loc G 1)*C))) ∧ Tunable Q ∧
    ∀ m (u v : PAC (Loc G 1) m), iteratedFDeriv ℝ 2 (stanza Q m) 0 ![u,v]= ∑ i,
        parts G 1 (arm G m 1 u) i ⬝ᵥ ((M.acts m) *ᵥ parts G 1 (arm G m 1 v) i) := by
  intro Q
  obtain ⟨hh,hQ,H⟩ := clipQ_tunable (colored G M) (colored_price G h) hw fun c=> by rw [colored_acts,FreeResolvent.tensor_transpose,he]
  refine ⟨hh,hQ,fun m u v=>?_⟩
  have hz : (1/2:ℝ)*iteratedFDeriv ℝ 2 (stanza Q m) 0 ![u,v]=(1/2:ℝ)*dotProduct u (FreeResolvent.tensor G (M.acts m) *ᵥ v) := by
    have he := (DFunLike.congr_fun (Tunable.pick hQ m) ![u,v]).trans (H m _)
    norm_num [Tensor.coeff,Nat.factorial, colored_acts] at *; exact he
  have he t : FreeResolvent.component u t ⬝ᵥ FreeResolvent.component (FreeResolvent.tensor G (M.acts m)*ᵥv) t = _ := (show _=parts G 1 (arm G m 1 u) t ⬝ᵥ ((M.acts m) *ᵥ parts G 1 (arm G m 1 v) t) by rw [FreeResolvent.component_mul]; rfl)
  rw [FreeResolvent.component_dot] at hz; simp_rw [he] at hz; exact mul_left_cancel₀ (by norm_num : (1/2 : ℝ)≠0) hz
lemma quad_sub (G : Gauge) {M N : KRow} (h : Whole M) (e : Whole N) :
    quad G (M-N)=quad G M-quad G N := by
  rw [show quad G (_-_) = clipQ (colored G M-colored G N) from ?_]; swap
  · unfold quad; congr 1; funext i j x; by_cases hi : i.2=j.2 <;> simp [colored,hi]
  unfold quad clipQ; simp_rw [octo_sub _ _ _ (colored_whole _ h) (colored_whole _ e),sum_sub_distrib]; rw [smul_sub]

lemma marked_units {G : Gauge} (i : G.ColorIndex) (B : FaceRow) (h : Whole B) (hv : ∀ m, (B.acts m)ᵀ=B.acts m)
    (hs : B.read 0=1) : probeK i (quad G (hessian B))=1 := by
  obtain ⟨w,C,hp,hG⟩ := hessian_whole h
  let r := quad G (hessian B)
  obtain ⟨hc,hR,H⟩ := quad_matches G (hessian B) hG hp.le fun m=> by rw [hessian_acts h]; exact k_symmetric (hv m)
  have ha (m) : Recorded (slots B G) (stanza r m) 0 := by
    apply according h.safe; intro p q; rw [← hessian_acts h]; exact H m p q
  have he (b r₀) (p : Corn (Keys 1)) : gallery r b r₀ (axes p)=slots B G b r₀ (axes p) := by
    let m (i : ℕ) : Side := ⟨i+1,Nat.succ_pos _⟩
    obtain ⟨P,V,H,e⟩ := fleet m (tendsto_add_atTop_nat _) (axes p) (axes_real p)
    obtain ⟨s,D,hp',ht⟩ := h
    refine tendsto_nhds_unique (harvest (f:=gallery r) (gallery_funds hc hp) (F:=fun i=>stanza r (m i)) (ε:=fun _=>0) (fun i=> ?_) tendsto_const_nhds p P V H e b r₀)
      (harvest (slots_cost hp' ht) (F:=fun i=>stanza r (m i)) (ε:=fun _=>0) (fun i => by simp only [mul_zero]; exact ha _) tendsto_const_nhds p P V H e b r₀)
    rw [mul_zero]; exact gallery_marks hR (hR.pick (m i))
  have hl : leapTip (gallery r) (step (0:Axis)) 1 ![i,i]=leapTip (slots B G) (step (0:Axis)) 1 ![i,i] := by
    have ht : pressLens (gallery r) ![i,i] 1 1=pressLens (slots B G) ![i,i] 1 1 := funext fun _ => he ..
    rw [leapTip,ht]; rfl
  obtain ⟨v,D,hb,Hv⟩ := h
  change alphaPay _ (gallery r)=_; rw [alphaPay,hl,tip_fuel i Hv hb hs]; norm_num
end YM.RG08
