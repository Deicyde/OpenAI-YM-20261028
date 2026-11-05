import YM.Extra.WILSON_STARTUP.Residual
import YM.Next.FOUNDATIONS.Regular

/-! # Startup estimates on actual faces -/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonStartup
open Function Filter Work Tensor Next.Fluctuations Lattice Wilson RG
open scoped ContDiff Topology Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {n : Side}

abbrev Cell (n : Side) := Face (Per n)
abbrev Bond (n : Side) := Edge (Site n)

def edges (p : Cell n) : Fin 4 → Bond n :=
  let i := p.2.val.1; let j := p.2.val.2
  ![(p.1,i), (p.1+step i,j), (p.1+step j,i), (p.1,j)]

lemma four_visit (p : Cell n) : touched p = {p.1, p.1+step p.2.val.1, p.1+step p.2.val.1+step p.2.val.2, p.1+step p.2.val.2} := by
  simp only [touched,visits,square,Step.vec_pos,Step.vec_neg,
    add_right_comm (b:=step p.2.val.1) (c:=step p.2.val.2), add_neg_cancel_right]
  ext y
  simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,Finset.mem_insert,Finset.mem_singleton]; tauto

lemma touched_card (p : Cell n) : (touched p).card ≤ 4 := by
  rw [four_visit]; refine (Finset.card_insert_le ..).trans ?_; refine Nat.succ_le_succ ((Finset.card_insert_le ..).trans ?_)
  exact Nat.succ_le_succ (Finset.card_le_two ..)

lemma anchor_visit (p : Cell n) : p.1 ∈ touched p := by rw [four_visit]; exact Finset.mem_insert_self ..

lemma visit_near (p : Cell n) {y : Site n} (h : y ∈ touched p) : separation y p.1 ≤ 2 := by
  rw [four_visit] at h
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  have hs (i : Axis) : separation (p.1+step i) p.1 ≤ 1 := by simpa [separation, add_comm p.1] using pdist_step (n:=n) i
  rcases h with rfl|rfl|rfl|rfl
  · simp
  · exact (hs _).trans (by omega)
  · simpa only [separation,show p.1+step p.2.val.1+step p.2.val.2 - p.1 = step p.2.val.1+step p.2.val.2 by abel] using
      (pdist_triangle (n:=n) (step p.2.val.1) (step p.2.val.2)).trans (Nat.add_le_add (pdist_step _) (pdist_step _))
  exact (hs _).trans (by omega)

lemma edges_visit (p : Cell n) (i : Fin 4) : (edges p i).1 ∈ touched p := by
  rw [four_visit]; fin_cases i <;> simp [edges]

lemma face_one (p : Cell n) : faceValue (1 : Config G n) p = 1 := by
  rw [← Precision.link_one (G:=G) (n:=n)]; exact Push.stroll_zero ..

lemma read_edges (p : Cell n) (U : Config G n) : Quad.read (U ∘ edges p) = faceValue U p := by

  simp only [faceValue, square,travel,Step.pos_read, Step.neg_read,Step.vec_pos, Step.vec_neg,
      show p.1 + step p.2.val.1 + step p.2.val.2 - step p.2.val.1 = p.1 + step p.2.val.2 by abel,
      show p.1 + step p.2.val.1 + step p.2.val.2 + (-step p.2.val.1) = p.1 + step p.2.val.2 by abel,add_sub_cancel_right]
  simp [Quad.read,edges,mul_assoc]

variable (G)

def residual (p : Cell n) (U : Config G n) := surplus (faceValue U p)

variable {G}

theorem residual_jet (p : Cell n) (U : Config G n) (l : List (Directions G n)) :
    leftDerivs (residual G p) l U = Quad.jet (l.map (· ∘ edges p)) (Quad.mat (U ∘ edges p)) := by
  induction l generalizing U with
  | nil => rw [leftDerivs, List.map_nil, Quad.jet, comp_apply, Quad.read_actual, Quad.surplus_actual, read_edges]; rfl
  | cons a l ih =>
    simp only [leftDerivs, List.map_cons, ih, Quad.jet]
    exact congr_arg (deriv · 0) (funext fun t => congr_arg _ (funext fun i : Fin 4 => G.mat_mul ..))

theorem healthy_chord (p : Cell n) (U : Config G n) {t : ℝ} (h : Healthy t (touched p) U) :
    G.chord (faceValue U p) ≤ t := by
  by_contra! hh
  have hp := anchor_visit p
  exact Finset.disjoint_left.mp h hp ((flags_spec ..).mpr ⟨_,hp,hh⟩)

theorem residual_price (G : Gauge) (k P : ℕ) : ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ δ ≤ 1 ∧
    ∀ (b : BudgetPoint), b.power = P → b.order = k → b.threshold ≤ δ → ∀ (n : Side) (p : Cell n) (o : Site n),
      o ∈ touched p → b.supBounds o (touched p) (residual G p) (C*b.threshold^5) := by
  let J := Fin (k+1)
  choose c d hc hd h' h using fun i : J => Quad.small_jet G i.val ((1+4)^P)
  obtain ⟨i,hi,he⟩ := Finset.exists_min_image Finset.univ d Finset.univ_nonempty
  let C := 1 + ∑ j : J, c j
  have hC : 0 < C := add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun i _ => (hc i).le)
  refine ⟨C,d i,hC, hd i, h' i, fun b hb hk ht n p o ho => ⟨mul_nonneg hC.le (pow_nonneg b.threshold_pos.le _),?_⟩⟩
  intro U hu l hl hA
  rw [hk] at hl
  let j : J := ⟨l.length, Nat.lt_succ_of_le hl⟩
  let a (i : Fin j.val) := l.get i ∘ edges p
  have ha : ‖a‖ ≤ b.threshold*(1+4:ℝ)^P := by
    have hh := b.threshold_pos
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro s
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro f
    apply ((hA _ (l.get_mem s)) (edges p f)).trans
    rw [hb]; gcongr
    exact_mod_cast (separation_triangle (edges p f).1 p.1 o).trans (Nat.add_le_add (visit_near p (edges_visit p f))
      ((separation_comm _ _) ▸ visit_near p ho))
  have H := h j (U ∘ edges p) a _ b.threshold_pos (ht.trans (he j (Finset.mem_univ j))) ha ((read_edges p U).symm ▸ healthy_chord p U hu)
  have hcj : c j ≤ C := (Finset.single_le_sum (fun i _ => (hc i).le) (Finset.mem_univ j)).trans
    (le_add_of_nonneg_left zero_le_one)
  rw [residual_jet, ← show List.ofFn a = l.map (· ∘ edges p) from (List.map_ofFn (g:=(· ∘ edges p)) (f:=l.get)).symm.trans (by rw [List.ofFn_get])]
  exact H.trans (mul_le_mul_of_nonneg_right hcj (pow_nonneg b.threshold_pos.le _))

theorem mat_face_inc (p : Cell n) (U : Config G n) :
    ContDiff ℝ ω fun v => G.mat (faceValue (increment U v) p) := by
  simp_rw [← read_edges,← Quad.read_actual]
  refine Quad.readMat_diff.comp (contDiff_pi.mpr fun i => ?_)
  simp only [Quad.mat,comp_apply, increment, G.mat_mul]
  exact (G.exp_jet.comp (contDiff_apply ..)).mul contDiff_const

theorem residual_smooth (p : Cell n) (U : Config G n) : ContDiff ℝ ω (residual G p ∘ increment U) := by
  simp_rw [comp_def, residual, ← Quad.surplus_actual]
  exact Quad.surplusMat_diff.comp (mat_face_inc ..)

theorem surplus_conjugate (u v : G.El) : surplus (u*v*u⁻¹) = surplus v := by
  unfold surplus diagonal
  rw [G.curvature_conjugate, G.price_conj, G.norm_adjoint, fourth,coeff_adjoint]

theorem surplus_inv (v : G.El) : surplus v⁻¹ = surplus v := by
  unfold surplus
  rw [G.curvature_inv,G.price_inv,norm_neg,← neg_one_smul ℝ _,homogeneous]
  norm_num [fourth]

lemma face_local (p : Cell n) : LocalOn (touched p) (fun U : Config G n => faceValue U p) :=
    fun U V h => travel_local _ _ U V (fun e he hm => h e (List.mem_toFinset.mpr he) (List.mem_toFinset.mpr hm))

theorem residual_regular (p : Cell n) (b : BudgetPoint) : b.Regular (touched p) (residual G p) := by
  have h (U : Config G n) := ((residual_smooth p U).of_le (m:=(b.order:ℕ∞)) le_top).contDiffAt (x:=0)
  refine ⟨fun U V h => congr_arg surplus (face_local p U V h), Continuous.measurable ?_, ?_,fun U _ => h U,
    fun U _ a l hl => Next.Foundations.left_has a hl (h U)⟩
  · change Continuous fun U => residual G p U
    simp only [residual,← Quad.surplus_actual]; exact Quad.surplusMat_diff.continuous.comp
      (G.continuous_mat.comp (continuous_travel ..))
  intro k U; exact (congr_arg surplus (face_gauge k U p)).trans (surplus_conjugate ..)

theorem residual_flat (p : Cell n) : FlatAt 5 (residual G p ∘ increment 1) 0 := by
  refine surplus_jet (fun v => faceValue (increment 1 v) p) ?_ (mat_face_inc .. |>.contDiffAt)
  rw [Work.G07.at_zero_increment,face_one]

theorem residual_one (p : Cell n) : residual G p 1 = 0 := by
  have h := congr_arg (Tensor.diagonal · (0:Directions G n)) (residual_flat p 0 (by omega))
  simpa [Tensor.diagonal,comp_def,G07.at_zero_increment] using! h

theorem residual_hess (p : Cell n) (x y : Directions G n) : logHessian (residual G p) x y = 0 :=
  congr_arg (fun u : Tensor.T (Directions G n) ℝ 2 => u ![x,y]) (residual_flat p 2 (by omega))

theorem residual_send (p : Cell n) (s : Signed) (x : Site n) (U : Config G n) :
    residual G (Face.send s x p) U = residual G p (pull s x U) :=
  (Face.send_price U p s x surplus surplus_inv (fun v u => surplus_conjugate u v)).symm
end YM.WilsonStartup
