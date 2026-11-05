import YM.Next.MAXWELL.Leading

/-! # Signed shifts and symmetry at adjacent orders -/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory Wick
open scoped ContDiff Topology BigOperators InnerProductSpace ComplexOrder
variable {G : Gauge}

def shift (i a b : Axis) := feed (basis i) 0 (cell a b)

theorem cell_skew (a b : Axis) : cell a b = - cell b a := LinearMap.ext (fun x => cell_change x a b)
theorem cell_center (a : Axis) : cell a a=0 := by
  apply LinearMap.ext; intro u
  change cell a a u = 0
  have h := cell_change u a a; linarith

theorem feeds_first (p : Sheet 1) (x : E4) (a b : Axis) : feed x 0 (cell a b) p=stay (fun _ => x) a b p := by
  change ↑(0 + 1 : ℕ) * p.val a b (Fin.cons x _) = p.val a b _
  rw [Nat.cast_one,one_mul]; congr 1; funext i; fin_cases i; rfl

theorem cell_span : Submodule.span ℝ {x : Flavor 0| ∃ a b : Axis, a<b ∧ x=cell a b}=⊤ := by
  let W := Submodule.span ℝ {x : Flavor 0| ∃ a b : Axis, a<b ∧ x=cell a b}
  have he (a b : Axis) (h : a<b) : cell a b ∈ W := Submodule.subset_span ⟨a,b,h,rfl⟩
  refine eq_top_iff.mpr ?_; rw [← unitStay 0]; apply Submodule.span_le.mpr; rintro t ⟨u,a,b,rfl⟩
  rw [show stay u a b=cell a b from congr_arg (fun u => stay (j:=0) u a b) (Subsingleton.elim ..)]
  rcases lt_trichotomy a b with h|h|h; exact he _ _ h
  · rw [h,cell_center]; exact Submodule.zero_mem W
  rw [cell_skew]; exact Submodule.neg_mem W (he _ _ h)

theorem shift_span : Submodule.span ℝ {x : Flavor 1|∃ i a b : Axis, a<b ∧ x=shift i a b}=⊤ := by
  let W := Submodule.span ℝ {x : Flavor 1|∃ i a b : Axis,a<b ∧ x=shift i a b}
  have he (i a b : Axis) : shift i a b ∈ W := by
    rcases lt_trichotomy a b with h|h|h
    · exact Submodule.subset_span ⟨_,_,_,h,rfl⟩
    · rw [h,shift,cell_center,map_zero]; exact Submodule.zero_mem W
    rw [shift,cell_skew,map_neg]; exact Submodule.neg_mem W (Submodule.subset_span ⟨_,_,_,h,rfl⟩)
  refine eq_top_iff.mpr ?_; rw [← unitStay 1]; apply Submodule.span_le.mpr; rintro t ⟨u,a,b,rfl⟩
  let x := u 0
  rw [show stay u a b=∑ i : Axis,x i • shift i a b from ?_];
  · exact Submodule.sum_mem W fun i _ => Submodule.smul_mem W _ (he _ _ _)
  apply LinearMap.ext; intro q; simp only [LinearMap.sum_apply,LinearMap.smul_apply,shift,feeds_first]
  let F := q.val a b
  let V (i : Axis) : ℝ := stay (j:=1) (fun _ => basis i) a b q
  let L := F.curryLeft
  rw [show stay u a b q = ((L (∑ i : Axis,x i • basis i)) (fun _ => 0)) from ?_]
  · rw [map_sum,sum_apply]; refine Finset.sum_congr rfl fun i _ => ?_; rw [map_smul,smul_apply]
    change x i • F (Fin.cons (basis i) _) = x i • F _
    congr 2; funext i; fin_cases i; rfl
  rw [show ∑ i : Axis, x i • basis i=x by ext j; simp]
  change F u= F _; congr 1; funext i; fin_cases i; rfl

lemma shift_skew (i a b : Axis) : shift i a b = -shift i b a := by unfold shift; rw [cell_skew,map_neg]

lemma shift_mark (p : Sheet 1) (i a b : Axis) : grad i (asWave p a b) 0 = shift i a b p := by
  rw [shift,feeds_first]
  unfold grad D asWave
  rw [differential_diagonal (p.val a b) ((show ClosedJet _ from p.property.1).coeffSym _ _)]
  change (1:ℕ) • _ = _
  rw [one_smul]; change p.val a b _ = p.val a b _
  congr 1; funext j; fin_cases j; rfl

lemma bianchi_shift (a b c : Axis) : shift a b c + shift b c a + shift c a b=0 := by
  apply LinearMap.ext; intro u; simp only [LinearMap.add_apply, ← shift_mark]; exact (wavePoly u).cycle a b c 0 (mem_univ _)

lemma free_shift (a : Axis) : ∑ i : Axis, shift i i a=0 := by
  apply LinearMap.ext; intro u; simp only [LinearMap.sum_apply, ← shift_mark]; exact (wavePoly u).divergence a 0 (mem_univ _)

def tilt (g : Signed) (b : Axis) : ℝ := if g.flip b then -1 else 1

theorem heads (g : Signed) (i : Axis) : Ortho.move g.ortho (basis i) = tilt g i • basis (g.perm i) := by
  rw [ortho_expansion, Finset.sum_eq_single_of_mem (g.perm i) (Finset.mem_univ _)]
  · rw [show g.ortho.val = g.matrix from rfl, Signed.matrix_at,if_pos rfl]; rfl
  intro a h ha; rw [show g.ortho.val = g.matrix from rfl,Signed.matrix_at,if_neg (Ne.symm ha),zero_smul]

lemma tilt_one (g : Signed) (a b : Axis) : actFlavor g.ortho 0 (cell a b) =
    (tilt g a*tilt g b) • cell (g.perm a) (g.perm b) := by
  apply LinearMap.ext; intro u
  let s := g.ortho
  change turnJ s⁻¹ u.val a b _ = _
  rw [turns_apply]
  let Y : Fin 0 → E4 := fun _ => 0
  simp only [inv_entry,show s.val=g.matrix from rfl,Signed.matrix_at]
  -- only pick i = perm a and l=perm b
  rw [Finset.sum_eq_single_of_mem (g.perm a) (Finset.mem_univ _)]
  · rw [Finset.sum_eq_single_of_mem (g.perm b) (Finset.mem_univ _)]
    · have he (x : Fin 0 → E4) : u.val (g.perm a) (g.perm b) x=cell (g.perm a) (g.perm b) u := congr_arg (u.val _ _) (Subsingleton.elim ..)
      simp only [↓reduceIte, he, LinearMap.smul_apply, tilt]
    intro l _ hl; simp [Ne.symm hl]
  intro i _ hi; simp [Ne.symm hi]

lemma step_go (s : Ortho) (p : Flavor 0) (x : E4) : actFlavor s 1 (feed x 0 p)=feed (Ortho.move s x) 0 (actFlavor s 0 p) := by
  ext u; apply congr_arg p; simpa using turn_comp_shift s⁻¹ u (Ortho.move s x)

lemma tilt_step (g : Signed) (i a b : Axis) : actFlavor g.ortho 1 (shift i a b) =
    (tilt g i * tilt g a * tilt g b) • shift (g.perm i) (g.perm a) (g.perm b) := by
  rw [shift,step_go,heads,tilt_one,map_smul]
  have he (x : E4) (a b : Axis) (c : ℝ) : feed (c • x) 0 (cell a b) = c • feed x 0 (cell a b) := by
    apply LinearMap.ext; intro u; change _ = c • feed x 0 (cell a b) u; rw [feeds_first,feeds_first]
    let w := fun _ : Fin 1 => x
    let v := fun _ : Fin 1 => c • x
    change u.val a b v = c • u.val a b w
    rw [show v=update w 0 (c • w 0) by ext1 i; fin_cases i; simp [v,w]]; exact ((u.val a b).map_update_smul w 0 c _).trans (by rw [update_eq_self])
  rw [he,smul_smul]; change _ • shift _ _ _ = _
  congr 1; ring

lemma act_inv_f (s : Ortho) {j : ℕ} (p : Flavor j) : actFlavor s j (actFlavor s⁻¹ j p)=p := by
  apply LinearMap.ext; intro x
  change p (solutionTurn s⁻¹⁻¹ (solutionTurn s⁻¹ x))=_; rw [inv_inv,← solution_rep,mul_inv_cancel, solution_id]

lemma feed_fare (c : G.ColorIndex) (p q : Flavor 0) (i : Axis) {x : E4} (hx : x≠0) :
    fare c (feed (basis i) 0 p) q x=grad i (fare c p q) x := by
  have hh := K_left_D (flavor 0 c p) (flavor 0 c q) hx (basis i)
  rw [← consecutive] at hh
  simp only [K,sub_zero] at hh; exact hh.symm

lemma symmetric_fares00 (c : G.ColorIndex) (p q : Flavor 0) (x : E4) (hx : x≠0) : fare c p q x=fare c q p x := by
  let P := flavor 0 c p
  let Q := flavor 0 c q
  have he := K_symmetric P Q hx
  rw [← K_orientation oppositeFrame.ortho Q P hx.symm, whole_axis,whole_axis,upside_zero,upside_zero] at he
  simp only [K,sub_zero,neg_zero,zero_sub,neg_neg] at he; exact he

lemma shifts_sym (c : G.ColorIndex) (p q : Flavor 0) (i : Axis) {x : E4} (hx : x≠0) :
    fare c (feed (basis i) 0 p) q x=fare c (feed (basis i) 0 q) p x := by
  simp only [feed_fare _ _ _ _ hx]
  exact GermD _ ((show EqOn _ _ away from symmetric_fares00 c p q).eventuallyEq_of_mem (open_away.mem_nhds hx))

lemma cross_seed_ne : basis 0 + basis 2 ≠ 0 := by
  intro h
  have hh := congr_arg (fun x : E4 => x 0) h; simp at hh

lemma cross_seed (c : G.ColorIndex) : fare c (shift 0 0 1) (cell 1 2) (basis 0+basis 2) = -2*normal := by
  rw [shift,feed_fare c _ _ _ cross_seed_ne]
  let p := cell 0 1
  let q := cell 1 2
  let x := basis 0 + basis 2
  have he z (hz : z≠0) : fare c p q z = (8*normal)*(z 0*z 2)*(‖z‖^2)⁻¹^3 := by
    rw [show fare c p q z=K (omegaLeg c 0 1) (omegaLeg c 1 2) z 0 by rw [K,sub_zero]; rfl,omega_K_eq _ _ _ _ _ _ hz,if_pos rfl,sub_zero,bareCurl, Pi.sub_apply]
    rw [Bare.opp_grad hz, Bare.opp_grad hz]; simp [Axis, second_Green hz]
  let L := fun z : E4 => (8*normal)*(z 0*z 2)*(‖z‖^2)⁻¹^3
  rw [grad,GermD (basis 0) ((show EqOn _ L away from he).eventuallyEq_of_mem (open_away.mem_nhds (show x∈away from cross_seed_ne)))]
  have hx : ‖x‖^2=(2:ℝ) := by rw [EuclideanSpace.real_norm_sq_eq]; simp [Axis,x,Fin.sum_univ_four]; norm_num
  have h := ((((compAxis 0).hasFDerivAt (x:=x)).mul (compAxis 2).hasFDerivAt).const_mul (8*normal)).mul
    (((hasFDerivAt_inv (show ‖x‖^2 ≠ 0 by rw [hx]; norm_num)).comp x
      (hasStrictFDerivAt_norm_sq x).hasFDerivAt).pow 3)
  have ht := h.fderiv
  change fderiv ℝ L x = _ at ht
  change fderiv ℝ L x (basis 0)=_
  rw [ht]
  simp [two_smul, -basis_eq, compAxis, hx]
  rw [← real_inner_comm x, basis_inner]; simp [Axis,x]; ring
end YM.Maxwell.Free
