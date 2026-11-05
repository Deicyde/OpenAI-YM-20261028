import YM.Pressure.Route
import YM.Pressure.Single
import YM.RG.History


/-!
# Macro accounting helpers
-/
set_option autoImplicit false
noncomputable section
namespace YM.Pressure
open Filter Function Lattice RG RG.Patch Axial Wilson Finset YM.Branch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators NNReal
variable {G : Gauge}

lemma spread (X Y : Finset Cover) (v : Cover) (hv : X.image (·+v) ⊆ Y) (U : CoverConfig G) :
    edges X (translate v U) ≤ edges Y U ∧ faces X (translate v U) ≤ faces Y U := by
  have h (i) (hi : i ∈ X) : i+v∈Y:=hv (mem_image_of_mem _ hi)
  have H (f : Cover → ℝ) (hf : ∀ i, 0≤f i) : (∑ i∈ X,f (i+v)) ≤ ∑ i∈Y, f i := by
    rw [← show ∑ i∈(X.image (·+v)), f i = _ from Finset.sum_image (by simp)]
    exact Finset.sum_le_sum_of_subset_of_nonneg hv fun i _ _ => hf i
  constructor
  · apply le_trans _ (H (fun i => ∑ k, perEdge Y U i k) (fun i => sum_nonneg fun k _ => per_nn ..))
    refine Finset.sum_le_sum fun i hi ↦ Finset.sum_le_sum fun k _ ↦ ?_
    unfold perEdge; split_ifs with ha hb hb
    · rfl
    · exact False.elim (hb (by rw [add_right_comm]; exact h _ ha))
    · exact G.chord_nonneg _
    rfl
  apply le_trans _ (H (field Y U) fun i => field_nonneg ..)
  apply Finset.sum_le_sum; intro i hi; apply Finset.sum_le_sum; intro k _
  unfold face; split
  next ha =>
    rw [if_pos ?_]
    · apply le_of_eq; unfold faceValue; rw [← pull_one v U,travel_pull]; simp [affine]
    simp only [square_corners,List.mem_cons,List.not_mem_nil,or_false] at *
    intro a e; rcases e with rfl|rfl|rfl|rfl|rfl
    · exact h i hi
    · rw [add_right_comm]; exact h _ (ha _ (by simp))
    · rw [add_right_comm i,add_right_comm (i+_ : Cover)]; exact h _ (ha _ (by simp))
    · rw [add_right_comm]; exact h _ (ha _ (by simp))
    exact h i hi
  exact face_nonneg Y U _ _

-- selector size: exchange first & conditional count ignoring collisions.
lemma box_length (i : ℕ) : (box i).card=(layers i).card^4 := by simp [box, Pi.card_Icc, layers, Axis]

lemma light (P : Patch) (x : P.Points) : P.weight x*(P.L.val:ℝ)^4 ≤ 1 := by
  classical
  let k := P.J-1
  have he : k+1=P.J := Nat.sub_add_cancel (by have := P.order_cut; omega)
  have hh : 2*(P.L.val/2)+1=P.L.val := by have h := P.odd_side; obtain ⟨u,hu⟩ := h; omega
  let f : (Fin (k+1) → P.Small) ≃ P.Rolls := Equiv.arrowCongr (finCongr he) (Equiv.refl P.Small)
  let l : P.Rolls ≃ P.Small×(Fin k → P.Small) := f.symm.trans (Fin.consEquiv
   _).symm
  have h (i : P.Small) (z : Fin k → P.Small) : (P.addRoll (l.symm (i,z))).val=i.val+∑ t : Fin k,(z t).val := by
    change ∑ t : Fin P.J, _ = _
    rw [← Equiv.sum_comp (finCongr he),Fin.sum_univ_succ]
    simp [l, f]
  let C : ℝ := Fintype.card P.Rolls
  let G (i : P.Small) (z : Fin k → P.Small) := if P.addRoll (l.symm (i,z))=x then C⁻¹ else 0
  have hN : 0<C := by unfold C; exact_mod_cast Fintype.card_pos
  have hv (z) : ∑ i, G i z ≤ C⁻¹ := by
    by_cases hx : ∃ i, P.addRoll (l.symm (i,z))=x
    · obtain ⟨i,hi⟩ := hx
      rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
      · unfold G; rw [if_pos hi]
      intro j hj he; apply if_neg; intro hw
      have hp := congr_arg Subtype.val (hw.trans hi.symm); rw [h,h, add_left_inj] at hp
      exact he (Subtype.ext hp)
    push Not at hx; simp [G,hx,hN.le]
  have ha : Fintype.card P.Small=P.L.val^4 := by rw [Fintype.card_coe, box_length,card_layers,hh]
  let M : ℝ := Fintype.card (Fin k → P.Small)
  have ht : C=(P.L.val:ℝ)^4*M := by
    unfold C; rw [Fintype.card_congr l,Fintype.card_prod,ha]; push_cast; rfl
  unfold Patch.weight; rw [← Equiv.sum_comp l.symm, Fintype.sum_prod_type, Finset.sum_comm]
  apply le_trans (mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun i _ => hv i) (by positivity))
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; change M*C⁻¹*_ ≤ _
  rw [mul_right_comm,mul_comm M,← ht]; rw [mul_inv_cancel₀ hN.ne']

lemma traverse (j : Axis) (P : Patch) (U : CoverConfig G) (d : ℕ) (v : Cover) (X : Finset Cover) (h : ∀ k : ℕ, k ≤ d →
    ∀ x ∈ P.sites, x+v+k • step j ∈ X) :
    (∑ x : P.Points,G.chord (travel U (x.val+v) (straight j d))) ≤ d*edges X U := by
  induction d with
  | zero => simp [straight, travel]
  | succ d ih =>
    simp_rw [Nat.cast_add_one,carry_succ,natCast_zsmul]
    refine (Finset.sum_le_sum fun i _ => G.chord_triangle _ _).trans ?_
    rw [sum_add_distrib, add_mul, one_mul]; apply add_le_add (ih fun k hk => h k (by omega))
    have he := fun (x : P.Points) => h d (by omega) x.val x.property
    let f (x : P.Points) := x.val+v+d • step j
    have hr : Injective f := fun i k he => by simp [f] at he; exact he
    calc
      _ = ∑ x ∈ Finset.univ.image f, perEdge X U x j := by
        rw [sum_image hr.injOn]; unfold perEdge
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [if_pos ?_]; unfold f
        rw [add_assoc (i.val+v), ← succ_nsmul]; exact h (d+1) le_rfl _ i.property
      _ ≤ ∑ x ∈ X, perEdge X U x j := Finset.sum_le_sum_of_subset_of_nonneg (by intro i hi; obtain ⟨v,-,rfl⟩ := Finset.mem_image.mp hi; exact he v) (fun i _ _ => per_nn ..)
      _ ≤ _ := Finset.sum_le_sum fun i _ => single_le_sum (f:=fun k => perEdge X U i k) (fun k _ => per_nn ..) (mem_univ j)

lemma price_query (P : Patch) (K : KernelChoices) (Y : P.Connector G) (t : P.Points) (x y : G.El) :
    G.chord (x⁻¹ * P.predict K Y t * y) ≤ 2*max 1 K.predictor_cut⁻¹ * ∑ i,P.weight i * G.chord (x⁻¹*Y i*y) := by
  classical
  let m := ∑ i, P.weight i • G.mat (Y i)
  have hi : 0 ≤ ∑ i, P.weight i * G.chord (x⁻¹*Y i*y) := Finset.sum_nonneg fun _ _ ↦ mul_nonneg (P.weight_nonneg _) (G.chord_nonneg _)
  have hk (p : G.El) : G.chord (x⁻¹*p*y)=G.chord (p*(x*y⁻¹)⁻¹) := by rw [mul_assoc (x⁻¹),chord_cyc]; simp only [mul_inv_rev,inv_inv, mul_assoc]
  unfold predict; split_ifs with h
  · have hz := (min_iff P.weight P.weight_sum Y (P.best Y)).2 (P.bond_min Y).choose_spec
    apply le_trans ?_ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_left ..) (by linarith)) hi)
    have ht : ‖m-G.mat (x*y⁻¹)‖ ≤ G.colorScale * ∑ i, P.weight i * G.chord (x⁻¹*Y i*y) := by
      let Q i := G.mat (Y i)-G.mat (x*y⁻¹)
      rw [show m-G.mat (x*y⁻¹) = ∑ i, P.weight i • Q i by simp only [Q,smul_sub, sum_sub_distrib, ← Finset.sum_smul,P.weight_sum,one_smul,m]]
      apply (norm_sum_le _ _).trans_eq
      simp_rw [Finset.mul_sum,Q,norm_smul,← chord_gap,Real.norm_of_nonneg (P.weight_nonneg _), hk, mul_left_comm (P.weight _) G.colorScale]
    apply le_of_mul_le_mul_left (a:=G.colorScale) ?_ G.colorScale_pos
    rw [hk,chord_gap]; apply le_trans (norm_sub_le_norm_sub_add_norm_sub _ m _)
    rw [norm_sub_rev (G.mat _)]; have he : ‖m-G.mat (P.best Y)‖ ≤ ‖m-G.mat (x*y⁻¹)‖ := hz _; linarith only [he,ht]
  have ht := (le_of_not_gt h).trans ((P.bond_min Y).choose_spec (x*y⁻¹))
  refine (G.chord_le_two _).trans ?_
  have h₁ : K.predictor_cut ≤ ∑ i,P.weight i * G.chord (x⁻¹*Y i*y) := by
    apply ht.trans; apply Finset.sum_le_sum
    intro i _; rw [hk]; apply mul_le_mul_of_nonneg_left _ (P.weight_nonneg _)
    let c := Y i * (x*y⁻¹)⁻¹
    change G.price c ≤ G.chord c
    nlinarith [G.chord_price c,G.chord_nonneg c,G.chord_le_two c]
  have hh := K.predictor_cut_pos
  apply le_trans ?_ (mul_le_mul (mul_le_mul_of_nonneg_left (le_max_right ..) zero_le_two) h₁ hh.le (by positivity))
  rw [mul_assoc, inv_mul_cancel₀ hh.ne',mul_one]
end YM.Pressure
