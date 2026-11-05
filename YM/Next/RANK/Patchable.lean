import YM.Next.RANK.Bordering

/-! Hold plate rights with their chosen precision. E and K anchor/hit tests;
    E values not clipped or redeclared canonical. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Alarm
open Function Filter RG Thirst Baler Lattice Wilson Finset MeasureTheory Relation Corona Value Glyph Marker PathData
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {p q : BudgetPoint} {A : Activities G n} {ι κ V : Type} [Fintype V] [DecidableEq V] {ζ : V→Site n}
variable {e d m t : ℝ}

structure Lower (p q : BudgetPoint) : Prop where
  grows : p.B≤q.B
  sci : q.order=p.order
  pave : q.power=p.power
  still : q.supportExponent=p.supportExponent
  tight : 2*q.threshold≤ p.threshold
  size : 8 ≤ q.B
lemma Lower.good (h : Lower p q): q.threshold≤p.threshold:= by linarith only [h.tight,q.threshold_pos]
lemma Lower.cost {o : Site n} (h : Lower p q) {v : Directions G n} (H : q.dirBound o v): p.dirBound o v:= by
  intro i; have hz:= H i; rw [h.pave] at hz; apply le_trans hz; exact mul_le_mul_of_nonneg_right h.good (pow_nonneg (by positivity) _)

lemma Lower.untouched (h : Lower p q) (H : A.RegularFamily p) : A.RegularFamily q:= by
  refine ⟨fun i=>?_, H.at_flat,H.vanish⟩; have ht:=H.smooth i
  let X:= (A.reg i).support
  have hs : ∀ U : Config G n,Healthy q.threshold X U → Healthy p.threshold X U:= fun U hx=> threshold_fit _ _ h.good _ hx
  exact ⟨ht.sites,ht.borel,ht.symmetry,fun U HH=>h.sci.symm ▸ ht.smooth U (hs U HH),fun U HH a b hh=>ht.hasDerivs U (hs U HH) a b (hh.trans_eq h.sci)⟩

lemma thinner (h : Lower p q) (H : A.EBound p m) : A.EBound q m := by
  obtain ⟨b,hb,hx⟩:=H
  have he i : q.supBounds (A.reg i).site (A.reg i).support (A.E i) (b i):= by
    refine ⟨(hb i).1,fun U hh l hl ht=> (hb i).2 U (threshold_fit _ _ h.good _ hh) l (hl.trans_eq h.sci) fun x hX=>h.cost (ht x hX)⟩
  refine ⟨b,he,fun x=>?_⟩
  let f P:= fun i=> if (A.reg i).site=x then BudgetPoint.mass P (A.reg i).support (b i) else 0
  change SumBudget (f q) m
  have hQ i : 0≤ f q i:= by unfold f;split;exact mul_nonneg (Real.exp_pos _).le (hb i|>.1); exact le_rfl
  have H i : f q i≤ f p i:= by
    unfold f; split; apply mul_le_mul_of_nonneg_right _ ((hb i).1); apply Real.exp_le_exp.mpr; rw [h.still]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast encumber _ _ h.grows _) p.exponent_pos.le
    exact le_rfl
  have ht:=(hx x).2.1.of_nonneg_of_le hQ H; exact ⟨hQ,ht,(ht.tsum_le_tsum H (hx x).2.1).trans (hx x).2.2⟩

-- path-optional mask changes on E

variable (A : Activities G n)

def eng (p q : BudgetPoint) (U : Config G n) := A.additive q U-A.additive p U

def compose (p q : BudgetPoint) (h : Lower p q) (H : A.RegularFamily p) (i : ℕ) : Wickless G n q.threshold where
  extent:=halo 8 (A.reg i).support
  active:= ⟨_, halo_subset _ _ (A.reg i).anchor⟩
  value U:= A.regularOccurrence q i U-A.regularOccurrence p i U
  inv k U:=congr_arg₂ (·-·) (sails _ _ _ (H.smooth i).symmetry k U) (sails _ _ _ (H.smooth i).symmetry k U)
  meas:= (masked_measurable _ _ _ (H.smooth i).borel).sub (masked_measurable _ _ _ (H.smooth i).borel)
  sees U V h _:=congr_arg₂ (·-·) (sail _ _ _ (H.smooth i).sites U V h) (sail _ _ _ (H.smooth i).sites U V h)
  untouched U hh:=by
    have ht:= awake_mask _ (A.E i) h.good U hh
    apply sub_eq_zero.mpr (sub_eq_zero.mp ht).symm

lemma comp_turn (x : Site n) (u : Signed) (P : A.Moves u x) (i : ℕ) (p : BudgetPoint) (U : Config G n) : A.regularOccurrence p (P.ep i) U=A.regularOccurrence p i (pull u x U):= by
  have H : Healthy p.threshold (A.reg (P.ep i)).support U ↔ Healthy p.threshold (A.reg i).support (pull u x U):= by rw [P.reg_support]; exact (s_healthy ..).symm
  unfold Activities.regularOccurrence; by_cases ht : Healthy p.threshold (A.reg i).support (pull u x U)
  · rw [masked_eq _ _ _ _ ht,masked_eq _ _ _ _ (H.2 ht),P.valuesE]
  rw [masked_ne _ _ _ _ ht,masked_ne _ _ _ _ (mt H.1 ht)]
lemma composers (h : A.Valid p m e) (H : Lower p q) : Garden (compose A p q H h.regular) := by
  intro s x; obtain ⟨M⟩:= h.moves s x; refine ⟨M.ep, fun i=> ⟨?_,fun U=>?_⟩⟩
  · unfold compose; dsimp only; rw [M.reg_support,swath_iffHalo]; rfl
  dsimp only [compose]; simp only [comp_turn A x s M]

-- support shift costs with same q.B, include halo

def scalesExp (p q : BudgetPoint) (e : ℝ) := 100000*(p.B:ℝ)*e ≤ q.B*p.supportExponent
lemma scaler (p q : BudgetPoint) (h : Lower p q) (he : scalesExp p q e) (he' : 0≤e) (X : Support n) : debt q.B e (halo 8 X) ≤ Real.exp (100000*e)*debt p.B p.supportExponent X:= by
  have hp:=h.grows
  have hz : (q.B:ℝ)*coverNumber q.B (halo 8 X)≤ 100000*(q.B + (p.B:ℝ)*coverNumber p.B X) := by exact_mod_cast widen p.B q.B 8 p.B_pos hp h.size X
  unfold debt; rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; apply le_of_mul_le_mul_left _ (Nat.cast_pos (α:=ℝ)|>.mpr q.B_pos)
  unfold scalesExp at he; linarith only [mul_le_mul_of_nonneg_left hz he', mul_le_mul_of_nonneg_right he (Nat.cast_nonneg (α:=ℝ) (coverNumber p.B X))]
lemma ante (p : BudgetPoint) (F : Activities G n) {W : ℝ} (h : F.EBound p W) (U) : Summable (fun i=> F.regularOccurrence p i U) := by
  obtain ⟨b,hb,hp⟩:= Activities.E_total h
  refine hb.of_norm_bounded fun i=> ?_; unfold Activities.regularOccurrence masked
  by_cases ht : Healthy p.threshold (F.reg i).support U
  · rw [Set.indicator_of_mem ht]; exact (hp i).2 U ht [] (Nat.zero_le _) (by simp)
  rw [Set.indicator_of_notMem ht]; rw [norm_zero]; exact (hp i).1
lemma once (h : A.Valid p m d) (H : Lower p q) (e : ℝ) (he : 0≤e) (hp : scalesExp p q (e+1)) :
    Volunteer (eng A p q) q e (wilt q.B*(Real.exp (100000*(e+1))*m)):= by
  obtain ⟨B,hB,hS⟩:=h.boundE
  let X:=compose A p q H h.regular
  refine ⟨ℕ,inferInstance,X,composers A h H, ⟨B, fun i=> ⟨(hB i).1,fun U=> ?_⟩,circle (n:=n) _ _ (fun i=> (A.reg i).site) ?_ e _ q.B_pos (fun i=> (hB i).1) _ ?_⟩,fun U=>?_⟩
  · let F:= (A.reg i).support
    by_cases ht:Healthy q.threshold F U
    · have he : (X i).value U=0:= by
        dsimp only [X,compose,Activities.regularOccurrence]; rw [masked_eq _ _ _ _ ht,masked_eq _ _ _ _ (threshold_fit _ _ H.good _ ht),sub_self]
      rw [he,abs_zero]; exact (hB i).1
    dsimp only [X,compose,Activities.regularOccurrence]; rw [masked_ne _ _ _ _ ht]; by_cases hf:Healthy p.threshold F U
    · rw [masked_eq _ _ _ _ hf,zero_sub,abs_neg]; exact (hB i).2 U hf [] (Nat.zero_le _) (by simp)
    rw [masked_ne _ _ _ _ hf,sub_zero,abs_zero]; exact (hB i).1
  · exact fun i=> halo_subset _ _ (A.reg i).anchor
  · intro x; let e':=e+1; let Y:=Real.exp (100000*(e+1)); let f i:=pay (fun i=> B i*debt q.B e' (X i).extent) (fun i=> (A.reg i).site=x) i
    let g i:= if (A.reg i).site=x then p.mass (A.reg i).support (B i) else 0; change SumBudget f (Y*m)
    have hf i:0≤f i:= by unfold f pay; split; exact mul_nonneg (hB i).1 (Real.exp_pos _).le;exact le_rfl
    have hg i:f i≤ Y*g i:= by
      unfold f pay g; split_ifs; exact (mul_le_mul_of_nonneg_left (scaler p q H hp (add_nonneg he zero_le_one) _) (hB _|>.1)).trans_eq (by unfold BudgetPoint.mass Y debt; ring)
      rw [mul_zero]
    have hs : Summable g:=(hS x).2.1; have hv:=hs.mul_left Y; have ht:= hv.of_nonneg_of_le hf hg; refine ⟨hf,ht,(ht.tsum_le_tsum hg hv).trans ?_⟩
    rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left (hS x).2.2 (Real.exp_pos _).le
  exact (Summable.tsum_sub (ante q A (thinner H h.boundE) U) (ante p A h.boundE U)).symm

-- K halo cost. mark from K pre budget
lemma march (u : ℕ) {a : ℝ} (E : ι→ Lifted G ζ t) (f : Site n) (j : ι) (hj : f∈ halo u (E j).extent) (ht : 0 ≤ a) : a≤∑ i∈ halo u {f}, if i∈ (E j).extent then a else 0 := by
  obtain ⟨y,hy,h⟩:=halo_spec.mp hj
  have he : y∈ halo u {f}:= halo_spec.mpr ⟨_,mem_singleton_self _,(separation_comm f y).trans_le h⟩
  calc
    _ = (if y∈(E j).extent then a else 0) := (if_pos hy).symm
    _ ≤ _ := single_le_sum (f:=fun i : Site n=> if i∈ (E j).extent then a else 0) (fun i hi=>by split <;> first|exact ht|exact le_rfl) he
lemma ShiftUp {E : ι→ Lifted G ζ t} {Z : ι→ℝ} (p q : BudgetPoint) (H : Lower p q) (e : ℝ) (he : 0≤e) (hp : scalesExp p q e) (h : ∀ i,0≤ Z i) (w : ℝ) (hi : Incur (fun i=> (E i).extent) p.B Z p.supportExponent w) :
    Incur (fun i=> halo 8 (E i).extent) q.B Z e (83521*(Real.exp (100000*e)*w)) := by
  intro x
  let f x:=pay (fun i=> Z i *debt p.B p.supportExponent (E i).extent) (fun i=> x∈(E i).extent)
  let g:= pay (fun i=> Z i*debt q.B e (halo 8 (E i).extent)) (fun i=> x∈halo 8 (E i).extent)
  let M:=halo 8 ({x} : Support n);let C:=Real.exp (100000*e)
  let D:=fun i=> ∑ y∈M,f y i
  have hz:=hi x; have hh : Summable D:= summable_sum fun i _=> (hi i).2.1
  have ht : 0≤w := le_trans (tsum_nonneg hz.1) hz.2.2
  have hp' : (∑' i,D i) ≤ 83521*w := by
    unfold D; rw [Summable.tsum_finsetSum (fun i _=> (hi i).2.1)]; apply le_trans _ <| mul_le_mul_of_nonneg_right (show (M.card:ℝ) ≤ 83521 by exact_mod_cast (by simpa using halo_size {x} 8)) ht
    simp only; apply le_trans (b:=∑ _∈ M, w); exact sum_le_sum fun i _=> (hi i).2.2
    simp
  have hf i:0≤ g i:= by unfold g pay;split;exact mul_nonneg (h i) (Real.exp_pos _).le;exact le_rfl
  have hg i:g i≤ C*D i:= by
    unfold g pay; dsimp only; split_ifs with hx
    · refine (mul_le_mul_of_nonneg_left (scaler p q H hp he _) (h i)).trans ?_; rw [mul_left_comm]; apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      unfold D; apply (march 8 E x i hx (mul_nonneg (h i) (posit p.B p.supportExponent _ |>.le))).trans
      apply sum_le_sum; intro j _; unfold f pay; split_ifs <;> exact le_rfl
    apply mul_nonneg (Real.exp_pos _).le (sum_nonneg (fun y _=> (hi y).1 i))
  have hv:=(hh.mul_left C).of_nonneg_of_le hf hg; refine ⟨hf,hv,(hv.tsum_le_tsum hg (hh.mul_left C)).trans ?_⟩; rw [tsum_mul_left]; exact (mul_le_mul_of_nonneg_left hp' (Real.exp_pos _).le).trans_eq (mul_left_comm ..)
end YM.Next.Rank.Alarm
