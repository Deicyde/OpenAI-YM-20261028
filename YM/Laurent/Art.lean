import YM.Laurent.Turn
/-!
# strip-sup to Width (pre-L)

Quantitative also when strip width decays.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Laurent
open Lattice Matrix Finset Filter RG MeasureTheory Function Topology Complex UnitAddTorus
open scoped Topology BigOperators ContDiff ComplexConjugate ENNReal

lemma pins (h : ℝ) (hp : 0 < h) (s : Finset ℤ) : ∑ i∈s, Real.exp (-h*i.natAbs) ≤ 2*((1+h)/h) := by
  let f (i : ℕ) := Real.exp (-h*i)
  have he (t : Finset ℕ) : ∑ i∈t,f i ≤ (1+h)/h := by
    have he : Real.exp (-h)<1 := by simpa only [Real.exp_lt_one_iff] using (Real.exp_lt_one_iff.mpr (by linarith : -h<0) : Real.exp (-h)<1)
    have hw := hasSum_geometric_of_lt_one (Real.exp_pos _).le he
    calc
      _ = ∑ i∈t,Real.exp (-h)^i := by unfold f; simp only [← Real.exp_nat_mul,mul_comm]
      _ ≤ _ := (hw.summable.sum_le_tsum _ (fun i _ => by positivity)).trans_eq hw.tsum_eq
      _ ≤ ((1+h)/h) := by
        have hx : Real.exp (-h) ≤ 1/(h+1) := by
          rw [Real.exp_neg,one_div]; exact (inv_le_inv₀ (Real.exp_pos _) (by linarith)).mpr (Real.add_one_le_exp _)
        rw [← one_div, div_le_iff₀ (show 0 < 1-Real.exp (-h) by linarith)]
        calc
          (1:ℝ)=((1+h)/h)*(1-1/(h+1)) := by field_simp; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hb (t : Finset ℤ) (hx : Set.InjOn Int.natAbs t) : ∑ i∈t,Real.exp (-h*i.natAbs)≤ (1+h)/h := by
    have hk := he (t.image Int.natAbs); rwa [sum_image hx] at hk
  let a := s.filter (fun i=> i<0)
  let b := s.filter (fun i => ¬ i<0)
  rw [← filter_union_filter_not_eq (s:=s) (p:=fun i => i<0),sum_union]
  · apply (add_le_add (hb a ?_) (hb b ?_)).trans (by rw [two_mul])
    all_goals intro i hi j hj hh; obtain ⟨-,h1⟩ := mem_filter.mp hi; obtain ⟨-,h2⟩ := mem_filter.mp hj; omega
  exact disjoint_left.mpr fun i hi hj => (mem_filter.mp hj).2 (mem_filter.mp hi).2

variable {α : Type*} [Fintype α]

lemma Width.compactPay (h : ℝ) (hp : 0<h) : RG.SumBudget (fun z : Shift α => Real.exp (-h*size z)) ( (2*((1+h)/h))^(Fintype.card α)) := by
  classical
  have he (S : Finset (Shift α)) : ∑ i∈S,Real.exp (-h*size i) ≤ (2*((1+h)/h))^(Fintype.card α) := by
    let A := fun i : α => S.image fun a => a i
    let f := fun v : ((i : α) → ↥(A i)) => fun i => (v i).val
    have hf : Function.Injective f := fun a b h => funext fun i => Subtype.ext (congr_fun h i)
    let g : (i : α) → ↥(A i) → ℝ := fun _ i => Real.exp (-h*i.val.natAbs)
    calc
      _ ≤ ∑ i∈univ.image f,Real.exp (-h*size i) := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro i hi; apply mem_image.mpr; exact ⟨fun j => ⟨i j,mem_image_of_mem _ hi⟩,mem_univ _,rfl⟩
        intro i _ _; positivity
      _ = ∑ i : ((j : α) → ↥(A j)),∏ j, g j (i j) := by rw [sum_image hf.injOn]; simp only [size,Nat.cast_sum, Finset.mul_sum, Real.exp_sum]; rfl
      _ = ∏ i, ∑ j,g i j := (Fintype.prod_sum g).symm
      _ ≤ ∏ _ : α,(2*((1+h)/h)) := prod_le_prod (fun i _ => sum_nonneg fun j _ => (Real.exp_pos _).le) fun i _ => by
        exact (sum_subtype (p:=fun j => j ∈ A i) _ (fun _ => Iff.rfl) (fun x => Real.exp (-h*(x:ℤ).natAbs))).symm.le.trans (pins h hp _)
      _ = _ := by simp
  have ht := summable_of_sum_le (fun z : Shift α => (Real.exp_pos (-h*size z)).le) he
  exact ⟨fun i => (Real.exp_pos _).le,ht,ht.tsum_le_of_sum_le he⟩

variable {u : Phase α → ℂ} {η K : ℝ}

lemma Vane.issues (h : Vane u η) (hk : ∀ p∈strip η,‖u p‖≤K) (H b : ℝ) (hp : 0≤H) (hb : 0<b) (hi : H+b < η) :
    Width H (K*(2*((1+b)/b))^(Fintype.card α)) (market u 0) := by
  have hv : 0≤K := (norm_nonneg _).trans (hk 0 (show (0 : Phase α)∈strip η from fun i=> by simpa using h.side))
  let f := fun i : Shift α => K*Real.exp (-b*size i)
  have he (i : Shift α) : Real.exp (H*size i)*‖market u 0 i‖ ≤ f i := by
    let d := H+b
    let p : Phase α := fun a => if 0 ≤ i a then Complex.I*(-(d:ℂ)) else Complex.I*d
    have hh (a : α) : |(p a).im|=d := by unfold p; split <;> simp [abs_of_nonneg (show 0≤d by unfold d; linarith)]
    have h' : p∈strip η := fun a => (hh a).trans_lt hi
    have hu := market_cap h h' i K hk; rw [coat_price h h',norm_mul] at hu
    have hw : ‖mode p i‖=Real.exp (d*size i) := by
      rw [mode, Complex.norm_exp]; congr 1
      simp only [size,Nat.cast_sum,Finset.mul_sum,Complex.re_sum,Complex.mul_re,I_re,I_im,zero_mul,one_mul,zero_sub,Complex.mul_im,Complex.intCast_im,mul_zero, Complex.intCast_re,zero_add]
      apply Finset.sum_congr rfl; intro j _
      unfold p; split <;> rename_i Hx
      · rw [show ((i j).natAbs : ℝ)=(i j) by  rw [← Int.cast_natCast (R:=ℝ), show ((i j).natAbs:ℤ)=i j  by omega] ]; simp
      rw [show ((i j).natAbs:ℝ)=-(i j:ℤ) by  rw [← Int.cast_natCast (R:=ℝ), show ((i j).natAbs:ℤ)= -(i j:ℤ)  by omega, Int.cast_neg] ]; simp
    rw [hw] at hu
    calc
      _ = (Real.exp (d*size i)*‖market u 0 i‖)*Real.exp (-b*size i) := by
        rw [mul_right_comm,←Real.exp_add]; congr 2; unfold d; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hu (Real.exp_pos _).le
  have ht := Width.compactPay (α:=α) b hb
  have hs := ht.2.1.mul_left K
  have hx (i : Shift α) : 0≤Real.exp (H*size i)*‖market u 0 i‖ := by positivity
  have hys := Summable.of_nonneg_of_le hx he hs
  exact ⟨hx,hys,(hys.tsum_le_tsum he hs).trans (by unfold f; rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left ht.2.2 hv)⟩

-- analytic closure obligation (Equality shown entire open strip; boundaries not asserted).
lemma Vane.paints (h : Vane u η) (hk : ∀ p∈ strip η,‖u p‖≤K) (p : Phase α) (hp : p∈strip η) : read (market u 0) p=u p := by
  have ht : ∃ H : ℝ, 0≤H ∧ Within H p ∧ H < η := by
    cases isEmpty_or_nonempty α
    · exact ⟨0,le_rfl,fun i=> isEmptyElim i,h.side⟩
    obtain ⟨a,-,ha⟩ := Finset.exists_max_image Finset.univ (fun i => |(p i).im|) Finset.univ_nonempty
    exact ⟨_, abs_nonneg _,fun i => ha i (mem_univ _),hp a⟩
  obtain ⟨H,hH,he,hy⟩ := ht
  have hb : Width H _ _ := h.issues hk H ((η-H)/2) hH (by linarith) (by linarith)
  have hi : Summable (market u p) := ((hb.series p he).2.1.of_norm).congr (fun i => (coat_price h hp i).symm)
  have hs := hasSum_mFourier_series_apply_of_summable (f:=h.guise hp) hi (dress α 0)
  have hl := hs.tsum_eq
  change (∑' i,market u p i • (mFourier i (dress α 0)))=veils u p _ at hl
  have ha : walk α 0=0 := by ext; simp [walk]
  simp only [coat_price h hp, h.steps hp, ha, wears,mode_constant,smul_eq_mul,mul_one, add_zero] at hl
  exact hl
end YM.Laurent
