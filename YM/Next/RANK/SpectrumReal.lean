import YM.Next.RANK.Common


/-!
# Variable-dimensional marks: extracting coefficients from real values

Costs polynomial when many fine sites in an origin stencil. Derivative
operator norm potentially from mixed polarization; here avoid it: uniform in
TOTAL degree and dimension growth, by tests on individual coordinate windows
of at most the degree and purely scalar value extraction. No positivity.
Also used to test polynomial identities of calibrated readout. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Spindle
open Function MvPolynomial Normal Rise Common Filter Set LinearMap
open scoped Classical BigOperators Topology

variable {A V B : Type*}

abbrev text {A : Type*} (x : A → ℝ) (p : poly A) := aeval (fun i => (x i:ℂ)) p

lemma listen (P Q : poly V) (B : ℝ) (hp : 0<B) (h : ∀ x : V→ℝ,(∀ i, |x i| ≤ B) → text x P=text x Q) : P=Q := by
  let v : Set ℂ := (fun x : ℝ => (x:ℂ)) '' Icc (-B) B
  have hv : v.Infinite := (Set.Icc_infinite (by linarith)).image Complex.ofReal_injective.injOn
  apply MvPolynomial.funext_set (fun _ : V => v) (fun _ => hv)
  intro x hx
  choose y hy fy using fun i : V => hx i (mem_univ i)
  rw [show x=fun i => (y i:ℂ) from funext fun i => (fy i).symm]; exact h y fun i => abs_le.mpr (hy i)
lemma audible (P Q : poly V) (h : ∀ x : V → ℝ, text x P=text x Q) : P=Q := listen P Q 1 zero_lt_one fun x _ => h x

private lemma sold {V Z : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T : Z→V→ₗ[ℂ] ℂ) (h : Injective (LinearMap.pi T)) : ∃ D : Finset Z, Injective (LinearMap.pi (fun x : D => T x.val)) := by
  let W := fun D : Finset Z => ker (LinearMap.pi (fun x : D => T x.val))
  let S D:= Module.finrank ℂ (W D)
  have ht : ∃ n : ℕ, ∃ D, S D=n := ⟨_,∅,rfl⟩
  obtain ⟨D,hD⟩ := (Nat.find_spec ht)
  refine ⟨D,ker_eq_bot.mp (ker_eq_bot'.mpr fun i hi => h ?_)⟩
  ext1 z
  let Y:= insert z D
  have hp : W Y ≤ W D := by
    intro i hh; unfold W at *; rw [LinearMap.mem_ker] at hh ⊢; ext1 k; exact congr_fun hh ⟨k.val,Finset.mem_insert_of_mem k.property⟩
  have he : W Y=W D := Submodule.eq_of_le_of_finrank_le hp (show S D ≤ S Y from hD ▸ Nat.find_min' _ ⟨_,rfl⟩)
  rw [map_zero]; exact congr_fun (show LinearMap.pi (fun x : Y => T x.val) i=0 from (show i∈W Y from he.symm ▸ hi)) ⟨z, Finset.mem_insert_self ..⟩

-- coefficient census support sizes

lemma notes_co (p : poly V) (i) : ‖coeff i p‖≤coin p := by
  rw [metal]; by_cases hi : i∈p.support
  · exact Finset.single_le_sum (fun _ _ => norm_nonneg _) hi
  rw [MvPolynomial.notMem_support_iff.mp hi,norm_zero]; exact Finset.sum_nonneg fun _ _ => norm_nonneg _
lemma retiring (F : poly V) (c : ℂ) : coin (c • F) ≤ ‖c‖*coin F := by
  rw [metal,metal, Finset.mul_sum]; apply le_trans _ (Finset.sum_le_sum_of_subset_of_nonneg (show (MvPolynomial.support (c • F)) ⊆ MvPolynomial.support F from MvPolynomial.support_smul)
    (fun i _ _ => show 0≤‖c‖*‖coeff i F‖ from mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  apply Finset.sum_le_sum; intro i _; rw [coeff_smul,norm_smul]
-- fixed dimension certificate via finitely many measuring points on a real cube
lemma molds (V : Type*) [Fintype V] (d : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ (T : Finset (V→ℝ)) (C : ℝ), 0 ≤ C ∧ (∀ x∈T, ∀ i, |x i| ≤ ε) ∧ ∀ p : poly V,p.totalDegree ≤ d →
      ∀ B : ℝ, 0 ≤ B → (∀ i∈T, ‖text i p‖≤B) → coin p ≤ C*B := by
  let F:= restrictTotalDegree V ℂ d
  let Z:= {x : V→ℝ // ∀ i : V, |x i| ≤ ε}
  let U (z : Z) := (aeval (R:=ℂ) (fun i => (z.val i:ℂ))).toLinearMap.comp F.subtype
  have h : Injective (LinearMap.pi U) := by
    intro x y he; exact Subtype.ext (listen x.val y.val ε hε (fun v hv => congr_fun he ⟨v,hv⟩))
  haveI : FiniteDimensional ℂ F := by unfold F; infer_instance
  obtain ⟨D,H⟩ := sold U h
  let E (x : D) := U x.val
  let T := D.image Subtype.val
  let J:= ((LinearMap.pi E)).leftInverse
  let L:= F.subtype.comp J
  let D' := ∑ i : D, coin (L (Pi.single i 1))
  refine ⟨T,D',Finset.sum_nonneg (fun _ _ => sign _ _ zero_le_one),?_,fun p hp B hB he => ?_⟩
  · intro x hx; obtain ⟨i,-,rfl⟩ := Finset.mem_image.mp hx; exact i.property
  let q : F := ⟨p,(mem_restrictTotalDegree ..).2 hp⟩
  let t:= LinearMap.pi E q
  have hu : p=L t := (congr_arg (F.subtype) (LinearMap.leftInverse_apply_of_inj (ker_eq_bot.mpr H) q)).symm
  have hh i : ‖t i‖≤B := he _ (Finset.mem_image_of_mem _ i.property)
  have ht : t=∑ i, (t i) • Pi.single i 1 := by ext1 i; simp [Pi.single_apply]; exact Eq.symm ((Finset.sum_ite_eq _ i t).trans (if_pos (Finset.mem_attach ..)))
  rw [hu,ht,map_sum]
  apply (Rise.collect _ zero_le_one ..).trans; rw [show D'= _ from rfl, ← mul_comm B]
  unfold D'; rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro i _
  exact (by rw [map_smul]; exact (retiring _ _).trans (mul_le_mul_of_nonneg_right (hh i) (sign _ _ zero_le_one)))

section
variable [Fintype A] {d : ℕ} {p : poly A} (h : p.totalDegree ≤ d)

-- project to just the variables of a single term. Retain degree bound.
omit [Fintype A] in
lemma legends {f : V → A} (hf : Injective f) : totalDegree (killCompl hf p) ≤ totalDegree p := by
  let H (i : A) := if h : i ∈ Set.range f then Finsupp.single ((Equiv.ofInjective f hf).symm ⟨i,h⟩) (1:ℂ) else 0
  have hx : killCompl (R:=ℂ) hf=exchange H := by ext1 i; rw [killCompl,MvPolynomial.aeval_X,exchange_x]; unfold H; split <;> simp [Normal.glyph]
  rw [hx]; exact Rise.ascent ..

private lemma places_sell (d : ℕ) (ε : ℝ) (hε : 0 < ε) : ∃ T : ℝ,0≤T ∧ ∀ (A : Type*) [Fintype A]
    (p : poly A) (_ : p.totalDegree≤d) (B : ℝ) (_ : 0≤B), (∀ U : A → ℝ,(∀ i, |U i| ≤ ε) → ‖text U p‖ ≤ B) → ∀ u, ‖p.coeff u‖ ≤ T*B := by
  choose t C hC ht hc using fun n : Fin (d+1) => molds (Fin n.val) d ε hε
  refine ⟨∑ i, C i,Finset.sum_nonneg (fun i _ => hC i),?_⟩
  intro A F p hp B hB he i; by_cases hi : i ∈ MvPolynomial.support p
  swap
  · rw [MvPolynomial.notMem_support_iff.mp hi,norm_zero]; exact mul_nonneg (Finset.sum_nonneg fun i _ => hC i) hB
  let D:= i.support
  have hD : D.card ≤ d := calc
    D.card ≤ i.sum (fun _ n => n) := by
      change D.card ≤ ∑ x∈i.support,i x; rw [show D.card=∑ _∈i.support,1 by simp [D]]; apply Finset.sum_le_sum; intro x hx; exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hx)
    _ ≤ _ := (le_totalDegree hi).trans hp
  let n : Fin (d+1) := ⟨D.card, Nat.lt_succ_of_le hD⟩
  let V : ↥D ≃ Fin n.val := Fintype.equivFinOfCardEq (Fintype.card_coe ..)
  let Z : Fin n.val → A := fun i => (V.symm i).val
  have hx : Injective Z := Subtype.val_injective.comp V.symm.injective
  let E:= killCompl hx (R:=ℂ)
  let m:= i.comapDomain Z hx.injOn
  have heq : coeff i p = coeff m (E p) := by
    unfold E; rw [coeff_killCompl]; apply congr_arg (fun x => coeff x p)
    refine Eq.symm (Finsupp.mapDomain_comapDomain _ hx i fun j hu => ⟨V ⟨j,hu⟩,?_⟩)
    unfold Z; rw [Equiv.symm_apply_apply]
  have hT := hc n (E p) ((legends hx).trans hp) B hB
  rw [heq]; apply (notes_co _ _).trans; apply (le_trans (hT ?_) (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ n)) hB))
  intro U h
  let H (i : A) := if h : i∈Set.range Z then U ((Equiv.ofInjective Z hx).symm ⟨i,h⟩) else 0
  have hv : (aeval (R:=ℂ) (fun i => (U i:ℂ))).comp E=aeval (fun j => (H j:ℂ)) := by
    ext1 j; rw [AlgHom.comp_apply,show E= _ from rfl]; unfold E H; simp only [killCompl,aeval_X]; split <;> simp
  rw [show text U (E p)=text H p from DFunLike.congr_fun hv p]; exact he H fun i => by unfold H; split; exact ht n _ h _; rw [abs_zero]; exact hε.le

include h
private lemma positions : p.support.card ≤ (d+1)*(Fintype.card A + 1)^d := by
  classical
  -- inject terms into slots words i.length
  let V:= p.support
  let P (i : V) := i.val.sum fun _ k => k
  have he (i : V) : P i ≤ d := (MvPolynomial.le_totalDegree i.property).trans h
  choose f hf using fun i : V => letter i.val
  let g (i : V) : (s : Fin (d+1)) × (Fin s.val→ A) := ⟨⟨P i,Nat.lt_succ_of_le (he i)⟩, f i⟩
  have hp : Injective g := by
    intro i j h
    have ht (x : ↥V) : monomial x.val (1:ℂ) = (fun (u : (s : Fin (d+1))× (Fin s.val→ A)) => glyphs u.2 Finset.univ) (g x) := hf x
    have hv : monomial i.val (1:ℂ) = monomial j.val 1 := by rw [ht i,ht j,h]
    by_contra h
    have hx : j.val≠i.val := Subtype.coe_ne_coe.mpr (Ne.symm h)
    have hh := congr_arg (coeff i.val) hv; rw [coeff_monomial,coeff_monomial,if_pos rfl,if_neg hx] at hh; exact one_ne_zero hh
  rw [← Fintype.card_coe]; apply le_trans (Fintype.card_le_of_injective _ hp); rw [Fintype.card_sigma]; apply le_trans (b:=∑ _ : Fin (d+1),(Fintype.card A + 1)^d)
  · apply Finset.sum_le_sum; intro i _; rw [Fintype.card_fun,Fintype.card_fin]
    exact (Nat.pow_le_pow_left (Nat.le_succ _) _).trans (pow_le_pow_right₀ (by omega) (Nat.le_of_lt_succ i.isLt))
  simp

omit [Fintype A] h in
-- readout constant independent of number of actual variables/natures.
lemma ball_count (d : ℕ) (ε : ℝ) (hε : 0 < ε) : ∃ T : ℝ,0 ≤ T ∧
    ∀ (A : Type*) [Fintype A] (p : poly A), p.totalDegree≤d → ∀ B : ℝ,0≤B →
      (∀ U : A → ℝ,(∀ i, |U i| ≤ ε) → ‖text U p‖ ≤ B) → coin p ≤ ((Fintype.card A:ℝ)+1)^d*T*B := by
  obtain ⟨T,hT,hP⟩ := places_sell d ε hε
  refine ⟨(d+1:ℝ)*T,by positivity,?_⟩; intro A I p hp B hB h
  rw [metal]; calc
    _ ≤ ∑ _i∈p.support,T*B := Finset.sum_le_sum fun i _ => hP A p hp B hB h i
    _ ≤ _ := by
      rw [Finset.sum_const,nsmul_eq_mul]; refine (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (positions hp)) (mul_nonneg hT hB)).trans (le_of_eq ?_)
      push_cast; ring
end
end YM.Next.Rank.Spindle
