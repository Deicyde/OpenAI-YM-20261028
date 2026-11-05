import YM.UVExtension.Copse.Wood
/-! Marked partner tree. Adapted from Trees.Weigh. Fan cap
 estimated against multicover everywhere merely to improve
 estimate at root. Retain ordinary currency on every internal
 node. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Copse
open Lattice Finset RG Ac Push.AbsoluteSums Animals Trees
open scoped Topology BigOperators Classical
variable {n:Side}{ι:Type*} (X:ι→Support n)(B d:ℕ)
private def scalePrice (δ : ℝ) (Y : Support n) : ℝ := max (δ * Copse.cover d B Y) 1
private lemma signPrice (Y : Support n) (δ : ℝ): 0<scalePrice B d δ Y:=by unfold scalePrice; positivity

private lemma pays_fan (Y : Support n) {δ : ℝ} (hd : 0 < δ) (k : ℕ) :
    scalePrice B d δ Y ^ k ≤ (k.factorial:ℝ) * worth d B δ Y := by
  let x : ℝ := δ * cover d B Y
  have hx : 0 ≤ x := by unfold x; positivity
  have he : 1 ≤ (k.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos k
  change (max x 1)^k ≤ _ * Real.exp x
  rcases le_total 1 x with h|h
  · rw [max_eq_left h]
    have hk := (div_le_iff₀ (show 0 < (k.factorial:ℝ) by positivity)).mp
      (Real.pow_div_factorial_le_exp _ hx k)
    rwa [mul_comm]
  rw [max_eq_right h,one_pow]
  exact he.trans (le_mul_of_one_le_right (by positivity) (Real.one_le_exp hx))

private lemma overlap_eq {α : Type*} [Fintype α] (w : ι → ℝ) (a : ℝ)
    (Y : Support n) (p : α → Option α) (z : α → ι) (h : Ranked p) :
    forestWeight X B w a Y p z = (∏ i, overlapWeight X B w a (installed X Y z (p i)) (z i)) /
      (Fintype.card α).factorial := by
  unfold forestWeight; split
  next he =>
    congr 1
    exact prod_congr rfl (fun i _ => (if_pos (he.2 i)).symm)
  next he =>
    simp only [Sprouts,h,true_and,not_forall] at he
    obtain ⟨i,hi⟩ := he
    rw [prod_eq_zero (mem_univ i) (show overlapWeight X B w a (installed X Y z (p i)) (z i) = 0 from
      if_neg hi), zero_div]

private lemma prod_fanPrice {α : Type*} [Fintype α] [DecidableEq α] {δ : ℝ} (hd : 0 < δ)
    (Y : Support n) (p : α → Option α) (z : α → ι) :
    (∏ i, scalePrice B d δ (installed X Y z (p i))) ≤ (fanout p:ℝ) * (worth d B δ Y *
      ∏ i : α, currency B δ (X (z i))) := by
  let c i := installed X Y z i
  calc
    _ = ∏ i : Option α, scalePrice B d δ (c i) ^ children p i := by
      have he := prod_fiberwise univ p (fun j => scalePrice B d δ (c (p j)))
      apply he.symm.trans
      apply prod_congr rfl; intro i _
      calc
        _ = ∏ _j ∈ univ with p _j=i, scalePrice B d δ (c i) := prod_congr rfl fun j hj => by
          rw [(mem_filter.mp hj).2]
        _ = _ := Finset.prod_const _
    _ ≤ ∏ i : Option α, ((children p i).factorial:ℝ) * (match i with | none => worth d B δ (c i) | some _=> currency B δ (c i)) :=
      prod_le_prod (fun i _ => pow_nonneg (signPrice B d (c i) δ).le _) fun i _ => by
        cases i with
        | none => exact pays_fan B d _ hd _
        | some j=> exact (pays_fan B d _ hd _).trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (oldCost d B _)) hd.le)) (Nat.cast_nonneg _))
    _ = _ := by
      rw [prod_mul_distrib,fanout,Nat.cast_prod]; simp only [Fintype.prod_option]; rfl

-- Transition kernels for the proof: with extra exponent and normalized.
private def kernel (w : ι → ℝ) (a γ δ : ℝ) (Y : Support n) (i : ι) :=
    overlapWeight X B w (a+δ) Y i / (stretch B γ δ * scalePrice B d δ Y)

private lemma kernel_sum {w : ι → ℝ} {a γ δ : ℝ} (hg : 0 < γ) (hd : 0 < δ)
    (hh : Ac.Hit X B w (a+δ) γ) (Y : Support n) (D : Finset ι) :
    ∑ i ∈ D, kernel X B d w a γ δ Y i ≤ 1 := by
  have ho := stretch_pos B hg hd; have hm := signPrice B d Y δ
  let c : ℝ := Copse.cover d B Y
  have hy : (Y.card:ℝ) ≤ (ballCost B:ℝ) * c := by
    rw [mul_comm]; unfold c ballCost; exact_mod_cast size d B Y
  unfold kernel; rw [← sum_div,div_le_one (by positivity)]
  apply (overlap_sum X B hh Y D).trans
  calc
    _ ≤ ((ballCost B:ℝ) * c)*γ := mul_le_mul_of_nonneg_right hy hg.le
    _ = stretch B γ δ * (δ * c) := by unfold stretch; field_simp
    _ ≤ stretch B γ δ * scalePrice B d δ Y := mul_le_mul_of_nonneg_left (le_max_left ..) ho.le

private lemma kernel_pos {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) {γ δ : ℝ} (hg : 0 < γ) (hd : 0 < δ)
    (a : ℝ) (Y : Support n) (i : ι) : 0 ≤ kernel X B d w a γ δ Y i :=
    div_nonneg (overlap_nonneg X B w hw _ Y i) (mul_nonneg (stretch_pos B hg hd).le (signPrice B d _ _).le)

private lemma buy {α : Type*} [Fintype α] [DecidableEq α] {δ γ : ℝ} (hd : 0 < δ) (hg : 0 < γ)
    {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (Y : Support n) (p : α → Option α) (z : α → ι) (a : ℝ) :
    let G := installed X Y z
    let O (i : α) := overlapWeight X B w a (G (p i)) (z i)
    let K (i : α) := kernel X B d w a γ δ (G (p i)) (z i)
    (∏ i, O i) ≤ worth d B δ Y * (stretch B γ δ)^Fintype.card α * fanout p * ∏ i, K i := by
  intro G O K
  let t := stretch B γ δ
  have ht : 0 < t := stretch_pos B hg hd
  let u i := currency B δ (X (z i))
  have hx i : 0 < u i := Real.exp_pos _
  have hh i : 0 ≤ K i := kernel_pos X B d hw hg hd a _ _
  have eq (i : α) : O i * u i = t * scalePrice B d δ (G (p i)) * K i := by
    unfold O K kernel overlapWeight
    split
    next h =>
      have he : currency B (a+δ) (X (z i)) = currency B a (X (z i)) * u i := by
        rw [currency,add_mul,Real.exp_add]; rfl
      change _ = t * _ * (_ * _ / (t*_))
      rw [he]; have hb := signPrice B d (G (p i)) δ; field_simp
    next h => simp
  apply le_of_mul_le_mul_right (a:=∏ i, u i) ?_ (Finset.prod_pos (fun i _ => hx i))
  calc
    _ = ∏ i, t * scalePrice B d δ (G (p i)) * K i := by
      rw [← prod_mul_distrib]; exact prod_congr rfl fun i _ => eq i
    _ = (t^Fintype.card α * ∏ i, K i) * ∏ i, scalePrice B d δ (G (p i)) := by
      simp_rw [prod_mul_distrib,Finset.prod_const,card_univ]; ring
    _ ≤ (t^Fintype.card α * ∏ i, K i) * ((fanout p:ℝ) * (worth d B δ Y * ∏ i, u i)) :=
      mul_le_mul_of_nonneg_left (prod_fanPrice X B d hd Y p z) (mul_nonneg (pow_nonneg ht.le _)
        (prod_nonneg fun i _ => hh i))
    _ = _ := by unfold t; ring

/-- Uniform at each finite D. This step pays all child factorials. -/
theorem basket (m : ℕ) (D : Finset ι) (Y : Support n) {γ δ a : ℝ} (hg : 0 < γ)
    (hd : 0 < δ) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hh : Ac.Hit X B w (a+δ) γ) :
    ∑ p : Fin m → Option (Fin m), ∑ z : Fin m → D, forestWeight X B w a Y p (fun i => (z i).val) ≤
      worth d B δ Y * (degreePrice B γ δ)^m := by
  let A := Fin m → Option (Fin m)
  let g p (z : Fin m → D) := forestWeight X B w a Y p (fun i => (z i).val)
  let t := stretch B γ δ
  let v := worth d B δ Y
  let K := fun (Y : Support n) (i : D) => kernel X B d w a γ δ Y i.val
  let Z := fun i : D => X i.val
  have hi Y i : 0 ≤ K Y i := kernel_pos X B d hw hg hd a _ _
  have hk Y : ∑ i:D, K Y i ≤ 1 := by
    rw [← sum_subtype D (p:=(· ∈ D)) (fun _ => Iff.rfl)
      (kernel X B d w a γ δ Y)]; exact kernel_sum X B d hg hd hh Y D
  have hv : 0 ≤ v := (Real.exp_pos _).le
  have ht : 0 < t := stretch_pos B hg hd
  have hm : 0 < (m.factorial:ℝ) := by positivity
  have he (p : A) : (∑ z, g p z) ≤ v * t^m * fanout p / m.factorial := by
    rw [le_div_iff₀ hm,sum_mul]; by_cases H : Ranked p
    · let q (z : Fin m → D) := ∏ i, K (installed Z Y z (p i)) (z i)
      calc
        _ ≤ ∑ z : Fin m → D, (v * t^m * fanout p) * q z := sum_le_sum fun z _ => by
          unfold g; rw [overlap_eq X B w a Y p _ H,Fintype.card_fin,div_mul_cancel₀ _ hm.ne']
          simpa! only [Fintype.card_fin,q,v,t,K,Z,installed,Function.comp_def] using buy X B d hd hg hw Y p (fun i => (z i).val) a
        _ ≤ _ := by
          rw [← mul_sum]; apply mul_le_of_le_one_right (by positivity)
          exact substochastic Y Z K p H hi hk
    have hz z : g p z = 0 := by simp [g,forestWeight,Sprouts,H]
    simp_rw [hz,zero_mul,sum_const_zero]; positivity
  change ∑ p:A, ∑ z, g p z ≤ _
  calc
    _ ≤ ∑ p:A, v * t^m * fanout p / m.factorial := sum_le_sum fun p _ => he p
    _ = v*t^m*(∑ p:A, (fanout p:ℝ)) / m.factorial := by rw [mul_sum,sum_div]
    _ ≤ v*t^m*((4:ℝ)^m*m.factorial) / m.factorial := by
      gcongr
      exact_mod_cast parent_fanout m
    _ = _ := by unfold degreePrice; change _ = v*(4*t)^m; rw [mul_pow]; field_simp

lemma eave (Y : Support n) {w : ι → ℝ} {a γ δ q : ℝ} (h : Ready X B w a γ δ q) (m : ℕ) : SumBudget (fun z : ForestAt ι m => forestW X B Y w a ⟨m,z⟩) (worth d B δ Y * q^m):=by
  rcases h with ⟨hg,hd,hq,h1,hw,hh⟩
  apply budget_assignments (fun z : _ × (Fin m → ι) => forestWeight X B w a Y z.1 z.2) (fun i => forest_nonneg X B hw a Y i.1 i.2)
  intro D
  have hp : 0 ≤ degreePrice B γ δ := mul_nonneg (by norm_num) (stretch_pos B hg hd).le
  exact (basket X B d m D Y hg hd hw hh).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp hq _) (Real.exp_pos _).le)
noncomputable def hearth (w u:ι→ℝ)(a:ℝ)(z:Root ι):ℝ:= let i:= z.2.1; u i*worth d B a (X i)*forestW X B (X i) w a ⟨z.1,z.2.2⟩
lemma hearth_k {w u : ι → ℝ} {a γ δ q b : ℝ} (hu : ∀ i, 0 ≤ u i) (h : Ready X B w a γ δ q) (he : SumBudget (fun i=>u i* worth d B (a+δ) (X i)) b) (m : ℕ) : SumBudget (fun z : RootAt ι m => hearth X B d w u a ⟨m,z⟩) (b * q^m) := by
  rw [mul_comm b]; refine budget_rows _ (fun i => q^m*(u i * worth d B (a+δ) (X i))) (fun k => ?_) (budget_scale (pow_nonneg (ready_pos X B h).le m) he)
  have hx:= budget_scale (show 0≤u k*worth d B a (X k) from mul_nonneg (hu k) (Real.exp_pos _).le) (eave X B d (X k) h m); apply budget_loosen hx; unfold worth; rw [add_mul, Real.exp_add]; apply le_of_eq; ring
lemma hearth_nn {u w:ι→ℝ}(hw:∀ i,0≤w i)(hu:∀ i,0≤u i)(a:ℝ)(z:Root ι): 0≤ hearth X B d w u a z:=mul_nonneg (mul_nonneg (hu _) (Real.exp_pos _).le) (forestW_nonneg X B _ hw a _)
end YM.UVExtension.Copse
