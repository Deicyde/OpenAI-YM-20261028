import YM.Further.LOCAL_LOG_JETS.Price
import YM.PhysicalNext.INTERPOLATED_SECANTS_FC.JetProducts


/-!
# Mixed jets of actual negative-log tuple contributions

Numbered even at coincidence. Variant of LogJets.Price, but also mixed with same-b retiming
orders through an additional finite scalar degree; needs charts at every Healthy, costs only
where tested. No logarithms taken across hard field gates, no infinite sums differentiated.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InterpolatedSecantsFc.Cluster
open Function Filter Finset Lattice RG Wilson Next.Foundations Push.Local Push.AbsoluteSums Trees Ursell Further.LogJets
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {ι : Type*} {G : Gauge} {n : Side} {Y : ι → Support n} (p : BudgetPoint)

/- Cost at the complete footprint, through N scalar derivatives. -/
def expense (Y : ι → Support n) (c : ι → ℝ) (N : ℕ) (z : Clusters ι) :=
    (1+coversFee Y p z)^N * fee Y p c z

def price (ε γ q : ℝ) (N m : ℕ) := Extra.Multi.Germs.pay p * (Reserves.polyPrice ε (N + orderFee p) * Reserves.treeYield γ q m)

lemma expense_pos (c : ι → ℝ) (hc : ∀ i,0 ≤ c i) (N : ℕ) (z : Clusters ι) : 0 ≤ expense p Y c N z := by
  have := covers_pos Y p z; exact mul_nonneg (by positivity) (fee_pos Y p c hc z)

lemma support_tail (hY : ∀ i, (Y i).Nonempty) {c : ι → ℝ} {ε γ q a δ : ℝ} (he : 0 < ε) (ha : 0 ≤ a)
    (h : Ready Y p.B c (a+2*ε) γ δ q) (x : Site n) (N m : ℕ) :
    SumBudget (fun z : Clusters ι => if m ≤ z.1 ∧ x∈foot Y z then expense p Y c N z * currency p.B a (foot Y z) else 0)
      (price p ε γ q N m) := by
  let z₀ (_ : ι) := (0:ℝ)
  have hh : Ready Y p.B (Reserves.tariff c z₀ z₀ ε) (a+2*ε) γ δ q := by
    simpa only [show Reserves.tariff c z₀ z₀ ε=c by ext; simp [Reserves.tariff,z₀]] using h
  have hp := Reserves.cluster_prices Y p.B c z₀ z₀ (blocked Y) (literal_test Y hY) h.2.2.2.2.1 (fun _ => le_rfl)
    he ha hh m (N+orderFee p) x (fun _ => True) (T:=0) (U:=0) (fun i _ _ _ _=> by
      unfold z₀ Reserves.clusterPrice Reserves.weight; simp; positivity)
  unfold price; convert budget_scale (show 0 ≤ Extra.Multi.Germs.pay p by unfold Extra.Multi.Germs.pay; positivity) hp using 1
  · ext i; by_cases hy : m ≤ i.1 <;> by_cases hx : x∈foot Y i <;> simp [Reserves.occurrence,
      show unionOf Y i.2 = foot Y i from rfl, hx, hy, expense,fee, premium,coversFee,Reserves.clusterPrice,
      Reserves.weight,z₀,pow_add]; ring
  · simp [Reserves.extract]

section Reanchor
variable {c : ι → ℝ} {o : ι → Site n} (ho : ∀ i,o i∈Y i) (z : Clusters ι) (x : Site n) (hx : x∈foot Y z)
include ho
private lemma covers_arity : (((univ : Finset (Option (Fin z.1))).card):ℝ) ≤ 1+coversFee Y p z := by
  apply le_trans (b:=coversFee Y p z) _ (le_add_of_nonneg_left zero_le_one)
  have he i : (1:ℝ) ≤ coverNumber p.B (Y i) := by
    have hv := Corona.pays (Y i) p.B
    have hp := card_pos.mpr (show (Y i).Nonempty from ⟨o i,ho i⟩)
    exact_mod_cast (show 1 ≤ coverNumber p.B (Y i) by by_contra! hh; rw [Nat.lt_one_iff.mp hh,zero_mul] at hv; omega)
  simpa [coversFee] using Finset.sum_le_sum (s:=univ) (f:=fun _ : Option (Fin z.1) => (1:ℝ)) fun i _ => he (z.2 i)

private def shift (Y : ι → Support n) (z : Clusters ι) := ((4*(p.B:ℝ)+2)*(1+coversFee Y p z))^p.power
omit ho in
private lemma shift_pos : 1 ≤ shift p Y z := by
  have h := covers_pos Y p z
  exact one_le_pow₀ (one_le_mul_of_one_le_of_one_le (by have := Nat.cast_nonneg (α:=ℝ) p.B; linarith) (by linarith))
include hx in
private lemma reanchor (hz : scalarWeight Y z ≠ 0) {v : Directions G n} (hv : p.dirBound x v) (i : Option (Fin z.1)) :
    p.dirBound (o (z.2 i)) ((shift p Y z)⁻¹ • v) := by
  have he := connected_pay (blocked Y) Y p.B (literal_test Y (fun i => ⟨_,ho i⟩)) z.2 zero_le_one (show coefficient _ _ ≠ 0 from
    fun he => hz (by simp [scalarWeight,he]))
  have h : (coverNumber p.B (foot Y z):ℝ) ≤ coversFee Y p z := by simpa [currency,←Real.exp_sum,coversFee] using he
  have hd : (separation (o (z.2 i)) x:ℝ) ≤ coverNumber p.B (foot Y z)*((4:ℝ)*p.B+2)+2*(p.B:ℝ) := by
    exact_mod_cast Corona.extent _ p.B (covered Y z i (ho _)) hx
  rw [shift, ← inv_pow]; refine Extra.Multi.Germs.relocate_dir ?_ hv
  nlinarith [Nat.cast_nonneg (α:=ℝ) p.B]

private lemma tariff (hc : ∀ i,0≤c i) {k m N : ℕ} (hk : k ≤ p.order) (hm : m ≤ N) :
    (shift p Y z)^k * (|scalarWeight Y z| * ((Fintype.card (Option (Fin z.1)):ℝ)^(k+m) * ∏ i,c (z.2 i))) ≤ expense p Y c N z := by
  let s := shift p Y z; let v := 1+coversFee Y p z; let d : ℝ := Fintype.card (Option (Fin z.1))
  have hv : 1 ≤ v := le_add_of_nonneg_right (covers_pos Y p z)
  have hh := shift_pos p (Y:=Y) z
  have hx := Finset.prod_nonneg (s:=Finset.univ) fun i _ => hc (z.2 i)
  rw [expense,quota]
  calc
    _ = (s^k * d^(k+m)) * (|scalarWeight Y z| * ∏ i,c (z.2 i)) := by ring
    _ ≤ ((s*v)^p.order * v^N) * (|scalarWeight Y z| * ∏ i,c (z.2 i)) := by
      gcongr ?_ * _
      rw [pow_add, ← mul_assoc (s^k), ← mul_pow]; have hi : d ≤ v := covers_arity p ho z
      gcongr
      · exact (pow_le_pow_left₀ (mul_nonneg (zero_le_one.trans hh) (Nat.cast_nonneg _)) (mul_le_mul_of_nonneg_left hi (zero_le_one.trans hh)) k).trans
          (pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le hh hv) hk)
      exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hi m).trans (pow_le_pow_right₀ hv hm)
    _ = _ := by unfold premium orderFee Extra.Multi.Germs.pay s v shift; rw [pow_mul,pow_succ]; simp only [mul_pow]; ring

variable {E E' : ι → Field G n} {U : Config G n} (hu : Healthy p.threshold (foot Y z) U)
include hx hu
lemma part_change {δ : ℝ} (hδ : 0≤δ) (hC : ∀ i,0 ≤ c i)
    (hf : ∀ i, Healthy p.threshold (Y i) U → Chart p.order (E i) U ∧ Chart p.order (E' i) U)
    (hh : ∀ i, Healthy p.threshold (Y i) U → ∀ l : List (Directions G n), l.length ≤ p.order → (∀ a∈l,p.dirBound (o i) a) →
      |leftDerivs (E i) l U| ≤ c i ∧ |leftDerivs (E' i) l U| ≤ c i ∧
        |leftDerivs (E i) l U - leftDerivs (E' i) l U| ≤ δ*c i)
    (l : List (Directions G n)) (hl : l.length ≤ p.order) (hd : ∀ a∈l,p.dirBound x a) :
    |leftDerivs (part Y E z) l U - leftDerivs (part Y E' z) l U| ≤ δ * expense p Y (fun i => 2*c i) 0 z := by
  have hy i : Healthy p.threshold (Y (z.2 i)) U := Disjoint.mono_left (covered Y z i) hu
  let v := scalarWeight Y z; let s := shift p Y z
  rw [cost_eq,cost_eq,left_constant_mul,left_constant_mul]; dsimp only []; rw [← mul_sub,abs_mul]
  change |v| * _ ≤ _
  by_cases he : v=0
  · rw [he,abs_zero,zero_mul]; exact mul_nonneg hδ (expense_pos p _ (fun i => mul_nonneg zero_le_two (hC _)) ..)
  have hs : 0<s := zero_lt_one.trans_le (shift_pos p z)
  have h := product_change univ (D:=fun a : Directions G n => ∀ i, p.dirBound (o (z.2 i)) a) hδ (fun i _ => hf _ (hy i))
    (fun i _ L hl hd => hh (z.2 i) (hy i) L hl (fun a ha => hd a ha i)) (l.map (s⁻¹ • ·)) (by simpa)
    (fun a ha i => by obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ha; exact reanchor p ho z x hx he (hd q hq) i)
  have h1 : Chart p.order (fun U => ∏ i,E (z.2 i) U) U := contDiffAt_prod fun i _ => (hf _ (hy i)).1
  have h2 : Chart p.order (fun U => ∏ i,E' (z.2 i) U) U := contDiffAt_prod fun i _ => (hf _ (hy i)).2
  rw [List.length_map,left_homogeneous l h1 hl,left_homogeneous l h2 hl,← smul_sub,smul_eq_mul,_root_.inv_pow,inv_mul_eq_div,
    abs_div,abs_of_pos (pow_pos hs _),div_le_iff₀ (pow_pos hs _)] at h
  have he := tariff p ho z (fun i => mul_nonneg zero_le_two (hC i)) hl (le_refl 0)
  rw [Nat.add_zero] at he
  rw [Finset.card_univ] at h; change s^l.length*(|v| * _) ≤ _ at he
  linarith only [mul_le_mul_of_nonneg_left h (abs_nonneg v),mul_le_mul_of_nonneg_left he hδ]

variable {f : ℝ → ι → Field G n}
omit hx hu ho in
private lemma shrink (L : List (Directions G n)) : ∃ s : ℝ, 1 ≤ s ∧ ∀ a ∈ L.map (s⁻¹ • ·), ∀ i, p.dirBound (o i) a := by
  obtain ⟨u,hu,ht⟩ := can_shrink p L
  let s := max 1 u⁻¹
  have hs : 0<s := zero_lt_one.trans_le (le_max_left ..)
  have he : s⁻¹ ≤ u := by rw [inv_le_comm₀ hs hu]; exact le_max_right ..
  refine ⟨s,le_max_left ..,fun a ha i j => ?_⟩
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ha
  refine le_trans ?_ (ht (o i) v hv j)
  simp only [Pi.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs),abs_of_pos hu]; gcongr

omit ho hx in
lemma part_continuous {r : Set ℝ} (hf : ∀ t∈r, ∀ i, Healthy p.threshold (Y i) U → Chart p.order (f t i) U)
    (hh : ∀ i, Healthy p.threshold (Y i) U → ∀ l : List (Directions G n), l.length ≤ p.order → (∀ a∈l,p.dirBound (o i) a) →
        ContinuousOn (fun t => leftDerivs (f t i) l U) r)
    (l : List (Directions G n)) (hl : l.length ≤ p.order) : ContinuousOn (fun t => leftDerivs (part Y (f t) z) l U) r := by
  have hy i : Healthy p.threshold (Y (z.2 i)) U := Disjoint.mono_left (covered Y z i) hu
  obtain ⟨s,hs,hD⟩ := shrink p (o:=o) l
  have h := left_product_continuous univ (D:=fun a : Directions G n => ∀ i,p.dirBound (o (z.2 i)) a)
    (fun t ht i _ => hf t ht _ (hy i)) (fun i _ L hl hd => hh (z.2 i) (hy i) L hl (fun a ha => hd a ha i))
    (l.map (s⁻¹ • ·)) (by simpa) (fun a ha i => hD a ha _)
  refine ((h.const_mul (scalarWeight Y z)).const_mul (s^l.length)).congr (fun t ht => ?_)
  rw [cost_eq,left_constant_mul]; dsimp only []; rw [left_homogeneous l (by exact contDiffAt_prod fun i _ => hf t ht _ (hy i)) hl]
  simp only [smul_eq_mul,inv_pow]; field_simp

set_option maxHeartbeats 500000 in
lemma mixed_part {t : ℝ} (N : ℕ) (hc : ∀ i,0 ≤ c i) (hf : ∀ᶠ t in 𝓝 t, ∀ i, Healthy p.threshold (Y i) U → Chart p.order (f t i) U)
    (hh : ∀ i, Healthy p.threshold (Y i) U → ∀ l : List (Directions G n), l.length ≤ p.order → (∀ a∈l,p.dirBound (o i) a) →
        let F := fun t => leftDerivs (f t i) l U
        ContDiffAt ℝ N F t ∧ ∀ j ≤ N, |iteratedDeriv j F t| ≤ c i)
    (l : List (Directions G n)) (hl : l.length ≤ p.order) (hd : ∀ a∈l,p.dirBound x a) :
    let F := fun t => leftDerivs (part Y (f t) z) l U
    ContDiffAt ℝ N F t ∧ ∀ j ≤ N, |iteratedDeriv j F t| ≤ expense p Y c N z := by
  intro F
  have hF u : F u = scalarWeight Y z * leftDerivs (fun U => ∏ i,f u (z.2 i) U) l U := by simp only [F,cost_eq,left_constant_mul]
  by_cases he : scalarWeight Y z=0
  · simp only [funext hF, he,zero_mul,contDiffAt_const,true_and,iteratedDeriv_fun_const_zero, abs_zero]; exact fun j _ => expense_pos p c hc ..
  have hy i : Healthy p.threshold (Y (z.2 i)) U := Disjoint.mono_left (covered Y z i) hu
  let s := shift p Y z
  have hs : 0<s := zero_lt_one.trans_le (shift_pos p z)
  let g u := leftDerivs (fun U => ∏ i,f u (z.2 i) U) (l.map (s⁻¹ • ·)) U
  have H : F =ᶠ[𝓝 t] fun u => s^l.length * (scalarWeight Y z * g u) := by
    filter_upwards [hf] with u hu
    unfold g; rw [hF,left_homogeneous l (by exact contDiffAt_prod fun i _ => hu _ (hy i)) hl,smul_eq_mul,inv_pow]
    field_simp
  have h := mixed_product univ (D:=fun a : Directions G n => ∀ i,p.dirBound (o (z.2 i)) a)
    (hf.mono (fun t ht i _ => ht _ (hy i))) (N:=N) (fun i _ L hl hd => hh (z.2 i) (hy i) L hl (fun a ha => hd a ha i)) (l.map (s⁻¹ • ·))
      (by simpa) (fun a ha i => by obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ha; exact reanchor p ho z x hx he (hd q hq) i)
  change ContDiffAt ℝ N g t ∧ _ at h
  refine ⟨(contDiffAt_const.mul (contDiffAt_const.mul h.1)).congr_of_eventuallyEq H,fun j hj => ?_⟩
  rw [H.iteratedDeriv_eq, iteratedDeriv_const_mul_field,iteratedDeriv_const_mul_field, abs_mul,abs_of_pos (pow_pos hs _),abs_mul]
  have hb := h.2 j hj; rw [Finset.card_univ,List.length_map] at hb
  exact le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (abs_nonneg _)) (pow_pos hs _).le) (tariff p ho z hc hl hj)
end Reanchor
end YM.PhysicalNext.InterpolatedSecantsFc.Cluster
