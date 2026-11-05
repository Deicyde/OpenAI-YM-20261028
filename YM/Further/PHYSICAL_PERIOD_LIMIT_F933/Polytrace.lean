import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Jacobi
import YM.Push.STATIONARY_UNIFORM.Slope


/-! # Counting on stationary loops

From true full-integrand/lifting estimates of STATIONARY_UNIFORM.
There is no factor proportional to #Free (which grows also with p)
in the intensive bounds here. Don't assume a ghost decomposition in
perturbation theory; we do a position estimate first.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Polytrace
open Push.Uniform Jacobi Function Filter Finset Lattice Matrix
open scoped Topology BigOperators ContDiff Classical
variable {ι κ : Type} [Fintype ι] [Fintype κ] {f : Positions (ι ⊕ κ) → ℝ} {x : Positions (ι⊕κ)}
    {n : Side}

lemma echogram (hf : ContDiffAt ℝ ω f x) : Faces (block f) x := fun i j => (tend_entry hf ![Sum.inr j,Sum.inr i]).1
lemma echogram₁ (hf : ContDiffAt ℝ ω f x) (i) (k j : κ) : delta (bolt i) (block f) x k j = entry f x ![i,Sum.inr j, Sum.inr k] := by
  have he := (tend_entry hf ![Sum.inr j,Sum.inr k]).2 i
  exact he
lemma echogram₂ (hf : ContDiffAt ℝ ω f x) (i i') (k j : κ) : delta (bolt i) (delta (bolt i') (block f)) x k j = entry f x ![i,i',Sum.inr j, Sum.inr k] := by
  have he : (fun y => delta (bolt i') (block f) y k j) =ᶠ[𝓝 x] (fun y => entry f y ![i',Sum.inr j,Sum.inr k]) := (hf.eventually (by simp)).mono (fun _ h => echogram₁ h _ _ _)
  change blade .. = _; rw [blade,he.fderiv_eq]; exact (tend_entry hf _).2 i

lemma fee {a b : ℝ} (h : b≤a) (i j : Site n) : Decay a i j ≤ Decay b i j := by
  unfold Decay; rw [Real.exp_le_exp]; gcongr
lemma separate {a b c : ℝ} (h : b+c≤a) (i j : Site n) : Decay a i j ≤ Decay b i j * Decay c i j := by
  refine (fee h _ _).trans_eq ?_; unfold Decay; rw [← Real.exp_add]; congr 1; ring

variable {l : ι ⊕ κ → Site n} {a t C : ℝ} {K N : ℕ}
abbrev space (K : ℕ) (a : ℝ) := (K:ℝ)*countCost a
lemma space_pos (K : ℕ) {a : ℝ} (hp : 0<a) : 0≤space K a := mul_nonneg (by positivity) (count_pos hp).le

local notation "loc" => l ∘ (@Sum.inr ι κ)

lemma chamber (h : Scatter l a N f x C) (hc : ContDiffAt ℝ ω f x) (he : 4≤N) (v w) (i j) :
    let d := Decay (n:=n) a
    ‖delta (bolt v) (block f) x i j‖ ≤ C*(d (l v) (loc j)*d (l v) (loc i)) ∧
    ‖delta (bolt v) (delta (bolt w) (block f)) x i j‖ ≤ C*(d (l v) (l w)*d (l v) (loc j)*d (l v) (loc i)) := by
  intro d; rw [echogram₁ hc,echogram₂ hc]
  have h1 := h 3 (le_trans (by norm_num) he) ![v,Sum.inr j, Sum.inr i] 0
  have h2 := h 4 he ![v,w,Sum.inr j, Sum.inr i] 0
  have comp (j : κ) : loc j = l (Sum.inr j) := rfl
  simpa [d,Decay, Real.exp_add, mul_add, Fin.sum_univ_succ,spanSites,Nat.cast_add,mul_assoc,comp] using And.intro h1 h2

section Pin
variable {m : κ→Site n} {d : ℝ} {P : Matrix κ κ ℝ}
    {B : ℝ} {p : Site n}

-- account at p location, can be either mutation
lemma intensive (hp : 0<t) (hc : 0≤C) (hm : Multiplicity m K)
    (h : ∀ i j, ‖P i j‖ ≤ C*(Decay t p (m j)*Decay t p (m i))) :
    ∑ i,∑ j, ‖P i j‖ ≤ C*(space K t * space K t) := by
  let D := Decay t p
  apply le_trans (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _=>h i j)))
  calc
    _ = C*((∑ i, D (m i))*∑ j,D (m j)) := by
      simp_rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]; rfl
    _ ≤ C*_ := by
      gcongr
      · exact Finset.sum_nonneg fun _ _ => (decay_pos ..).le
      any_goals exact space_pos K hp
      all_goals exact hm.count _ hp _

lemma traced (hf : ∀ i j, |P i j| ≤ B) {U : Matrix κ κ ℝ} (h : ∑i,∑j, ‖U i j‖ ≤ C) (hq : 0≤B) :
    ‖Matrix.trace (P*U)‖ ≤ B*C := by
  unfold trace; simp only [diag_apply, Matrix.mul_apply]; rw [Real.norm_eq_abs]
  apply le_trans (Finset.abs_sum_le_sum_abs ..)
  apply le_trans (Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _))
  calc
    _ ≤ ∑ i,∑ j,B*‖U j i‖ := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
      rw [abs_mul,Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_right (hf ..) (by positivity)
    _ ≤ B*C := by rw [Finset.sum_comm]; simp_rw [← Finset.mul_sum]; gcongr

private lemma rope (hp : 0≤a) (p q x y : Site n) : Decay a p x * Decay a x y * Decay a q y ≤ Decay a p q := by
  rw [decay_comm a q y]
  apply (mul_le_mul_of_nonneg_right (decay_step hp ..) (decay_pos ..).le).trans (decay_step hp ..)

-- Matrix bubble: Any two indices around can be first. Free payments not n^4.
-- Use tiny t chosen jointly even if real birth gap etc very different from loop path widths.
lemma exchange (hp : 0<t) (ht : t+t≤a) (hd : t≤d) {U V : Matrix κ κ ℝ}
    {q : Site n} (hc : 0≤C) (hB : 0≤B) (hU : ∀ i j, ‖U i j‖ ≤ C*(Decay a p (m j)*Decay a p (m i)))
    (hV : ∀ i j, ‖V i j‖ ≤ C*(Decay a q (m j)*Decay a q (m i)))
    (hs : Sealed m d P B) (hm : Multiplicity m K) :
    ‖Matrix.trace (P*U*P*V)‖ ≤ B^2*C^2*(space K t*(space K t*(space K t*space K t)))*Decay t p q := by
  let D := Decay (n:=n) t
  let Q := space K t
  have hy x y : 0≤D x y := (decay_pos ..).le
  let L := B^2*C^2*D p q
  have H (i j k b : κ) : |P i j*U j k*P k b*V b i| ≤ L*(D q (m i)*(D p (m k)*(D p (m j)* D q (m b)))) := by
    let x := m i; let y := m j; let z := m k; let u := m b
    have he i j : |P i j| ≤ B := (hs _ _).trans (mul_le_of_le_one_right hB (decay_le (hp.le.trans hd) ..))
    have hm : |P k b| ≤ B*D z u := (hs _ _).trans (mul_le_mul_of_nonneg_left (fee hd ..) hB)
    have h1 : |U j k| ≤ C*(D p z*D p z*D p y) := (hU j k).trans (by
      gcongr
      · exact (decay_pos ..).le
      · exact mul_nonneg (hy ..) (hy ..)
      · exact separate ht ..
      exact fee (le_trans (le_add_of_nonneg_left hp.le) ht) ..)
    have h2 : |V b i| ≤ C*(D q x*(D q u*D q u)) := (hV b i).trans (by
      gcongr
      · exact (decay_pos ..).le
      · exact hy ..
      · exact fee (le_trans (le_add_of_nonneg_left hp.le) ht) ..
      exact separate ht ..)
    rw [abs_mul,abs_mul,abs_mul]; apply ((mul_le_mul (mul_le_mul
      (mul_le_mul (he i j) h1 (abs_nonneg _) hB) hm (abs_nonneg _) (mul_nonneg hB (mul_nonneg hc (by
      have := hy p z; have := hy p y; positivity)))) h2 (abs_nonneg _) (by
      have := hy p z; have := hy p y; have := hy z u; positivity))).trans
    unfold L
    change _ ≤ _*(D q x*(D p z*(D p y*D q u)))
    calc
      _ = B^2*C^2*(D p z*D z u*D q u)*(D q x*(D p z*(D p y*D q u))) := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (rope hp.le p q _ _) (by positivity))
        have := hy p z; have := hy p y; have := hy q u; have := hy q x; positivity
  unfold trace; simp_rw [diag_apply,mul_apply,Finset.sum_mul]; rw [Real.norm_eq_abs]
  apply le_trans (abs_sum_le_sum_abs ..)
  apply le_trans (Finset.sum_le_sum (fun _ _ => abs_sum_le_sum_abs _ _))
  apply le_trans (Finset.sum_le_sum fun _ _ => Finset.sum_le_sum (fun _ _ => abs_sum_le_sum_abs _ _))
  apply le_trans (Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => Finset.sum_le_sum (fun _ _ => abs_sum_le_sum_abs _ _))
  have hx := space_pos K hp
  calc
    _ ≤ ∑ (i:κ),∑ b:κ,∑ k:κ,∑ j:κ,L*(D q (m i)*(D p (m k)*(D p (m j)* D q (m b)))) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun j _=> H i j k b
    _ = L*((∑ i:κ,D q (m i))*((∑ b:κ,D q (m b))*((∑ k:κ,D p (m k))*∑ j:κ,D p (m j)))) := by
      simp_rw [Finset.sum_mul, Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; refine Finset.sum_congr rfl fun b _ => ?_; refine Finset.sum_congr rfl fun k _ => ?_; refine Finset.sum_congr rfl fun j _ => ?_; ring
    _ ≤ L*(Q*(Q*(Q*Q))) := by
      have hL : 0≤L := mul_nonneg (by positivity) (hy ..)
      have hq := Finset.sum_nonneg (s:=(Finset.univ: Finset κ)) (f:=fun i => D q (m i)) (fun i _ => hy q (m i)); have hh := Finset.sum_nonneg (s:=(Finset.univ: Finset κ)) (f:=fun i => D p (m i)) (fun i _ => hy p (m i)); change 0≤Q at hx
      gcongr <;> try positivity
      any_goals exact hm.count m hp _
    _ = _ := by unfold L Q; ring
end Pin

abbrev determinantLog (f : Positions (ι⊕κ) → ℝ) (x) := Real.log ((block f x).det)

-- keep price usable before period; additive bound for i=j etc
def feeVac (C B : ℝ) (K : ℕ) (t : ℝ) :=
  let Q := space K t
  B*C*Q*Q + B^2*C^2*(Q*(Q*(Q*Q)))
lemma feeVac_nonneg (K : ℕ) (he : 0≤C) {B : ℝ} (ht : 0≤B) (hp : 0<t) : 0 ≤ feeVac C B K t := by
  have := space_pos K hp; unfold feeVac; positivity

-- sometimes separated spectral analysts prefer from own inverse Hgap with a suitable uniform rate; don't take it arbitrarily away
set_option maxHeartbeats 200000 in
lemma bared (h : Scatter l a N f x C) (hc : ContDiffAt ℝ ω f x) (he : 4≤N) (hf : 0 ≤ C)
    {B d : ℝ} (hm : Multiplicity l K) (hv : (block f x).det ≠ 0) (hp : 0<t) (ht : t+t≤a) (hd : t≤d) (hb : 0≤B)
    (hh : Sealed loc d (block f x)⁻¹ B) (i j : ι ⊕ κ) :
    ‖blade (bolt i) (determinantLog f) x‖ ≤ feeVac C B K t ∧
    ‖mixed (bolt i) (bolt j) (determinantLog f) x‖ ≤ feeVac C B K t * Decay t (l i) (l j) := by
  let Q := space K t
  let R := (block f x)⁻¹
  let D := Decay (n:=n) t
  have hx (i j) := chamber h hc he i j
  have hK : Multiplicity loc K := hm.comp Sum.inr_injective
  have hs s y : |R s y| ≤ B := (hh _ _).trans (mul_le_of_le_one_right hb (decay_le (hp.le.trans hd) _ _))
  have hf' := echogram hc
  have hz : t ≤ a := by linarith
  have hl (j k : Site n) := mul_nonneg hf (decay_pos t j k).le
  have hX i j : 0 ≤ D i j := (decay_pos ..).le
  have hQ : 0 ≤ Q := space_pos _ hp
  constructor
  · unfold determinantLog; rw [stroke _ hf' hv]; apply (traced hs (C:=C*(Q*Q)) _ hb).trans
    · change _ ≤ B*C*Q*Q+B^2*C^2*(Q*(Q*(Q*Q))); linarith only [mul_nonneg (mul_nonneg (sq_nonneg B) (sq_nonneg C)) (show 0 ≤ Q*(Q*(Q*Q)) by positivity)]
    apply intensive hp hf hK (p:=l i) fun a b => ?_
    apply ((hx i j _ _).1).trans
    gcongr
    · exact (decay_pos ..).le
    · exact (decay_pos ..).le
    all_goals exact fee hz ..
  unfold determinantLog; rw [tranche _ _ hf' hv]
  apply le_trans (norm_sub_le ..)
  change _ ≤ (B*C*Q*Q + B^2*C^2*(Q*(Q*(Q*Q)) )) * D (l i) (l j)
  rw [add_mul]
  have hZ := exchange hp ht hd (m:=loc) (p:=l i) (q:=l j) (P:=R) (K:=K)
      (U:=delta (bolt i) (block f) x) (V:=delta (bolt j) (block f) x) hf hb (fun s y => (hx i i s y).1) (fun s y=>(hx j j s y).1) hh hK
  apply add_le_add _ hZ
  apply (traced hs (intensive hp (hl (l i) (l j)) hK (p:=l i) ?_) hb).trans
  · exact le_of_eq (by ring)
  intro s y
  refine ((hx i j s y).2).trans ?_
  simp_rw [mul_assoc]
  gcongr
  all_goals first | exact fee hz .. | exact (decay_pos ..).le | exact mul_nonneg (decay_pos ..).le (decay_pos ..).le
end YM.Further.PhysicalPeriodLimitF933.Polytrace
