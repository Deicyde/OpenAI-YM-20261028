import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Tower
import YM.Next.ROTATIONS.Response
import YM.Next.SCHEDULE.Postal
import YM.Push.CUTOFF_PROJECTORS.Bank
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.ResidualPrice


/-!
Elementary finite-marginal price transfers (NOT a trace or ordered chain
expansion over a period). Polynomial overhead in the number of *queried*
coordinates at fixed differential order. No differentiating a choice of
window. Need estimates on the actual entries / smooth on-sector versions.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.MarginalMultiplier3b1d.FiniteMatrix
open Function Filter Lattice RG Wilson Push.Local Next.Foundations Finset Matrix
  Next.SectorChange Next.SectorChange.Gaussian
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {ι : Type} [Fintype ι] [DecidableEq ι]

def Upper (A : Gaussian.Table ι) (a : ℝ) := ∀ i j, |A i j| ≤ a
lemma Upper.flare {a : ℝ} {A : Gaussian.Table ι} (h : Upper A a) : ResidualPrice.flared (Fintype.card ι*a) A :=
  fun j => (sum_le_sum (fun i (_:i∈univ) => h i j)).trans_eq (by simp)
lemma Upper.times {A B : Gaussian.Table ι} {a b : ℝ} (h : Upper A a) (h' : Upper B b) : Upper (A*B) (Fintype.card ι*(a*b)) := fun i j =>
  (abs_sum_le_sum_abs ..).trans ((sum_le_sum (fun r (_:r∈univ) => (abs_mul _ _).trans_le <| mul_le_mul (h i r) (h' r j) (abs_nonneg _) ((abs_nonneg _).trans (h i r)))).trans_eq (by simp))

variable {D : Directions G n → Prop} {V : Config G n} {k : ℕ} {A B : Config G n → Gaussian.Table ι} {K H a b : ℝ}

abbrev Entries (k : ℕ) (D : Directions G n → Prop) (V : Config G n) (A B : Config G n → Gaussian.Table ι) (a b : ℝ) :=
  ∀ i j : ι, Compare k D V (fun W => A W i j) (fun W => B W i j) a b 1

lemma mat_chart (h : Entries k D V A B a b) : Chart k A V ∧ Chart k B V := by
  let L : (ι → ι → ℝ) ≃L[ℝ] Gaussian.Table ι := (ofLinearEquiv ℝ).toContinuousLinearEquiv
  have he (A : Config G n → Gaussian.Table ι) (h : ∀ i j, Chart k (fun W => A W i j) V) : Chart k A V := by
    refine L.contDiff.contDiffAt.comp (f:=fun W i j => A (increment V W) i j) 0 ?_
    exact contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr (h i)
  exact ⟨he A fun i j => (h i j).west.smooth,he B fun i j => (h i j).east.smooth⟩

def innerRate (A : Config G n → Gaussian.Table ι) (v : Directions G n) : Config G n → Gaussian.Table ι :=
  fun W => Matrix.of fun i j => leftDerivs (fun W => A W i j) [v] W
lemma inner_eq (A : Config G n → Gaussian.Table ι) (v : Directions G n) (h : Chart 1 A V) : innerRate A v V = leftDerivs A [v] V := by
  ext i j
  exact left_linear (FreeResolvent.TestD.evaluate i j) [v] h le_rfl
lemma inv_left (h : Chart 1 A V) (ht : IsUnit (A V)) (v : Directions G n) (i j : ι) :
    leftDerivs (fun W => (A W)⁻¹ i j) [v] V = -(((A V)⁻¹ * innerRate A v V * (A V)⁻¹) i j) := by
  let L := FreeResolvent.TestD.evaluate i j
  let T := ht.unit
  have he := hasFDerivAt_ringInverse (𝕜:=ℝ) T
  have hx : Ring.inverse (T : Gaussian.Table ι) = (A V)⁻¹ := (Matrix.nonsing_inv_eq_ringInverse _).symm
  rw [Ring.inverse_unit] at hx
  rw [hx] at he
  have ho := left_has v (l:=[]) (by simp) h
  rw [show (T:Gaussian.Table ι)= A (increment V ((0:ℝ) • v)) by simp only [zero_smul,Work.G07.at_zero_increment]; rfl] at he
  have H := L.hasFDerivAt.comp_hasDerivAt 0 (he.comp_hasDerivAt 0 ho)
  rw [inner_eq A v h,leftDerivs]; simp_rw [Matrix.nonsing_inv_eq_ringInverse]
  exact H.deriv.trans (by change -((A V)⁻¹ * _ * (A V)⁻¹) i j = _; simp_rw [Matrix.nonsing_inv_eq_ringInverse])

lemma inv_chart (h : Chart k A V) (ht : IsUnit (A V)) (i j : ι) : Chart k (fun W => (A W)⁻¹ i j) V := by
  let L := FreeResolvent.TestD.evaluate (ι:=ι) (κ:=ι) i j
  have he : ContDiffAt ℝ (k : WithTop ℕ∞) Ring.inverse (A (increment V 0)) := by rw [Work.G07.at_zero_increment]; exact contDiffAt_ringInverse ℝ ht.unit
  simp_rw [Matrix.nonsing_inv_eq_ringInverse]; exact L.contDiff.contDiffAt.comp 0 (he.comp (f:=A ∘ increment V) 0 h)

lemma mat_near (h : Chart (k+1) A V) (ht : IsUnit (A V)) :
    ∀ᶠ y in 𝓝 (0:Directions G n), Chart 1 A (increment V y) ∧ IsUnit (A (increment V y)) := by
  have he : ∀ᶠ y in 𝓝 (0:Directions G n), Chart 1 A (increment V y) := chart_eventually
    (by rw [Work.G07.at_zero_increment]; exact h.of_le (Nat.cast_le.mpr (Nat.le_add_left 1 k))) (fun i => by
      simp only [increment,G.mat_mul]; exact ((G.exp_jet.comp (contDiff_apply ..)).mul contDiff_const).contDiffAt)
  exact he.and (h.continuousAt.eventually (Units.isOpen.mem_nhds (by simpa only [Set.mem_setOf,Function.comp_apply,Work.G07.at_zero_increment] using ht)))
lemma inv_germ (v : Directions G n) (h : Chart (k+1) A V) (ht : IsUnit (A V)) (i j : ι) :
    leftDerivs (fun W => (A W)⁻¹ i j) [v] ∘ increment V =ᶠ[𝓝 0]
      (fun W => -∑ s,∑ t, (A W)⁻¹ i t * innerRate A v W t s * (A W)⁻¹ s j) ∘ increment V := by
  filter_upwards [mat_near h ht] with y ⟨hy,hU⟩
  simp only [Function.comp_apply,inv_left hy hU v,Matrix.mul_apply,Finset.sum_mul]

-- determinant at identity along a physical curve in marginal matrices
private lemma det_one {Z : ℝ → Gaussian.Table ι} {z : Gaussian.Table ι} (h : ∀ i j, HasDerivAt (fun t => Z t i j) (z i j) 0)
    (he : Z 0=1) : HasDerivAt (fun t => (Z t).det) (∑ i, z i i) 0 := by
  classical
  have H (p : Equiv.Perm ι) : HasDerivAt (fun t => Equiv.Perm.sign p • ∏ i, Z t (p i) i) (if p=1 then ∑ i, z i i else 0) 0 := by
    have hx := HasDerivAt.finsetProd (u:=Finset.univ) fun i _ => h (p i) i
    have hg := hx.const_smul (Equiv.Perm.sign p)
    rw [he] at hg
    simp_rw [Pi.smul_def,Finset.prod_apply,smul_eq_mul] at hg
    split
    next he =>
      subst p
      change HasDerivAt _ (Equiv.Perm.sign (1:Equiv.Perm ι) • ∑ x, (∏ j ∈ univ.erase x, (1:Gaussian.Table ι) j j) * z x x) _ at hg
      simpa using hg
    next hh =>
      have ht (i : ι) : (∏ j ∈ univ.erase i, (1:Gaussian.Table ι) (p j) j)=0 := by
        by_contra hne
        have hfix (j) (hj : j≠i) : p j=j := by
          by_contra hn; apply hne; exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hj,mem_univ _⟩) (Matrix.one_apply_ne hn)
        apply hh; ext j; by_cases hj : j=i
        · subst j; by_contra H; exact H (p.injective (hfix _ H))
        exact hfix j hj
      simpa [ht] using hg
  simp_rw [Matrix.det_apply]; simpa using (HasDerivAt.fun_sum (u:=univ) fun p _ => H p)

lemma det_smooth (A : Config G n → Gaussian.Table ι) (h : Chart k A V) : Chart k (fun W => det (A W)) V := by
  unfold Chart
  simp only [Function.comp_def, Matrix.det_apply]
  apply ContDiffAt.sum; intro p _
  have he : ContDiffAt ℝ (↑k) (fun W => ∏ i, A (increment V W) (p i) i) 0 := contDiffAt_prod fun i _ =>
    (FreeResolvent.TestD.evaluate (p i) i).contDiff.contDiffAt.comp 0 h
  simp only [Units.smul_def]
  rcases Int.units_eq_one_or (Equiv.Perm.sign p) with hp|hp <;> simp [hp]; exacts [he,he.neg]
lemma log_germ (v : Directions G n) (h : Chart (k+1) A V) (ht : IsUnit (A V)) :
    leftDerivs (fun W => Real.log (A W).det) [v] ∘ increment V =ᶠ[𝓝 0]
      (fun W => ∑ i, ∑ j, (A W)⁻¹ i j * innerRate A v W j i) ∘ increment V := by
  filter_upwards [mat_near h ht] with y ⟨hy,hu⟩
  set w := increment V y
  let f (t : ℝ) := increment w (t • v)
  have hf : f 0 = w := by unfold f; rw [zero_smul,Work.G07.at_zero_increment]
  let L := A w
  have he : IsUnit L.det := (Matrix.isUnit_iff_isUnit_det _).mp hu
  let Z (t : ℝ) := L⁻¹ * A (f t)
  have hz : Z 0=1 := by unfold Z; rw [hf]; exact Matrix.nonsing_inv_mul _ he
  have hx : HasDerivAt Z (L⁻¹ * innerRate A v w) 0 := (inner_eq A v hy).symm ▸ (left_has v (l:=[]) (by simp) hy).const_mul (L⁻¹)
  have hZ i j : HasDerivAt (fun t => Z t i j) ((L⁻¹ * innerRate A v w) i j) 0 := (FreeResolvent.TestD.evaluate i j).hasFDerivAt.comp_hasDerivAt 0 hx
  have H := (det_one hZ hz).mul_const L.det
  have hW t : (Z t).det * L.det = (A (f t)).det := by unfold Z; rw [det_mul,det_nonsing_inv,Ring.inverse_eq_inv,mul_right_comm, inv_mul_cancel₀ he.ne_zero,one_mul]
  simp_rw [hW] at H
  have he' := H.log (f:=fun t => (A (f t)).det) (show (A (f 0)).det≠0 by rw [hf]; exact he.ne_zero)
  rw [hf, show (A w).det=L.det from rfl, mul_div_cancel_right₀ _ he.ne_zero] at he'
  exact he'.deriv

-- inversion budgets with polynomial price per-order and linear in the variation budget

def stock (N : ℕ) (a H : ℝ) : ℕ → ℝ
  | 0 => H
  | k+1 => H+(N:ℝ)^2 * stock N a H k * a * stock N a H k * 3^k
def reaction (N : ℕ) (a H : ℝ) : ℕ → ℝ
  | 0 => (N:ℝ)^2*H^2
  | k+1 => let L:=stock N a H k; let M:=reaction N a H k
           (N:ℝ)^2*H^2+(N:ℝ)^2*((M*a+L)*L+L*a*M)*3^k
lemma stock_nn (N k : ℕ) {a H : ℝ} (h : 0≤a) (he : 0≤H) : 0≤stock N a H k ∧ 0≤reaction N a H k := by
  induction k with
  | zero => exact ⟨he,by unfold reaction; positivity⟩
  | succ k ih => rw [stock,reaction]; obtain ⟨h,h'⟩:=ih; constructor <;> positivity

lemma inverse_sub {A B : Gaussian.Table ι} (h : IsUnit A) (hh : IsUnit B) : A⁻¹ - B⁻¹ = A⁻¹ * (B-A) * B⁻¹ := by
  rw [Matrix.mul_sub, Matrix.sub_mul,Matrix.mul_assoc,Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hh), Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp h), Matrix.mul_one, Matrix.one_mul]
lemma inverse_jets (h : Entries k D V A B a b) (ha : 0≤a) (hb : 0≤b) (hH : 0≤H)
    (hA : IsUnit (A V)) (hB : IsUnit (B V)) (hR : Upper (A V)⁻¹ H) (hS : Upper (B V)⁻¹ H) :
    Entries k D V (fun W => (A W)⁻¹) (fun W => (B W)⁻¹) (stock (Fintype.card ι) a H k) (reaction (Fintype.card ι) a H k*b) := by
  let N := Fintype.card ι
  have he : Upper (B V-A V) b := fun i j => (abs_sub_comm ..).trans_le (h i j).swing.value
  have hδ : Upper ((A V)⁻¹-(B V)⁻¹) ((N:ℝ)^2*H^2*b) := by
    rw [inverse_sub hA hB]
    exact show Upper _ _ from (show (N:ℝ)*(N*(H*b)*H)=(N:ℝ)^2*H^2*b by ring) ▸ ((hR.times he).times hS)
  induction k with
  | zero =>
    have h₁ i j := inv_chart (mat_chart h).1 hA i j
    have h₂ i j := inv_chart (mat_chart h).2 hB i j
    intro i j
    refine ⟨⟨h₁ i j,hH,zero_le_one,?_⟩,⟨h₂ i j,hH,zero_le_one,?_⟩,⟨(h₁ i j).sub (h₂ i j),mul_nonneg (stock_nn _ _ ha hH).2 hb,zero_le_one,?_⟩⟩
    all_goals intro l hl _; rw [Nat.le_zero,List.length_eq_zero_iff] at hl; subst l; rw [one_pow,mul_one]
    exacts [hR i j,hS i j,hδ i j]
  | succ k ih =>
    let T := stock N a H k; let E := reaction N a H k
    have ⟨ht,he⟩ := stock_nn N k ha hH
    have ht : H ≤ stock N a H (k+1) := by rw [stock]; exact le_add_of_nonneg_right (by positivity)
    have he' : (N:ℝ)^2*H^2 ≤ reaction N a H (k+1) := by rw [reaction]; exact le_add_of_nonneg_right (by positivity)
    have h₁ i j := inv_chart (mat_chart h).1 hA i j
    have h₂ i j := inv_chart (mat_chart h).2 hB i j
    intro i j
    apply Compare.next (h₁ i j) (h₂ i j) ((hR i j).trans ht) ((hS i j).trans ht) ((hδ i j).trans (mul_le_mul_of_nonneg_right he' hb))
    intro v hv
    specialize ih (fun i j => (h i j).lower k.le_succ)

    have H i j := (h i j).first hv
    let g (A : Config G n → Gaussian.Table ι) (W : Config G n) := -∑ s,∑ t,(A W)⁻¹ i t*innerRate A v W t s*(A W)⁻¹ s j
    have three : (3:ℝ)=1+1+1 := by norm_num
    have hg : Compare k D V (g A) (g B) (N*(N*(T*a*T))) (N*(N*((E*b*a+T*b)*T+(T*a)*(E*b)))) 3 := Compare.neg <| Compare.univ (fun s => Compare.univ
      (fun t => three.symm ▸ (((ih i t).mul (H t s)).mul (ih s j))) (by norm_num)) (by norm_num)
    refine ((hg.flatten (by norm_num)).congr (inv_germ v (mat_chart h).1 hA i j) (inv_germ v (mat_chart h).2 hB i j)).weaker ?_ ?_ le_rfl
    · rw [stock]; exact le_trans (le_of_eq (show (N*(N*(T*a*T)))*3^k=(N:ℝ)^2*T*a*T*3^k by ring)) (le_add_of_nonneg_left hH)
    · refine le_trans (le_of_eq (show (N*(N*((E*b*a+T*b)*T+(T*a)*(E*b))))*3^k=(N:ℝ)^2*((E*a+T)*T+T*a*E)*3^k*b by ring)) ?_
      rw [reaction]; change _ ≤ (_^2*_^2+(N:ℝ)^2*((E*a+T)*T+T*a*E)*3^k)*b; rw [add_mul _ (_*3^k)]; exact le_add_of_nonneg_left (by positivity)

section amount
variable {A B : Gaussian.Table ι}
lemma log_le (h : ResidualPrice.flared (1+a) A) (ha : 0 ≤ a) (hA : 0 < A.det) : Real.log A.det ≤ Fintype.card ι*a := by
  apply (Real.log_le_log hA ((le_abs_self _).trans (ResidualPrice.det_pay h))).trans
  rw [Real.log_pow]; gcongr; exact (Real.log_le_sub_one_of_pos (by linarith)).trans_eq (by ring)
lemma log_change (ha : A.PosDef) (hb : B.PosDef) (h : Upper B⁻¹ H) (he : Upper (A-B) b) (hh : 0≤H) (hδ : 0≤b) :
    Real.log A.det - Real.log B.det ≤ (Fintype.card ι:ℝ)^3*H*b := by
  let N : ℝ := Fintype.card ι
  have hx : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det _).mp hb.isUnit
  have hB : B⁻¹.det=B.det⁻¹ := (Matrix.det_nonsing_inv _).trans (Ring.inverse_eq_inv _)
  have hy : A*B⁻¹=1+(A-B)*B⁻¹ := by rw [Matrix.sub_mul,B.mul_nonsing_inv hx]; abel
  have hr : ResidualPrice.flared (1+N*(N*(b*H))) (A*B⁻¹) := fun j => by
    rw [hy]
    calc
      _ ≤ ∑ i, (|(1:Gaussian.Table ι) i j|+|((A-B)*B⁻¹) i j|) := sum_le_sum fun _ _ => abs_add_le ..
      _ = 1 + ∑ i, |((A-B)*B⁻¹) i j| := by rw [sum_add_distrib]; simp [Matrix.one_apply,apply_ite abs]
      _ ≤ _ := add_le_add le_rfl ((he.times h).flare _)
  have hp : 0<(A*B⁻¹).det := by rw [Matrix.det_mul,hB]; exact mul_pos ha.det_pos (inv_pos.mpr hb.det_pos)
  have hv := log_le hr (by unfold N; positivity) hp
  rw [Matrix.det_mul,hB,Real.log_mul ha.det_pos.ne' (inv_pos.mpr hb.det_pos).ne',Real.log_inv,← sub_eq_add_neg] at hv
  exact hv.trans_eq (by unfold N; ring)
lemma log_abs (ha : A.PosDef) (h : Upper A a) (h' : Upper A⁻¹ H) (he : 0≤a) (hh : 0≤H) :
    |Real.log A.det| ≤ (Fintype.card ι:ℝ)^2*(a+H) := by
  let N : ℝ := Fintype.card ι
  have hx {B : Gaussian.Table ι} (hb : 0 < B.det) (ht : Upper B (a+H)) : Real.log B.det ≤ N^2*(a+H) := by
    apply (log_le (a:=N*(a+H)) (fun j => (ht.flare j).trans (le_add_of_nonneg_left zero_le_one)) (by unfold N; positivity) hb).trans_eq
    unfold N; ring
  have he' := hx ha.det_pos (fun i j => (h i j).trans (le_add_of_nonneg_right hh))
  have hh' := hx (ha.inv.det_pos) (fun i j => (h' i j).trans (le_add_of_nonneg_left he))
  rw [det_nonsing_inv,Ring.inverse_eq_inv,Real.log_inv] at hh'; exact abs_le.mpr ⟨neg_le.mp hh',he'⟩
end amount

def logCost (N : ℕ) (a H : ℝ) (k : ℕ) := (N:ℝ)^2*((a+H)+stock N a H k*a*2^k)
def logReaction (N : ℕ) (a H : ℝ) (k : ℕ) := (N:ℝ)^3*H+(N:ℝ)^2*(reaction N a H k*a+stock N a H k)*2^k
lemma logCost_nn (N k : ℕ) (ha : 0≤a) (hH : 0≤H) : 0 ≤ logCost N a H k ∧ 0 ≤ logReaction N a H k := by
  have ⟨h,h'⟩ := stock_nn N k ha hH
  unfold logCost logReaction; constructor <;> positivity

lemma log_jets (h : Entries k D V A B a b) (ha : 0≤a) (hb : 0≤b) (hH : 0≤H)
    (hA : (A V).PosDef) (hB : (B V).PosDef) (hR : Upper (A V)⁻¹ H) (hS : Upper (B V)⁻¹ H) :
    Compare k D V (fun W => Real.log (A W).det) (fun W => Real.log (B W).det)
      (logCost (Fintype.card ι) a H k) (logReaction (Fintype.card ι) a H k*b) 1 := by
  let N := Fintype.card ι
  have ⟨h₁,h₂⟩ := mat_chart h
  have h₁' : Chart k (fun W => Real.log (A W).det) V := (det_smooth A h₁).log (by simp only [Function.comp_apply,Work.G07.at_zero_increment]; exact hA.det_pos.ne')
  have h₂' : Chart k (fun W => Real.log (B W).det) V := (det_smooth B h₂).log (by simp only [Function.comp_apply,Work.G07.at_zero_increment]; exact hB.det_pos.ne')
  have ⟨ht,he⟩ := stock_nn N k ha hH
  have hl : (N:ℝ)^2*(a+H) ≤ logCost N a H k := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (sq_nonneg _)
  have hV := (log_abs hA (fun i j => (h i j).west.value) hR ha hH).trans hl
  have hV' := (log_abs hB (fun i j => (h i j).east.value) hS ha hH).trans hl
  have hl' : (N:ℝ)^3*H ≤ logReaction N a H k := le_add_of_nonneg_right (by positivity)
  have hδ : |Real.log (A V).det - Real.log (B V).det| ≤ logReaction N a H k*b := by
    apply le_trans ?_ (mul_le_mul_of_nonneg_right hl' hb)
    have hw := log_change hB hA hR (fun i j => (abs_sub_comm ..).trans_le (h i j).swing.value) hH hb
    rw [abs_le]; exact ⟨by unfold N; linarith, log_change hA hB hS (fun i j => (h i j).swing.value) hH hb⟩
  have ⟨h0,h0'⟩:=logCost_nn N k ha hH
  cases k with
  | zero =>
    refine ⟨⟨h₁',h0,zero_le_one,?_⟩,⟨h₂',h0,zero_le_one,?_⟩,⟨h₁'.sub h₂',mul_nonneg h0' hb,zero_le_one,?_⟩⟩
    all_goals intro l hl _; rw [Nat.le_zero,List.length_eq_zero_iff] at hl; subst l; rw [one_pow,mul_one]
    exacts [hV,hV',hδ]
  | succ k =>
    apply Compare.next h₁' h₂' hV hV' hδ; intro v hv
    let T := stock N a H (k+1); let E := reaction N a H (k+1)
    have IH i j := (inverse_jets h ha hb hH hA.isUnit hB.isUnit hR hS i j).lower k.le_succ
    have H i j := (h i j).first hv
    let g (A : Config G n → Gaussian.Table ι) W := ∑ i, ∑ j, (A W)⁻¹ i j * innerRate A v W j i
    have hg : Compare k D V (g A) (g B) (N*(N*(T*a))) (N*(N*(E*b*a+T*b))) (1+1) := Compare.univ (fun i => Compare.univ
      (fun j => (IH i j).mul (H j i)) (by norm_num)) (by norm_num)
    refine ((hg.flatten (by norm_num)).congr (log_germ v h₁ hA.isUnit) (log_germ v h₂ hB.isUnit)).weaker ?_ ?_ le_rfl
    · change _ ≤ (N:ℝ)^2*((a+_)+T*a*2^(k+1)); norm_num; rw [pow_succ (2:ℝ) k]; nlinarith only [show 0≤(N:ℝ)^2*a by positivity,show 0≤(N:ℝ)^2*_ by apply mul_nonneg (sq_nonneg _) hH,show 0≤(N:ℝ)^2*T*a*2^k by positivity]
    change _ ≤ ((N:ℝ)^3*_+(N:ℝ)^2*(E*a+T)*2^(k+1))*b
    calc
      _ ≤ (N:ℝ)^2*(E*a+T)*2^(k+1)*b := by rw [show (1+1:ℝ)=2 by norm_num,pow_succ (2:ℝ) k]; nlinarith only [show 0≤(N:ℝ)^2*(E*a+T)*2^k*b by positivity]
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) hb
end YM.AnalyticBridge.MarginalMultiplier3b1d.FiniteMatrix
