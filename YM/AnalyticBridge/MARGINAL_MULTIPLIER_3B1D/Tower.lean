import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Jets
import YM.Bid.Craft
import YM.Next.BOUNDARY.Synchronize
import YM.Next.FOUNDATIONS.SU2

/-!
Finite smooth nonlinear price transfer for sectors, including stability when the
outer evaluation point or even the read changes (one real germ estimate on
each tower and a modulus across their actual base points suffices). Keep the
*value* in the exponential rather than exponentiating the high-jet budget.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.MarginalMultiplier3b1d
open Function Filter Set Lattice RG Wilson Push.Local Next.Foundations
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side}
section linear
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : Config G n} {k : ℕ} {D : Directions G n → Prop} {a b K : ℝ}
    {f f' : Config G n → E} {g g' : Config G n → F}

lemma Bound.map (h : Bound k D V f a K) (L : E →L[ℝ] F) {c : ℝ} (hc : 0 ≤ c) (ht : ∀ x, ‖L x‖ ≤ c*‖x‖) :
    Bound k D V (fun W => L (f W)) (c*a) K := by
  refine ⟨L.contDiff.contDiffAt.comp _ h.smooth, mul_nonneg hc h.nn,h.size,fun l hl he => ?_⟩
  change ‖leftDerivs (L ∘ f) l V‖ ≤ _
  rw [left_linear _ _ h.smooth hl,mul_assoc]; exact (ht _).trans (mul_le_mul_of_nonneg_left (h.pays _ hl he) hc)
lemma Compare.map (h : Compare k D V f f' a b K) (L : E →L[ℝ] F) {c : ℝ} (hc : 0 ≤ c) (ht : ∀ x, ‖L x‖ ≤ c*‖x‖) :
    Compare k D V (fun W => L (f W)) (fun W => L (f' W)) (c*a) (c*b) K :=
  ⟨h.west.map L hc ht,h.east.map L hc ht,by simpa using h.swing.map L hc ht⟩
lemma Compare.smul_const_left (h : Compare k D V f f' a b K) (r : ℝ) :
    Compare k D V (fun W => r • f W) (fun W => r • f' W) (|r| * a) (|r| * b) K :=
  h.map (r • ContinuousLinearMap.id ℝ E) (abs_nonneg _) (fun x => (norm_smul r x).le)
lemma Bound.prod_mk (h : Bound k D V f a K) (hh : Bound k D V g a K) : Bound k D V (fun W => (f W,g W)) a K := by
  have hf : Chart k (fun W => (f W,g W)) V := h.smooth.prodMk hh.smooth
  refine ⟨hf,h.nn,h.size,fun l hl he => ?_⟩
  have h1 := left_linear (ContinuousLinearMap.fst ℝ E F) l hf hl
  have h2 := left_linear (ContinuousLinearMap.snd ℝ E F) l hf hl
  change leftDerivs f l V = (leftDerivs (fun W => (f W,g W)) l V).1 at h1
  change leftDerivs g l V = (leftDerivs (fun W => (f W,g W)) l V).2 at h2
  rw [Prod.norm_def]; exact max_le (h1 ▸ h.pays l hl he) (h2 ▸ hh.pays l hl he)
lemma Compare.prod_mk (h : Compare k D V f f' a b K) (e : Compare k D V g g' a b K) :
    Compare k D V (fun W => (f W,g W)) (fun W => (f' W,g' W)) a b K :=
  ⟨h.west.prod_mk e.west,h.east.prod_mk e.east,h.swing.prod_mk e.swing⟩
lemma Bound.pi {ι : Type*} [Fintype ι] {f : Config G n → ι → E} (h : ∀ i, Bound k D V (fun W => f W i) a K) (ha : 0 ≤ a) (hK : 0 ≤ K) : Bound k D V f a K := by
  have hf : Chart k f V := contDiffAt_pi.mpr fun i => (h i).smooth
  refine ⟨hf,ha,hK,fun l hl he => (pi_norm_le_iff_of_nonneg (mul_nonneg ha (pow_nonneg hK _))).mpr fun i => ?_⟩
  have ht := left_linear (ContinuousLinearMap.proj i) l hf hl
  rw [show leftDerivs f l V i = leftDerivs (fun W => f W i) l V from ht.symm]; exact (h i).pays l hl he
lemma Compare.pi {ι : Type*} [Fintype ι] {f g : Config G n → ι → E} (h : ∀ i, Compare k D V (fun W => f W i) (fun W => g W i) a b K)
    (ha : 0≤a) (hb : 0≤b) (hK : 0≤K) : Compare k D V f g a b K :=
  ⟨Bound.pi (fun i => (h i).west) ha hK,Bound.pi (fun i => (h i).east) ha hK,Bound.pi (fun i => (h i).swing) hb hK⟩

lemma Bound.next (hf : Chart (k+1) f V) (h : ‖f V‖ ≤ a) (he : ∀ v, D v → Bound k D V (leftDerivs f [v]) a 1) : Bound (k+1) D V f a 1 := by
  refine ⟨hf,(norm_nonneg _).trans h,zero_le_one,fun l hl hh => ?_⟩
  simp only [one_pow,mul_one]; induction l using List.reverseRecOn with
  | nil => exact h
  | append_singleton l v _ =>
    rw [Work.G07.left_append]; exact (he v (hh _ (by simp))).simple l (by simpa using hl) (fun _ hv => hh _ (by simp [hv]))

lemma Compare.next (hf : Chart (k+1) f V) (hg : Chart (k+1) f' V)
    (h : ‖f V‖ ≤ a) (h' : ‖f' V‖ ≤ a) (ht : ‖f V-f' V‖ ≤ b)
    (H : ∀ v, D v → Compare k D V (leftDerivs f [v]) (leftDerivs f' [v]) a b 1) : Compare (k+1) D V f f' a b 1 := by
  refine ⟨Bound.next hf h (fun v hv => (H v hv).west),Bound.next hg h' (fun v hv => (H v hv).east), Bound.next (hf.sub hg) ht (fun v hv => ?_)⟩
  have he {w : Config G n → E} (hw : Chart (k+1) w V) : ∀ᶠ y : Directions G n in 𝓝 0, Chart 1 w (increment V y) :=
    chart_eventually (by rw [Work.G07.at_zero_increment]; exact hw.of_le (Nat.cast_le.mpr (Nat.le_add_left 1 k))) (fun i => by
      simp only [increment,G.mat_mul]; exact ((G.exp_jet.comp (contDiff_apply ..)).mul contDiff_const).contDiffAt)
  apply (H v hv).swing.congr
  filter_upwards [he hf,he hg] with y hx hy
  exact ((left_has v (l:=[]) (by simp) hx).sub (left_has v (l:=[]) (by simp) hy)).deriv
end linear

section tower
universe u
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

structure Towers (k : ℕ) (φ ψ : E → F) (x y : E) (c d : ℝ) : Prop where
  west : ContDiffAt ℝ (k : WithTop ℕ∞) φ x
  east : ContDiffAt ℝ (k : WithTop ℕ∞) ψ y
  along (i : ℕ) : i ≤ k → ‖iteratedFDeriv ℝ i φ x‖ ≤ c ∧ ‖iteratedFDeriv ℝ i ψ y‖ ≤ c ∧
    ‖iteratedFDeriv ℝ i φ x-iteratedFDeriv ℝ i ψ y‖ ≤ d

variable {k : ℕ} {φ ψ : E → F} {x y : E} {c d : ℝ}

lemma Towers.zero (h : Towers k φ ψ x y c d) : ‖φ x‖ ≤ c ∧ ‖ψ y‖ ≤ c ∧ ‖φ x - ψ y‖ ≤ d := by
  simpa only [iteratedFDeriv_zero_eq_comp,comp_apply,← map_sub,LinearIsometryEquiv.norm_map] using h.along 0 (Nat.zero_le _)
lemma Towers.nn (h : Towers k φ ψ x y c d) : 0 ≤ c ∧ 0 ≤ d := ⟨(norm_nonneg _).trans h.zero.1,(norm_nonneg _).trans h.zero.2.2⟩
lemma Towers.step (h : Towers (k+1) φ ψ x y c d) : Towers k (fderiv ℝ φ) (fderiv ℝ ψ) x y c d := by
  refine ⟨h.west.fderiv_right (by simp),h.east.fderiv_right (by simp),fun i hi => ?_⟩
  have he := h.along (i+1) (Nat.add_le_add_right hi 1)
  let L := (continuousMultilinearCurryRightEquiv' ℝ i E F).symm
  simp only [iteratedFDeriv_succ_eq_comp_right, comp_apply] at he
  refine ⟨(L.norm_map _).symm.trans_le he.1, (L.norm_map _).symm.trans_le he.2.1, (L.norm_map _).symm.trans_le ?_⟩
  rw [L.map_sub]; exact he.2.2
lemma Towers.within {s : Set E} (hf : ∀ x ∈ s, ContDiffAt ℝ (↑(k+1:ℕ)) φ x)
    (hp : ∀ x∈s, ∀ i ≤ k+1, ‖iteratedFDeriv ℝ i φ x‖ ≤ c) (hs : Convex ℝ s) (hx : x∈s) (hy : y∈s) (hxy : ‖x-y‖ ≤ d) :
    Towers k φ φ x y c (c*d) := by
  refine ⟨(hf x hx).of_le (Nat.cast_le.mpr k.le_succ),(hf y hy).of_le (Nat.cast_le.mpr k.le_succ),fun i hi => ?_⟩
  have he z (hz : z∈s) := hf z hz |>.differentiableAt_iteratedFDeriv (Nat.cast_lt.mpr (hi.trans_lt k.lt_succ_self))
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le he (fun z hz => (norm_fderiv_iteratedFDeriv).trans_le (hp z hz _ (Nat.add_le_add_right hi 1))) hs hy hx
  exact ⟨hp x hx i (by omega),hp y hy i (by omega), h.trans (mul_le_mul_of_nonneg_left hxy ((norm_nonneg _).trans (hp x hx i (by omega))))⟩

def compositionCost (k : ℕ) (a : ℝ) := (2^k*(1+a))^k
lemma compositionCost_one {a : ℝ} (k : ℕ) (ha : 0≤a) : 1 ≤ compositionCost k a := by
  exact one_le_pow₀ (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (by linarith))
lemma compositionCost_append {a : ℝ} (k : ℕ) (ha : 0≤a) :
    compositionCost k a * (1+a) * 2^k ≤ compositionCost (k+1) a := by
  unfold compositionCost; rw [mul_assoc,mul_comm (1+a),← pow_succ]; gcongr <;> norm_num

variable {D : Directions G n → Prop} {V : Config G n} {f g : Config G n → E} {a b : ℝ}
lemma first_chain {φ : E → F} (h : Chart (k+1) f V) (hf : ContDiffAt ℝ (↑(k+1:ℕ)) φ (f V)) (v : Directions G n) :
    leftDerivs (φ ∘ f) [v] ∘ increment V =ᶠ[𝓝 0] (fun W => fderiv ℝ φ (f W) (leftDerivs f [v] W)) ∘ increment V := by
  have he : ∀ᶠ y : Directions G n in 𝓝 0, Chart 1 f (increment V y) :=
    chart_eventually (by rw [Work.G07.at_zero_increment]; exact h.of_le (Nat.cast_le.mpr (Nat.le_add_left 1 k))) (fun i => by
      simp only [increment,G.mat_mul]; exact ((G.exp_jet.comp (contDiff_apply ..)).mul contDiff_const).contDiffAt)
  have hh : Tendsto (f ∘ increment V) (𝓝 0) (𝓝 (f V)) := by simpa only [comp_apply,Work.G07.at_zero_increment] using h.continuousAt.tendsto
  filter_upwards [he,hh.eventually (hf.eventually (by simp))] with y hy ht
  have ht : DifferentiableAt ℝ φ (f (increment V y)) := ht.differentiableAt (by exact_mod_cast Nat.succ_ne_zero k)
  exact ((show DifferentiableAt ℝ φ (f (increment (increment V y) ((0:ℝ) • v))) by rw [zero_smul,Work.G07.at_zero_increment]; exact ht).hasFDerivAt.comp_hasDerivAt 0 (left_has v (l:=[]) (by simp) hy)).deriv.trans (by rw [zero_smul,Work.G07.at_zero_increment]; rfl)

lemma Compare.chain (h : Compare k D V f g a b 1) (hh : Towers k φ ψ (f V) (g V) c d) :
    Compare k D V (φ ∘ f) (ψ ∘ g) (compositionCost k a*c) (compositionCost k a*(d+k*c*b)) 1 := by
  have ha := h.west.nn; have hb := h.swing.nn
  have hc := hh.nn.1; have hd := hh.nn.2
  induction k generalizing F with
  | zero =>
    have hw := hh.west; have he := hh.east; rw [← Work.G07.at_zero_increment V] at hw he
    simp only [compositionCost,pow_zero,Nat.cast_zero,zero_mul,add_zero,one_mul]
    have Hf : Chart 0 (φ ∘ f) V := hw.comp (f:=f ∘ increment V) 0 h.west.smooth
    have Hg : Chart 0 (ψ ∘ g) V := he.comp (f:=g ∘ increment V) 0 h.east.smooth
    refine ⟨⟨Hf,hc,zero_le_one,?_⟩,⟨Hg,hc,zero_le_one,?_⟩,⟨Hf.sub Hg,hd,zero_le_one,?_⟩⟩
    all_goals
      intro l hl _
      rw [Nat.le_zero,List.length_eq_zero_iff] at hl
      subst l; simp only [one_pow,mul_one,leftDerivs,comp_apply]; first | exact hh.zero.1 | exact hh.zero.2.1 | exact hh.zero.2.2
  | succ k ih =>
    have hw := hh.west; have he := hh.east
    have hC := compositionCost_one (k+1) ha
    have ht := compositionCost_append k ha
    let T := compositionCost k a
    let T' := compositionCost (k+1) a
    -- smooth at chart centers
    rw [← Work.G07.at_zero_increment V] at hw he
    apply Compare.next (hw.comp (f:=f ∘ increment V) 0 h.west.smooth) (he.comp (f:=g ∘ increment V) 0 h.east.smooth)
      (hh.zero.1.trans (le_mul_of_one_le_left hc hC)) (hh.zero.2.1.trans (le_mul_of_one_le_left hc hC))
      (hh.zero.2.2.trans (by exact (le_add_of_nonneg_right (by positivity)).trans (le_mul_of_one_le_left (by positivity) hC)))
    intro v hv
    have H := ih (h.lower k.le_succ) hh.step
    have H' := (H.apply_clm (h.first hv)).congr (first_chain h.west.smooth hh.west v) (first_chain h.east.smooth hh.east v)
    refine (H'.flatten (by norm_num)).weaker ?_ ?_ le_rfl
    · change T*c*a*(1+1)^k ≤ T'*c
      have hT : 0≤T := zero_le_one.trans (compositionCost_one _ ha)
      calc
        _ ≤ T*(1+a)*2^k*c := by norm_num; nlinarith [show 0≤2^k*T*c by positivity]
        _ ≤ _ := mul_le_mul_of_nonneg_right ht hc
    · change (T*(d+k*c*b)*a+T*c*b)*(1+1)^k ≤ T'*(d+((k+1:ℕ):ℝ)*c*b)
      have hT : 0≤T := zero_le_one.trans (compositionCost_one _ ha)
      push_cast
      calc
        _ ≤ T*(1+a)*2^k*(d+(k+1)*c*b) := by norm_num; nlinarith [show 0≤T*d*2^k by positivity, show 0≤T*a*c*b*2^k by positivity, show 0≤T*k*c*b*2^k by positivity]
        _ ≤ _ := mul_le_mul_of_nonneg_right ht (by positivity)
end tower

lemma Compare.exp {k : ℕ} {D : Directions G n → Prop} {V : Config G n} {f g : Config G n → ℝ} {a b M : ℝ} (h : Compare k D V f g a b 1) (hf : f V ≤ M) (hg : g V ≤ M) :
    Compare k D V (fun W => Real.exp (f W)) (fun W => Real.exp (g W)) (compositionCost k a*Real.exp M) (compositionCost k a*((1+k)*Real.exp M*b)) 1 := by
  have hh := Towers.within (k:=k) (φ:=Real.exp) (s:=Iic M) (fun _ _ => Real.contDiff_exp.contDiffAt)
    (fun x hx i _ => by rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,Real.norm_of_nonneg (Real.exp_pos _).le]; exact Real.exp_monotone hx)
    (convex_Iic M) hf hg h.swing.value
  have he : Real.exp M * b + k*Real.exp M*b = (1+k)*Real.exp M*b := by ring
  rw [← he]; exact h.chain hh
end YM.AnalyticBridge.MarginalMultiplier3b1d
