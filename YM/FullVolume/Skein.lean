import YM.FullVolume.Cohort

/-! Arithmetic lattice averages for detectors. Averaging only in the
*first* slot and only for the axes in a requested difference. This way the
detector uses exactly the fixed scaled positions/bases of the norm-bounded
purchases, and summation by parts of the tested higher differences doesn't
yet need any limiting convergence result. Integers throughout. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume
open Filter Function Set Lattice RG Wilson Extraction Extraction.Lease Difference
open Push.RelayDifference
open scoped BigOperators Topology ContDiff

abbrev Positions (m:ℕ) := Fin m → Cover
variable {ι:Type*}[AddCommGroup ι] {m:ℕ}

/-- single normalized increment difference -/
def delta (u:ι) (t:ℝ) : (ι→ℂ) →ₗ[ℂ] (ι→ℂ) where
  toFun f x:= (t:ℂ)⁻¹ * (f (x+u)-f x)
  map_add' f g:= by ext x:1; simp; ring
  map_smul' c f:= by ext x:1; simp; ring

@[simp] lemma delta_at (f:ι→ℂ) (u:ι) (t:ℝ) (x:ι):delta u t f x= (t:ℂ)⁻¹ * (f (x+u)-f x) := rfl

def blur (u:ι) (n:ℕ) : (ι→ℂ) →ₗ[ℂ] (ι→ℂ) where
  toFun f x:= (n:ℂ)⁻¹ * ∑ j∈Finset.range n, f (x+j • u)
  map_add' f g:= by ext x:1; simp [Finset.sum_add_distrib,mul_add]
  map_smul' c f:= by ext x:1; simp [Finset.mul_sum,mul_left_comm]

@[simp] lemma blur_at (f:ι→ℂ) (u:ι) (n:ℕ) (x:ι):blur u n f x=(n:ℂ)⁻¹ * ∑ j∈Finset.range n, f (x+j • u):=rfl

lemma blurred {n:ℕ}(hn:0<n)(f:ι→ℂ)(x u:ι){v:ℝ}(h:∀ j:ℕ, j < n→ ‖f (x+j • u)‖ ≤ v):
    ‖blur u n f x‖ ≤ v:=by
  rw [blur_at,norm_mul,norm_inv,Complex.norm_natCast]
  apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) (by positivity : (0:ℝ)≤ (n:ℝ)⁻¹)).trans
  apply (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj=>h j (Finset.mem_range.mp hj)) (by positivity)).trans_eq
  simp [nsmul_eq_mul, hn.ne']

lemma same_delta (x u:ι)(t:ℝ)(n:ℕ)(f:ι→ℂ) :
    blur u n (delta u t f) x = ((n:ℂ)*(t:ℂ))⁻¹ * (f (x+n • u)- f x):=by
  simp_rw [blur_at, delta_at (f:=f), ← Finset.mul_sum]; simp_rw [show ∀ i:ℕ,x + i • u + u=x+(i+1) • u from fun i=> by rw [add_assoc,add_smul,one_smul]]
  rw [Finset.sum_range_sub (fun i=> f (x+i • u))] -- adjust succ
  simp [mul_comm (t:ℂ)⁻¹,← mul_assoc]
  ring

lemma next_delta (u v:ι)(t:ℝ)(n:ℕ)(f:ι→ℂ):blur u n (delta v t f)=delta v t (blur u n f):=by
  ext x:1; simp only [blur_at, delta_at f, delta_at (blur u n f)]
  simp_rw [add_right_comm x _ v,← Finset.mul_sum,Finset.sum_sub_distrib]; ring

/- Use same integer length in every average in each detector. -/
variable (t:ℝ) (a: ℕ)

def blurs : List ι → ((ι→ℂ) →ₗ[ℂ] (ι→ℂ))
  | [] => LinearMap.id
  | i::l => (blur i a).comp (blurs l)

def deltas (t:ℝ): List ι → ((ι→ℂ) →ₗ[ℂ] (ι→ℂ))
  | [] => LinearMap.id
  | i::l=> (delta i t).comp (deltas t l)

lemma thru (i:ι)(l:List ι)(f:ι→ℂ): blurs a l (delta i t f)=delta i t (blurs a l f):=by
  induction l with
  | nil=> rfl
  | cons j l ih => change blur j a (blurs a _ _) = _; rw [ih,next_delta j i t a]; rfl

/-- Convenience: unit mesh shift at the first slot. -/
def tick (i:Axis) : Positions (m+1):= Pi.single 0 (step i)

lemma stride (x: Positions (m+1)) (u e): x+e • tick u=advance x 0 u e:=by
  ext i : 1
  by_cases hi:i=0 <;> simp [tick,advance,hi]

section bounds
variable (l:List Axis)

lemma rounds (ha:0<a) (ht:0<t) (p:Points (m+1)) {R b v:ℝ} (hh : t*a ≤ b) (f:Positions (m+1)→ℂ)
    (h:∀ x, dist (tag t x) p ≤ R → ‖f x‖ ≤ v) (x: Positions (m+1)) (hx: dist (tag t x) p ≤ R - l.length*b) :
    ‖blurs a (l.map tick) f x‖≤ v:=by
  induction l generalizing x R with
  | nil => exact h x (by simpa using hx)
  | cons i l ih =>
    change ‖blur (tick i) a _ x‖≤_
    apply blurred ha; intro j hj; apply ih h
    have he: t*j≤b := le_trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hj.le) ht.le) hh
    simp only [List.length_cons,Nat.cast_add, Nat.cast_one] at hx; rw [stride]
    exact le_trans (dist_triangle _ (tag t x) _) (by rw [extent _ _ _ _ _ ht]; linarith only [he,hx])

lemma reserve_abs (_ha:0<a)(ht:0<t) (p:Points (m+1)) {R b v r:ℝ} (hr:0<r) (hk : r ≤ a*t) (hh:a*t ≤ b) (f:Positions (m+1)→ℂ) (_hv:0 ≤ v)
    (h:∀ x, dist (tag t x) p ≤ R → ‖f x‖ ≤ v) (x: Positions (m+1)) (hx: dist (tag t x) p ≤ R - l.length*b) :
    ‖blurs a (l.map tick) (deltas t (l.map tick) f) x‖ ≤ (2/r)^l.length * v:=by
  induction l generalizing x R with
  | nil=> simpa using! h x (by simpa using hx)
  | cons i l ih =>
    simp only [List.map_cons,blurs,deltas,LinearMap.comp_apply]; rw [thru, same_delta,norm_mul,norm_inv,norm_mul,Complex.norm_natCast,Complex.norm_real, Real.norm_of_nonneg ht.le]
    simp only [List.length_cons,Nat.cast_add, Nat.cast_one] at hx
    have he:dist (tag t (x+a • tick i)) p ≤ R - l.length*b := by
      rw [stride]; exact le_trans (dist_triangle _ (tag t x) _) (by rw [extent _ _ _ _ _ ht]; linarith)
    have hi:=ih h _ he; have hp:=ih h x (by linarith)
    apply (mul_le_mul (inv_anti₀ hr hk) ((norm_sub_le ..).trans (add_le_add hi hp)) (norm_nonneg _) (inv_pos.mpr hr).le).trans_eq
    rw [List.length_cons,pow_succ]; ring

lemma blur_fixed (ha:0<a) (l:List ι)(c:ℂ): blurs a l (fun _=>c)=(fun _=>c):=by
  induction l with
  | nil=> rfl
  | cons i l ih =>
    change blur _ a _ = _; rw [ih]; ext:1; simp [nsmul_eq_mul, ha.ne']

lemma closer (ha:0<a)(ht:0<t)(p:Points (m+1)){R b v:ℝ}(hh:t*a ≤ b)(f: Positions (m+1)→ℂ)
    (x:Positions (m+1))(hp:∀ y, dist (tag t y) p ≤ R → dist (f y) (f x) ≤ v)
    (hx:dist (tag t x) p ≤ R- l.length*b) : dist (blurs a (l.map tick) f x) (f x) ≤ v:=by
  have h':= rounds t a l ha ht p hh (f-(fun _=> f x)) (fun y hy=> by simpa only [dist_eq_norm (f y) _] using! hp y hy) x hx
  rw [map_sub,blur_fixed a ha,Pi.sub_apply] at h'; simpa [dist_eq_norm] using h'
end bounds

/-- Length set in lattice units. -/
def steps (S:Schedule) (d:ℝ) (N:ℕ) := ⌈d/S.a N⌉₊
lemma step_upper (S:Schedule) {d:ℝ} (hd:0<d): ∀ᶠ N in atTop, 0< steps S d N ∧ d ≤ steps S d N*S.a N ∧ steps S d N*S.a N ≤ 2*d :=by
  filter_upwards [S.shrinks.eventually (ge_mem_nhds hd)] with N hn
  unfold steps; have he := S.a_pos N; have hx := Nat.ceil_lt_add_one (div_nonneg hd.le he.le)
  refine ⟨Nat.ceil_pos.mpr (by positivity), (div_le_iff₀ he).mp (Nat.le_ceil _), ?_⟩
  exact (mul_le_mul_of_nonneg_right hx.le he.le).trans (by rw [add_mul,one_mul,div_mul_cancel₀ _ he.ne']; linarith)
end YM.FullVolume
