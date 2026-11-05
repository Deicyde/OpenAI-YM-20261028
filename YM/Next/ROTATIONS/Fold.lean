import YM.Next.ROTATIONS.Energy
/-! # Univariate jet contact preparation for product profiles

Argument `Form` in **position** here. -/
noncomputable section
namespace YM.Outer
open Function Filter Set MeasureTheory Measure Complex Boundary Probe
open scoped Topology BigOperators ContDiff

def flat (D : ℕ) (f : Form) := ∀ j : ℕ, j<D → iteratedDeriv j f 0=0
abbrev prime := SchwartzMap.derivCLM ℂ ℂ
lemma prime_zero_order (D) (f : Form) (h : flat (D+1) f) : flat D (prime f) := by
  intro i hi; rw [show ⇑(prime f)=deriv f from funext (SchwartzMap.derivCLM_apply ℂ f), ← iteratedDeriv_succ']; exact h _ (by omega)

/-- Bump at zero with all factorials literal. -/
def gen (k : ℕ) := (k.factorial:ℂ)⁻¹ • stamp (pump k center)
lemma home_at (k : ℕ) : gen k 0 = if k=0 then 1 else 0 := by cases k <;> simp [gen,stamp_at,pump_at,center_plane]
lemma gen_jet (k j) : iteratedDeriv j (gen k) 0 = if j=k then 1 else 0 := by
  have he : ⇑(gen k) =ᶠ[𝓝 0] fun x : ℝ => (k.factorial:ℂ)⁻¹ * ((x^k:ℝ):ℂ) := by
    filter_upwards [Ioo_mem_nhds (a:=(-1:ℝ)) (b:=1) (by norm_num) (by norm_num)] with x hx
    rw [gen,_root_.smul_apply,stamp_at,pump_at,center_plane x (abs_le.mpr ⟨hx.1.le,hx.2.le⟩),mul_one]; rfl
  rw [(he.iteratedDeriv j).self_of_nhds]
  rw [iteratedDeriv_const_mul_field]
  have hx (j : ℕ) : iteratedDeriv j (fun x : ℝ => ((x^k:ℝ):ℂ)) 0 =
      ((iteratedDeriv j (fun x : ℝ => x^k) 0:ℝ):ℂ) := by
    -- composition CLM
    rw [iteratedDeriv_eq_iteratedFDeriv,iteratedDeriv_eq_iteratedFDeriv,
      show (fun x : ℝ => ((x^k:ℝ):ℂ))=ofRealCLM ∘ (fun x : ℝ => x^k) from rfl]
    rw [ofRealCLM.iteratedFDeriv_comp_left (f:=fun x : ℝ => x^k) (n:=↑j) (by fun_prop) le_rfl]
    rfl
  rw [hx,iteratedDeriv_fun_pow_zero]; split_ifs <;> simp [Nat.factorial_ne_zero]

def collect (D : ℕ) (f : Form) := ∑ j∈Finset.range D,(iteratedDeriv j f 0) • gen j
lemma collect_all (f : Form) {D k} (hk : k<D) : iteratedDeriv k (collect D f) 0=iteratedDeriv k f 0 := by
  unfold collect
  rw [show ⇑(∑ j∈Finset.range D,(_ • gen j:Form)) =
    fun x => ∑ j∈Finset.range D,(iteratedDeriv j f 0) • gen j x from funext fun x => by simp,
    iteratedDeriv_fun_sum (fun j hj => ?_)]
  · simp_rw [iteratedDeriv_fun_const_smul_field,gen_jet]
    simp [hk]
  exact ((iteratedDeriv j f 0 • gen j).smooth k).contDiffAt
lemma collect_add (D f g) : collect D (f+g)=collect D f+collect D g := by
  have he j : iteratedDeriv j (f+g : Form) 0 = iteratedDeriv j f 0+iteratedDeriv j g 0 :=
    iteratedDeriv_fun_add (f.smooth j).contDiffAt (g.smooth j).contDiffAt
  unfold collect; simp_rw [he,add_smul,Finset.sum_add_distrib]
lemma collect_scale (D) (c : ℂ) (f : Form) : collect D (c • f : Form)=c • collect D f := by
  have he j : iteratedDeriv j (c•f : Form) 0 = (c:ℂ) • iteratedDeriv j f 0 := iteratedDeriv_fun_const_smul_field c ⇑f
  unfold collect; simp_rw [he,Finset.smul_sum]; refine Finset.sum_congr rfl fun i hi => ?_
  rw [smul_smul,smul_eq_mul]
lemma missed (D f) : flat D (f-collect D f) := by
  intro i hi
  rw [show ⇑(f-collect D f)=(fun x => f x-collect D f x) from rfl,
    iteratedDeriv_fun_sub (f.smooth i).contDiffAt ((collect D f).smooth i).contDiffAt,collect_all f hi,sub_self]
lemma all_miss (f : Form) (k : ℕ) (h : flat k f) : collect k f=0 := by unfold collect; apply Finset.sum_eq_zero; intro i hi; rw [h i (Finset.mem_range.mp hi),zero_smul]

abbrev glare : Form →L[ℂ] Form := along (LinearIsometryEquiv.neg ℝ).toContinuousLinearEquiv
lemma glare_at (f : Form) (x) : glare f x=f (-x) := rfl
lemma neg_order (f : Form) (j) : iteratedDeriv j (glare f) 0=(-1:ℂ)^j*iteratedDeriv j f 0 := by
  rw [show ⇑(glare f)=(fun x => f (-x)) from rfl,iteratedDeriv_comp_neg]; simp [Complex.real_smul]
lemma gen_flip (k) : glare (gen k)=(-1:ℂ)^k • gen k := by
  ext x
  simp only [glare_at,_root_.smul_apply,gen,stamp_at,pump_at,smul_eq_mul,center_even x]
  rw [neg_eq_neg_one_mul x,mul_pow]; push_cast; ring
lemma collect_glare (D f) : glare (collect D f)=collect D (glare f) := by
  unfold collect
  simp_rw [_root_.map_sum,map_smul,gen_flip,neg_order]; apply Finset.sum_congr rfl; intro i hi
  rw [smul_smul,mul_comm]
end YM.Outer
