import YM.Bid.Loan
import YM.Planned.PRIMARY_INTEGRAL_295.Paint

/-!
# Unloading translated moments into the position-degree filtration

Norm in coordinate-free real homogeneous tensors, with fixed E4 initial
vertices. Pre-side charges: in particular, paying a finite polynomial
test or a canonical input does NOT cost a multiple of all N residues.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Carrier
open Function Filter Set Lattice Laurent RG Precision Bloch Exterior Work.F08 Next.Free Place ContinuousMultilinearMap
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {j n t : ℕ}

lemma shade_slice (A : Tensor.T E4 E n) (s : Slices n) (x v : E4) :
    ‖forSlice A s x v‖ ≤ ‖A‖ * (‖x‖^(home s)*‖v‖^(away s)) := by
  let p i := if s i then v else x
  let a i := if s i then 0 else (1:ℕ); let b i := if s i then 1 else (0:ℕ)
  have h i : ‖p i‖=‖x‖^(a i)*‖v‖^(b i) := by cases hs:s i<;>simp [hs,p,a,b]
  apply (A.le_opNorm p).trans_eq
  simp_rw [h,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]; rfl

variable [FiniteDimensional ℝ E]

/-- Direction costs for real E4 homogeneous tensors, selected BEFORE L. -/
theorem stamp (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (n : ℕ) :
    ∃ B : ℝ, 1≤B ∧ ∀ (v : Tensor.T E4 E n), Tensor.Sym v → ∀ c : ℝ,0≤c →
      (∀ x : E4, ‖Tensor.diagonal v x‖ ≤ c*‖x‖^n) → ‖v‖ ≤ B*c := by
  classical
  let S : Submodule ℝ (Tensor.T E4 E n) := {
    carrier := {A | Tensor.Sym A}
    zero_mem' := fun _ _ => rfl
    add_mem' := fun h k x t => by rw [add_apply, h x t,k x t]; rfl
    smul_mem' := fun c a h x t => by simp only [smul_apply,h x t] }
  let W := Metric.sphere (0:S) 1
  letI : ProperSpace S := FiniteDimensional.proper ℝ S
  let t (i : S) (x : E4) := Tensor.diagonal i.val x
  have he (x : E4) : Continuous fun i:S => ‖t i x‖ := ((ContinuousMultilinearMap.apply ℝ _ E fun _ => x).continuous.comp continuous_subtype_val).norm
  let U (p : E4 × ℝ) := {q : S | ‖q‖ < p.2*‖t q p.1‖}
  have hW : W ⊆ ⋃ i, U i := by
    intro q hq
    have hg : q.val ≠ 0 := by
      intro hv; have hz : q=0 := Subtype.ext hv; simp [W,hz] at hq
    have hf : ∃ x : E4,0<‖t q x‖ := by
      by_contra! ht
      apply hg; exact Tensor.ext_diag q.val 0 q.property (fun _ _=>rfl) (funext fun x => norm_le_zero_iff.mp (ht x)) -- name
    obtain ⟨x,hx⟩ := hf
    apply mem_iUnion.mpr; refine ⟨(x,(‖q‖+1)/‖t q x‖),?_⟩
    change ‖q‖ < _; rw [div_mul_cancel₀ _ hx.ne']; simp
  obtain ⟨l,hL⟩ := (isCompact_sphere (0:S) 1).elim_finite_subcover U (fun p => isOpen_lt continuous_norm (continuous_const.mul (he _))) hW
  let C (p : E4 × ℝ) := |p.2| *‖p.1‖^n
  have hC p : 0≤C p := by unfold C; positivity
  refine ⟨1+∑ i∈l,C i,le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hC i), fun v hv c hc hb => ?_⟩
  have heq i (hi:i∈l) : C i ≤ 1+∑ i∈l,C i := (Finset.single_le_sum (fun i _=>hC i) hi).trans (le_add_of_nonneg_left zero_le_one)
  by_cases hV : v=0
  · rw [hV,norm_zero]; positivity [Finset.sum_nonneg (s:=l) (fun i _=>hC i)]
  have ht := norm_pos_iff.mpr hV
  let s : S := ⟨v,hv⟩; let a := ‖v‖⁻¹
  have hm : a • s∈W := by simp [W,norm_smul,hV,s,a]
  obtain ⟨i,hi,hh⟩ := mem_iUnion₂.mp (hL hm)
  have hp : ‖v‖ ≤ |i.2| *‖t s i.1‖ := by
    change ‖a • s‖ < i.2*‖t (a • s) _‖ at hh
    have he : t (a • s) i.1=a • t s i.1 := rfl
    rw [he] at hh; change ‖a • v‖ < _ at hh; rw [norm_smul,norm_smul,mul_left_comm] at hh
    refine (le_of_lt (lt_of_mul_lt_mul_left hh (norm_nonneg _))).trans (mul_le_mul_of_nonneg_right
      (le_abs_self _) (norm_nonneg _))
  refine hp.trans ((mul_le_mul_of_nonneg_left (hb i.1) (abs_nonneg i.2)).trans (Eq.trans_le ?_
    (mul_le_mul_of_nonneg_right (heq i hi) hc)))
  unfold C; ring

def tokenPrice (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (n : ℕ) := (stamp E n).choose
lemma tokenPrice_ge (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (n : ℕ) :
    1≤tokenPrice E n := (stamp E n).choose_spec.1

section
variable {P : Flight j t} (q : Cover → ℝ) (A : Tensor.T E4 (Axis → E) n) (i : Axis)

private def spoke (q : Cover→ℝ) (A : Tensor.T E4 (Axis→E) n) (i : Axis) (s : Slices n) (x : E4) (z : Cover) := q z • forSlice A s x (seat z) i

private lemma speak (s : Slices n) {σ C : ℝ} (hσ : 0<σ) (h : Width σ C q) :
    ∃ M : Tensor.T E4 E (home s), Tensor.Sym M ∧ (∀ x, HasSum (spoke q A i s x) (Tensor.diagonal M x)) ∧
      ‖M‖ ≤ tokenPrice E (home s)*‖A‖*widthCost σ (away s)*C := by
  classical
  let g (z : Cover) x := spoke q A i s x z
  letI : CompleteSpace E := FiniteDimensional.complete ℝ _
  have hg (z : Cover) : g z ∈ exactDegree E (home s) := Submodule.smul_mem _ _
    (linear_pure (ContinuousLinearMap.proj i) (forSlice_home A s _))
  let c z := ‖q z‖*liftCost (away s) z
  have hc z : 0≤c z := mul_nonneg (norm_nonneg _) (liftCost_pos ..)
  have ht z x : ‖g z x‖ ≤ (‖A‖*c z)*‖x‖^(home s) := by
    have he := ((show ‖forSlice A s x (seat z) i‖ ≤ ‖forSlice A s x (seat z)‖ from norm_le_pi_norm ..).trans (shade_slice A s x (seat z)))
    unfold g spoke; rw [norm_smul]; calc
      _ ≤ ‖q z‖*(‖A‖*(‖x‖^home s * ‖seat z‖^away s)) := mul_le_mul_of_nonneg_left he (norm_nonneg _)
      _ ≤ ‖q z‖*(‖A‖*(‖x‖^home s * (1+(size z:ℝ))^away s)) := by
        gcongr; exact (shade_seat z).trans (le_add_of_nonneg_left zero_le_one)
      _ = _ := by unfold c liftCost; ring
  choose T hT H using fun z : Cover => pure_sym (hg z)
  let f := tokenPrice E (home s)
  have he z : ‖T z‖ ≤ f * ‖A‖ * c z := by
    refine (stamp E (home s)).choose_spec.2 (T z) (hT z) _ (mul_nonneg (norm_nonneg _) (hc _))
      (fun x => ?_)|>.trans_eq (mul_assoc ..).symm
    rw [← H]; exact ht z x
  let B := widthCost σ (away s)*C
  have hr : SumBudget c B := width_income hσ h _
  have hp : Summable fun z => ‖T z‖ := (hr.2.1.mul_left (f*‖A‖)).of_nonneg_of_le (fun i => norm_nonneg _) he
  let M := ∑' z, T z
  have hx (Q) : HasSum (fun z => T z Q) (M Q) := (ContinuousMultilinearMap.apply ℝ _ E Q).hasSum hp.of_norm.hasSum
  refine ⟨M,fun x s => ?_,fun x => ?_,?_⟩
  · rw [← (hx _).tsum_eq,← (hx _).tsum_eq]; exact tsum_congr fun z=> hT z x s
  · have he (z : Cover) : spoke q A i s x z=Tensor.diagonal (T z) x := congr_fun (H z) x
    rw [funext he]; exact hx _
  change ‖∑' z, T z‖≤ _; have hf := (tokenPrice_ge E (home s))
  have he' := (norm_tsum_le_tsum_norm hp).trans (hp.tsum_le_tsum he (hr.2.1.mul_left _))
  rw [tsum_mul_left] at he'; refine he'.trans ((mul_le_mul_of_nonneg_left hr.2.2
    (mul_nonneg (zero_le_one.trans hf) (norm_nonneg _))).trans_eq ?_)
  unfold B; ring
end

/-- Fresh exponent local to these formulas: exactly L^(-b). -/
def unitStep (L : Side) := (L.val:ℝ)⁻¹
lemma unitStep_pos (L : Side) : 0<unitStep L := by unfold unitStep; positivity
lemma unitStep_le (L : Side) : unitStep L≤1 := inv_le_one_of_one_le₀ (show 1≤ (L.val:ℝ) from Nat.one_le_cast.mpr L.property)

private def projected (k : ℝ) (P : Flight j t) (A : Tensor.T E4 (Axis→E) n) (s : Slices n) (x : E4) (i : Axis) :=
    ∑ b : Axis, ∑' z : Cover, (unitStep P.L)^(home s) • spoke (member (linesOf P k) 0 i b) A b s x z

-- Uniform cost before L for one true position-degree component.
private theorem plan (k : ℝ) (hk : 0<k) (hj : 4 ≤ j) (ht : 4 ≤ t) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (n : ℕ) (s : Slices n) :
    ∃ C : ℝ,0<C ∧ ∀ (P : Flight j t) (A : Tensor.T E4 (Axis→E) n),
      projected k P A s ∈ Place.exactDegree (Axis→E) (home s) ∧
        ∀ z : E4, ‖projected k P A s z‖ ≤ C * ‖A‖ * (unitStep P.L)^(home s + 1) * ‖z‖^(home s) := by
  classical
  obtain ⟨σ,C,hσ,hC,h⟩ := priced k hk hj ht
  let c := tokenPrice E (home s)*widthCost σ (away s)*C
  have hc : 0<c := by unfold c; have := tokenPrice_ge E (home s); have := widthCost_ge hσ (away s); positivity
  refine ⟨4*c,by positivity,fun P A => ?_⟩
  let A' := member (linesOf P k) 0
  have hr a b : Width σ (C*unitStep P.L) (A' a b) := by
    have he := h P [] (by simp); simp only [unitStep]; rw [← div_eq_mul_inv]
    simpa only [advanceC,List.length_nil, Nat.add_zero,pow_one, A', member] using he (wrap P.L 0, Exterior.coord a) (Exterior.coord b)
  choose T hT hh he using fun i j => speak (A' i j) A j s hσ (hr i j)
  let D := unitStep P.L; have hd : 0<D := unitStep_pos _
  have hP (x : E4) (i : Axis) : projected k P A s x i=∑ b : Axis,D^(home s) • Tensor.diagonal (T i b) x := by
    unfold projected; refine Finset.sum_congr rfl fun b _=> ?_
    exact ((hh i b x).const_smul _).tsum_eq
  constructor
  · apply Place.vector_pure; intro i
    rw [show (fun x => projected k P A s x i)=∑ b : Axis,D^(home s) • Tensor.diagonal (T i b) from funext fun x => by rw [Finset.sum_apply,hP]; rfl]
    exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Place.simple _)
  intro z; refine (pi_norm_le_iff_of_nonneg ?_).mpr (fun i => ?_)
  · positivity
  rw [hP z]
  have hx (b : Axis) : ‖D^(home s) • Tensor.diagonal (T i b) z‖ ≤ c * ‖A‖ * D^(home s+1)*‖z‖^(home s) := by
    rw [norm_smul, Real.norm_of_nonneg (pow_nonneg hd.le _)]
    have he' := he i b
    have hz : ‖Tensor.diagonal (T i b) z‖ ≤ ‖T i b‖ * ‖z‖^(home s) := by
      simpa [Tensor.diagonal] using (T i b).le_opNorm (fun _ => z)
    refine (mul_le_mul_of_nonneg_left (hz.trans (mul_le_mul_of_nonneg_right he' (by positivity)))
      (by positivity)).trans_eq ?_
    unfold D c; ring
  apply (norm_sum_le ..).trans ((Finset.sum_le_sum (fun b _ => hx b)).trans_eq ?_); simp [Axis,D]; ring

private lemma projected_eval {k : ℝ} (hk : 0<k) {t : ℕ} (P : Flight j t) (ht : 4≤t)
    (A : Tensor.T E4 (Axis→E) n) (hn : n < j) (x : Cover) (i : Axis) :
    applyLine (linesOf P k) (verdict (Tensor.diagonal A)) x i = ∑ s:Slices n, projected k P A s (seat x) i := by
  classical
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  let D := unitStep P.L
  obtain ⟨σ,C,hσ,hC⟩ := stored P k hk ht
  let q j := member (linesOf P k) 0 i j
  have hr j : Width σ C (q j) := hC _ _
  rw [field_pure k hk P ht _ (Place.simple _) hn]; unfold projected; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  unfold respond
  let f (z : Cover) (s : Slices n) := spoke (q b) A b s (seat x) z
  have hz (z : Cover) : q b z • Tensor.diagonal A (D • seat x + seat z) b = ∑ s, D^(home s) • f z s := by
    rw [show Tensor.diagonal A (D • seat x + seat z) = _ from
      (show _=∑ s:Slices n, D^(home s) • forSlice A s (seat x) (seat z) from by
        have hh := slice_diagonal A (D • seat x) (seat z) 1; simp only [one_smul, one_pow] at hh
        rw [hh]; refine Finset.sum_congr rfl fun s _ => ?_
        have he := slice_scale A s (seat x) (seat z) D 1; simpa using he)]
    rw [Finset.sum_apply, Finset.smul_sum]; apply Finset.sum_congr rfl; intro z hz; exact smul_comm ..
  change (∑' z, q b z • Tensor.diagonal A (D • seat x + seat z) b) = _
  simp_rw [hz]
  rw [Summable.tsum_finsetSum]
  · intro s hs; obtain ⟨T,_,he,_⟩ := speak (q b) A b s hσ (hr b)
    exact (he (seat x)).summable.const_smul _

private lemma projected_aim 
    (s : Slices n) (h : home s=n) : s=(fun _=>false) := by
  have hr := covers s
  ext i
  cases he:s i
  · rfl
  have he : 0<away s := by
    apply Finset.sum_pos'; intro a _; positivity
    exact ⟨i,Finset.mem_univ _,by simp [he]⟩
  omega

omit [FiniteDimensional ℝ E] in
private lemma projected_top (k : ℝ) (hk : 0<k) (P : Flight j t) (ht : 4≤t) (A : Tensor.T E4 (Axis→E) n) [CompleteSpace E] :
    projected k P A (fun _=>false)=(unitStep P.L)^(n+1) • Tensor.diagonal A := by
  funext x i
  let s (_ : Fin n) := false
  let q b := member (linesOf P k) 0 i b
  obtain ⟨σ,C,hσ,hC⟩ := stored P k hk ht
  have he b : Summable (q b) := (show Width σ C (q b) from hC _ _).summable hσ.le
  let u := unitStep P.L; let v := Tensor.diagonal A x
  change (∑ b : Axis, ∑' z : Cover,u^(home s) • (q b z • forSlice A s x (seat z) b))=u^(n+1) • v i
  have hr : home s=n := by simp [home,s]
  have hz b : (∑' z : Cover, u^(home s) • (q b z • forSlice A s x (seat z) b))=u^n • ((if i=b then u else 0) • v b) := by
    simp_rw [hr, show ∀ z : Cover, forSlice A s x (seat z)=v from fun _=>rfl, ((he b).smul_const (v b)).tsum_const_smul _, (he b).tsum_smul_const,show ∑' z,q b z = _ from origin_money k hk P ht 0 i b]; rfl
  simp_rw [hz]; rw [Finset.sum_eq_single i]; simp [pow_succ',smul_smul,mul_comm]
  · intro b _ hb; rw [if_neg hb.symm,zero_smul,smul_zero]
  · simp

abbrev Prism (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) :=
    (i : Fin n) → Tensor.T E4 (Axis→E) i.val

def charted {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ} (q : Prism F n) : E4 → Axis → F :=
    ∑ i, Tensor.diagonal (q i) -- add {F}

/-- Budget the whole outgoing homogeneous expansion (all vector colors).
Pre-L constants in the ordinary real symmetric-tensor normalization. The
exact top weight at every support size, not perturbative closeness. -/
theorem pure_alloc (k : ℝ) (hk : 0<k) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (n : ℕ) (hj : 4≤j) (ht : 4≤t) (hs : n<j) :
    ∃ C:ℝ,1≤C ∧ ∀ (P : Flight j t) (A : Tensor.T E4 (Axis→E) n), ∃ g : Prism E (n+1),
    (∀ i, Tensor.Sym (g i)) ∧ (∀ i, ‖g i‖ ≤ C*‖A‖*unitStep P.L^(i.val+1)) ∧
      Tensor.diagonal (g (Fin.last n)) = unitStep P.L ^ (n+1) • Tensor.diagonal A ∧
      applyLine (linesOf P k) (verdict (Tensor.diagonal A))=verdict (charted g) := by
  classical
  choose C hC h using plan k hk hj ht E n
  let r := 1+∑ s:Slices n,C s
  let F := Axis→E
  choose B hB HH using fun i:Fin (n+1)=> stamp (Axis→E) i.val
  let G := (1+∑ i,B i)
  have hr : 1≤r := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => (hC i).le)
  have hg0 (i:Fin (n+1)) : 0≤B i := zero_le_one.trans (hB i)
  have hG : 1≤G := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hg0 i)
  refine ⟨G*r,one_le_mul_of_one_le_of_one_le hG hr, fun P A => ?_⟩
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  let K := unitStep P.L; have hK : 0<K := unitStep_pos _
  let T (s:Slices n) : Fin (n+1) := ⟨home s,by have := covers s;omega⟩
  let f (i:Fin (n+1)) := ∑ s : Slices n with T s=i, projected k P A s
  have hf (i : Fin (n+1)) : f i ∈ exactDegree (Axis→E) i.val :=
    Submodule.sum_mem _ fun _ he => (Finset.mem_filter.mp he).2 ▸ (h _ P A).1
  choose g H hh using fun i => pure_sym (hf i)
  refine ⟨g,H,fun i => ?_,⟨?_,?_⟩⟩
  · let b := ‖A‖*K^(i.val+1)
    have hb : 0≤b := mul_nonneg (norm_nonneg _) (by positivity)
    have hu (x : E4) : ‖Tensor.diagonal (g i) x‖ ≤ (r*b)*‖x‖^i.val := by
      rw [← hh, show f i x=_ from Finset.sum_apply x _ _, Finset.sum_filter]
      apply (norm_sum_le ..).trans
      let u := b*‖x‖^i.val; have h0 : 0≤u := by unfold u; positivity
      calc
        _ ≤ ∑ s:Slices n,C s * u := Finset.sum_le_sum fun s hq => by
          split <;> rename_i he
          · have ht := (h s P A).2 x; have he' : home s=i.val := congr_arg Fin.val he
            rw [he'] at ht; unfold u b K; exact ht.trans_eq (by ring)
          rw [norm_zero]; positivity [hC s]
        _ ≤ r*u := by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) h0
        _ = _ := (mul_assoc ..).symm
    refine (HH i (g i) (H i) (r*b) (by positivity) hu).trans ?_
    have ht : B i ≤ G := (Finset.single_le_sum (fun i _ => hg0 i) (Finset.mem_univ i)).trans (le_add_of_nonneg_left zero_le_one)
    exact (mul_le_mul_of_nonneg_right ht (by positivity)).trans_eq (by unfold b; ring)
  · let s (_:Fin n) := false
    rw [← hh]; unfold f; rw [Finset.sum_eq_single s,projected_top k hk P ht]
    · intro b hb hs; have he : T b=Fin.last n := (Finset.mem_filter.mp hb).2; exact (hs (projected_aim b (congr_arg Fin.val he))).elim
    intro hc; exfalso; apply hc; apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,Fin.ext (by simp [T,s,home])⟩
  ext1 x; ext1 i; rw [projected_eval hk P ht A hs x i]; unfold charted verdict
  simp_rw [← hh,f,Finset.sum_apply, Finset.sum_filter]
  rw [Finset.sum_comm]; simp only [Finset.sum_ite_eq, Finset.mem_univ,if_true] -- check orient
end YM.Planned.PrimaryIntegral295.Carrier
