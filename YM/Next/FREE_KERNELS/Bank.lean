import Mathlib.Analysis.Normed.Group.Tannery
import YM.CellFourier.Circulant
import YM.Next.FREE_KERNELS.Glue



/-!
# Cover coefficients are unique

Summable *counting* kernels. Sampling ALL side lengths detects an entry;
no assertion from just one period. Mon includes the upper endpoint harmonic
aliased direction convention (even side tie).
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric
open scoped Topology BigOperators

lemma mon_re (n : Side) (p : Site n) (i : Axis) : (mon p i).re=2*Real.pi*(lift p i)/(n.val:ℝ) := by
  have he := congr_arg (fun q : Momentum => (q i).re) (mon_phase p)
  dsimp at he
  rw [← Nat.cast_smul_eq_nsmul ℂ] at he
  simp only [reciprocal,smul_eq_mul, Complex.mul_re, Complex.mul_im,
    Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im,
    Complex.natCast_im, Complex.natCast_re, Complex.intCast_re, Complex.intCast_im] at he
  have hn := side_pos n
  rw [eq_div_iff hn.ne']; linarith

lemma mon_mem (n : Side) (p : Site n) : mon p ∈ baseCube := by
  refine ⟨real_frequency p,fun i => ?_⟩
  obtain ⟨h1,h2⟩ := lift_centers p i
  have h3 : -(n.val:ℝ) ≤ 2*(lift p i:ℝ) := by exact_mod_cast h1.le
  have h4 : 2*(lift p i:ℝ) ≤ n.val := by exact_mod_cast h2
  rw [mon_re n p i,abs_le]
  have hπ := Real.pi_pos
  exact ⟨(le_div_iff₀ (side_pos n)).mpr (by nlinarith), (div_le_iff₀ (side_pos n)).mpr (by nlinarith)⟩

lemma eventually_unfold {ι : Type*} {f : Filter ι} (n : ι → Side)
    (hn : Tendsto (fun i => (n i).val) f atTop) (x : Cover) :
    ∀ᶠ i in f, lift (wrap (n i) x)=x := by
  filter_upwards [hn.eventually (eventually_ge_atTop (2*size x+1))] with i hi
  refine lift_eq_iff.mpr ⟨rfl,fun j => ?_⟩
  have hx : (x j).natAbs ≤ size x := Finset.single_le_sum (f:=fun i : Axis => (x i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  change 2 * size x + 1 ≤ (n i).val at hi
  omega

lemma entry_limit {ι : Type*} {f : Filter ι} (n : ι → Side)
    (hn : Tendsto (fun i => (n i).val) f atTop) {α β : Type*} (R : Row α β) (h : R.safe)
    (a : α) (b : β) (x : Cover) : Tendsto (fun i => R.acts (n i) (0,a) (wrap (n i) x,b))
      f (𝓝 (R a b x)) := by
  classical
  let F (i : ι) (y : Cover) := if wrap (n i) x=0 + wrap (n i) y then R a b y else 0
  let G (y : Cover) := if y=x then R a b y else 0
  have he (y) : Tendsto (fun i => F i y) f (𝓝 (G y)) := by
    apply Filter.EventuallyEq.tendsto
    filter_upwards [eventually_unfold n hn x, eventually_unfold n hn y] with i hx hy
    by_cases h : x=y
    · simp [h,F,G]
    have ht : wrap (n i) x ≠ wrap (n i) y := fun e => h (hx ▸ hy ▸ congr_arg lift e)
    simp [F,G, ht, Ne.symm h]
  have hb (i y) : ‖F i y‖ ≤ ‖R a b y‖ := by unfold F; split <;> simp
  have hm := tendsto_tsum_of_dominated_convergence (h a b) he (Eventually.of_forall hb)
  have hG : ∑' y, G y=R a b x := by simp [G]
  rw [hG] at hm
  exact hm

variable {α β : Type*} {A B : Row α β}

lemma bank_injective (ha : A.safe) (hb : B.safe) (h : ∀ n, A.acts n=B.acts n) : A=B := by
  let n (i : ℕ) : Side := ⟨i+1, Nat.zero_lt_succ _⟩
  have hn : Tendsto (fun i => (n i).val) atTop atTop := tendsto_atTop_mono (fun i => show i ≤ i+1 by omega) tendsto_id
  funext a b x
  have hm := entry_limit n hn A ha a b x
  simp_rw [h] at hm
  exact tendsto_nhds_unique hm (entry_limit n hn B hb a b x)

lemma acts_of_cube [Fintype α] [Fintype β] (ha : A.safe) (hb : B.safe)
    (h : ∀ p ∈ baseCube, A.read p=B.read p) (n : Side) : A.acts n=B.acts n := by
  classical
  apply prom_inj
  apply cancel_rotation
  rw [circulant n A ha,circulant n B hb]
  congr! 3 with p
  exact h _ (mon_mem n _)

lemma RRead_injective {a b : Cover → ℝ} (ha : Summable fun i => ‖a i‖) (hb : Summable fun i => ‖b i‖)
    (h : ∀ p ∈ baseCube,RRead a p=RRead b p) : a=b := by
  let A : Row Unit Unit := fun _ _ => a
  let B : Row Unit Unit := fun _ _ => b
  have he : ∀ p ∈ baseCube,A.read p=B.read p := by intro p hp; ext; apply h p hp
  have hA : A.safe := fun _ _ => ha
  have hB : B.safe := fun _ _ => hb
  have hh := bank_injective hA hB (acts_of_cube hA hB he)
  exact congr_arg (fun v : Row Unit Unit => v () ()) hh
end YM.Next.Free
