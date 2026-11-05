import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Taylor
import YM.PCalc.Band
import YM.Source.Drops
import YM.Work.G05.Taylor



/-!
# Projection analysis, Part 1

Arithmetic of the engineering / factor degree coordinates before calibration.
First some elementary real-jet helpers. We compute the reads of radial polynomial
labels at both scalings. No cutoff or renormalization estimates used.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WardBin
open Function Set Filter Work.G05 Labels Lattice RG Wilson Source Source.Drops
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff

variable {n k : ℕ}
section
variable {E F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → F}

def leading (n : ℕ) (f : ℝ → F) := (n.factorial:ℝ)⁻¹ • iteratedDeriv n f 0

lemma leading_zero_iff : leading n f=0 ↔ iteratedDeriv n f 0=0 := by simp [leading, Nat.factorial_ne_zero]

lemma leading_tensor (x : E) (g : E → F) (hg : ContDiffAt ℝ n g 0) :
    leading n (fun t : ℝ => g (t • x)) = Tensor.diagonal (Tensor.coeff g n 0) x := by
  let L : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight x
  change (n.factorial:ℝ)⁻¹ • iteratedFDeriv ℝ n (g ∘ L) 0 (fun _ => 1) = _
  have ht : iteratedFDeriv ℝ n (blockTaylor n g ∘ L) 0 = iteratedFDeriv ℝ n (g ∘ L) 0 :=
    jets_comp (L.contDiff.contDiffAt) (L.contDiff.contDiffAt) (blockTaylor_contDiff n g _|>.contDiffAt)
      (by rw [map_zero]; exact hg) rfl (fun _ _ => rfl) (map_zero L ▸ blockTaylor_jets hg) _ le_rfl
  rw [← ht,L.iteratedFDeriv_comp_right (blockTaylor_contDiff n g n) _ le_rfl, map_zero, blockTaylor_jets hg _ le_rfl]
  suffices H : (fun a : Fin n => L 1) = fun _ => x by
    change _ • iteratedFDeriv ℝ n g 0 (fun _ => L 1) = _; rw [H]; rfl
  simp [L]

/-- If `t⁻ⁿ f` has a limit through this half-line, lower powers vanish. -/
lemma falls (h : k < n) {Y : F} (hs : Tendsto (fun t : ℝ => (t^n)⁻¹ • f t) (𝓝[>] (0:ℝ)) (𝓝 Y)) :
    Tendsto (fun t : ℝ => (t^k)⁻¹ • f t) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have he := ((show Tendsto (fun t : ℝ => t) (𝓝[>] (0:ℝ)) (𝓝 0) from
    tendsto_id.mono_left nhdsWithin_le_nhds).pow (n-k)).smul hs
  rw [zero_pow (Nat.sub_ne_zero_of_lt h), zero_smul] at he
  apply he.congr'
  filter_upwards [self_mem_nhdsWithin (s:=Ioi (0:ℝ))] with t ht
  rw [smul_smul]; apply congr_arg (fun c : ℝ => c • f t)
  have hp := (pow_pos (show 0<t from ht) (n-k)).ne'
  rw [show t^n = t^(n-k)*t^k by rw [← pow_add, Nat.sub_add_cancel h.le]]
  have hu : 0 < t := ht
  field_simp

/-- Use with actual finite differentiability, even at 0. -/
lemma leading_of_lim (hf : ContDiffAt ℝ n f 0) (X : F)
    (he : Tendsto (fun t : ℝ => (t^n)⁻¹ • f t) (𝓝[>] (0:ℝ)) (𝓝 X)) : leading n f=X := by
  induction n using Nat.strong_induction_on generalizing X with
  | h n ih =>
    have hh (k : ℕ) (hk : k<n) : leading k f=0 := ih k hk (hf.of_le (by exact_mod_cast hk.le)) 0 (falls hk he)
    obtain ⟨r,hr,h⟩ := Metric.mem_nhds_iff.mp (hf.eventually (by simp))
    have hv (x : ℝ) (hx : x ∈ Metric.ball 0 r) : ContDiffAt ℝ n f x := h hx
    let s := Metric.ball (0:ℝ) r
    have hk : 0 ∈ s := Metric.mem_ball_self hr
    have hs : s ∈ 𝓝 (0:ℝ) := Metric.ball_mem_nhds _ hr
    have hx := taylor_tendsto (show Convex ℝ s from convex_ball (0:ℝ) r) hk (show ContDiffOn ℝ n f s from fun x h => (hv x h).contDiffWithinAt)
    have H (t : ℝ) : taylorWithinEval f n s 0 t = t^n • leading n f := by
      rw [taylor_within_apply, Finset.sum_range_succ, Finset.sum_eq_zero (s:=Finset.range n)]
      · rw [zero_add, iteratedDerivWithin_of_isOpen (show IsOpen s from Metric.isOpen_ball) hk]
        simp [leading, mul_smul, smul_comm (t^n)]
      intro i hi
      rw [iteratedDerivWithin_of_isOpen (show IsOpen s from Metric.isOpen_ball) hk,
        leading_zero_iff.mp (hh i (Finset.mem_range.mp hi)),smul_zero]
    rw [nhdsWithin_eq_nhds.mpr hs] at hx
    have hh : Tendsto (fun t : ℝ => (t^n)⁻¹ • (f t - t^n • leading n f)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      simp_rw [sub_zero,H] at hx; exact hx.mono_left nhdsWithin_le_nhds
    refine tendsto_nhds_unique_of_eventuallyEq (show Tendsto (fun t : ℝ => (t^n)⁻¹ •
      (f t - t^n • leading n f) + leading n f) (𝓝[>] (0:ℝ)) (𝓝 (leading n f)) by
        simpa only [zero_add] using hh.add_const (leading n f)) he ?_
    filter_upwards [self_mem_nhdsWithin (s:=Ioi (0:ℝ))] with t ht
    have Ht : 0<t := ht
    simp only [smul_sub,inv_smul_smul₀ (pow_ne_zero n Ht.ne'), sub_add_cancel]

lemma lead_monomial (n k : ℕ) (V : F) : leading n (fun t : ℝ => t^k • V) = if n=k then V else 0 := by
  unfold leading
  have he : ContDiffAt ℝ (n:WithTop ℕ∞) (fun t : ℝ => t^k) (0:ℝ) := contDiffAt_id.pow _
  rw [iteratedDeriv_smul_const he, iteratedDeriv_fun_pow_zero]
  split_ifs with h
  · subst n; rw [inv_smul_smul₀ (by positivity : (k.factorial : ℝ)≠0)]
  simp

lemma lead_sum {ι : Type*} (I : Finset ι) (f : ι → ℝ → F) (hf : ∀ i∈I,ContDiffAt ℝ n (f i) 0) :
    leading n (fun t => ∑ i ∈ I, f i t) = ∑ i ∈ I, leading n (f i) := by
  rw [leading, iteratedDeriv_fun_sum hf, Finset.smul_sum]; rfl

end

/-! Scaling operations on `Snap` and on raw jets. -/
variable {G : Gauge} {d j : ℕ}

/-- Scale by engineering degree. -/
def engineered (t : ℝ) : Snap G d →L[ℝ] Snap G d :=
  LinearMap.toContinuousLinearMap {
    toFun v i := t^(i.val+2) • v i
    map_add' _ _ := funext (fun _ => smul_add ..)
    map_smul' a _ := funext (fun _ => smul_comm _ a _) }

lemma engineered_at (v : Snap G d) (t : ℝ) (i : Fin (d-1)) :
    engineered t v i = (t^(i.val+2)) • v i := rfl

lemma expand_jet (v : Snap G d) (t : ℝ) : scaleJet (expand d v) t = expand d (engineered t v) := by
  funext i; by_cases h:i<d-1 <;> simp [h,expand,scaleJet,engineered_at]
lemma expand_smul (v : Snap G d) (t : ℝ) : expand d (t • v) = t • expand d v := by
  funext i; by_cases h : i < d-1 <;> simp [expand,h]

lemma monoSmooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : E) (p : ℕ) (N : WithTop ℕ∞) :
    ContDiff ℝ N fun t : ℝ => t^p • V := by fun_prop

lemma eng_cont (v : Snap G d) (N : WithTop ℕ∞) : ContDiff ℝ N fun t : ℝ => engineered t v := by
  apply contDiff_pi.mpr; intro i
  change ContDiff ℝ N fun t : ℝ => t^(i.val+2) • v i
  exact monoSmooth (v i) _ _

lemma scaled_mono (t : ℝ) (A : Jet G) (p : Key G →₀ ℕ) (c : ℂ) :
    Labels.read (scaleJet A t) (MvPolynomial.monomial p c) = t^(height p) •
      Labels.read A (MvPolynomial.monomial p c) := by
  have he (i : Key G) : coord (scaleJet A t) i = ((↑t:ℂ)^(generation i))*coord A i := by simp [coord, scaleJet,generation]
  have hh : height p = ∑ k∈ p.support, generation k * p k := by
    unfold height; rw [Finsupp.weight_apply]; unfold Finsupp.sum
    simp [mul_comm]
  rw [Labels.read,Labels.read]
  simp only [Complex.real_smul, Complex.ofReal_pow, MvPolynomial.aeval_monomial, he]
  unfold Finsupp.prod
  simp_rw [mul_pow,← pow_mul,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum, hh]; ring

lemma scaled_grade (t : ℝ) (A : Jet G) (p : Label G d)
    (h : p ∈ Grade (n,k)) : Labels.read (scaleJet A t) p.val = t^n • Labels.read A p.val := by
  rw [p.val.as_sum, map_sum,map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl; intro i hi; rw [scaled_mono]
  have hh := (pure_grade _ p).mp h (MvPolynomial.mem_support_iff.mp hi)
  rw [weight_slot] at hh; rw [show height i=n from congr_arg Prod.fst hh]

lemma multiplied_mono (t : ℝ) (A : Jet G) (p : Key G→₀ℕ) (c : ℂ) :
    Labels.read (t • A) (MvPolynomial.monomial p c) = t^(Finsupp.weight bidegree p).2 •
      Labels.read A (MvPolynomial.monomial p c) := by
  have he (i : Key G) : coord (t • A) i = (t:ℂ)*coord A i := by simp [coord]
  simp only [Labels.read, Complex.real_smul, MvPolynomial.aeval_monomial, he, Complex.ofReal_pow,weight_slot]
  unfold Finsupp.prod Finsupp.sum
  simp_rw [mul_pow, Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]; ring

lemma multiplied_grade (t : ℝ) (A : Jet G) (p : Label G d)
    (h : p ∈ Grade (n,k)) : Labels.read (t • A) p.val = t^k • Labels.read A p.val := by
  rw [p.val.as_sum, map_sum,map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl; intro i hi
  rw [multiplied_mono,(pure_grade _ p).mp h (MvPolynomial.mem_support_iff.mp hi)]

abbrev Board (G : Gauge) (d : ℕ) := (i : Fin (d-1)) × Fin (Labels.dim G i.val)

def key (i : Board G d) : Key G := ⟨i.1.val,i.2⟩

def chip (i : Board G d) : Snap G d := Pi.single i.1 ((axes G i.1.val) i.2)

def atChip (A : Snap G d) (i : Board G d) : ℝ := (axes G i.1.val).repr (A i.1) i.2

lemma read_chip (A : Jet G) (i : Board G d) : (↑(atChip (trunk d A) i):ℂ) = coord A (key i) := rfl

lemma chip_scale (A : Snap G d) (t : ℝ) (i : Board G d) :
    atChip (engineered t A) i = t^(generation (key i)) * atChip A i := by
  simp only [atChip,engineered_at, map_smul, Finsupp.smul_apply,smul_eq_mul]; rfl

lemma chips (A : Snap G d) : (∑ i, atChip A i • chip i) = A := by
  classical
  rw [Fintype.sum_sigma]; funext i
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · simp only [Finset.sum_apply, chip, Pi.smul_apply, Pi.single_eq_same]
    exact (axes G i.val).sum_repr (A i)
  · intro j _ hj
    simp only [Finset.sum_apply, chip, Pi.smul_apply, Pi.single_eq_of_ne hj.symm, smul_zero, Finset.sum_const_zero]
  simp

def depth (x : Fin k → Board G d) := ∑ i, generation (key (x i))

/-- Polynomial contributing to a single bidegree from an ordinary Taylor
coefficient. -/
def tile (M : Tensor.T (Snap G d) ℂ k) (n : ℕ) : Pol G :=
    ∑ x : Fin k → Board G d with depth x=n, MvPolynomial.C (M (chip ∘ x)) * ∏ a, MvPolynomial.X (key (x a))

lemma tile_grade (M : Tensor.T (Snap G d) ℂ k) (n : ℕ) : pureDegree (tile M n) n k := by
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro i hi; apply MvPolynomial.IsWeightedHomogeneous.C_mul
  have he (x : Board G d) := MvPolynomial.isWeightedHomogeneous_X ℂ bidegree (key x)
  have ht : (n,k) = ∑ a, bidegree (key (i a)) := Prod.ext (by rw [Prod.fst_sum]; exact (Finset.mem_filter.mp hi).2.symm)
    (by simp [Prod.snd_sum, bidegree])
  rw [ht]; exact MvPolynomial.IsWeightedHomogeneous.prod _ _ _ fun i _ => he _

lemma chip_expansion (M : Tensor.T (Snap G d) ℂ k) (A : Snap G d) :
    M (fun _ => A) = ∑ x : Fin k → Board G d, (∏ i, atChip A (x i)) • M (chip ∘ x) := by
  calc M (fun _ => A) = M fun _ => ∑ i, atChip A i • chip i := congr_arg M (by simp only [chips])
       _ = ∑ x : Fin k → Board G d, M fun i => atChip A (x i) • chip (x i) := M.map_sum (fun _ v => atChip A v • chip v)
       _ = _ := Finset.sum_congr rfl fun x _ => M.map_smul_univ _ (chip ∘ x)

lemma tile_reads (M : Tensor.T (Snap G d) ℂ k) (n : ℕ) (J : Jet G) :
    leading n (fun t => Tensor.diagonal M (engineered t (trunk d J))) = Labels.read J (tile M n) := by
  let p (x : Fin k → Board G d) := (∏ i, atChip (trunk d J) (x i)) • M (chip ∘ x)
  have he (t : ℝ) : Tensor.diagonal M (engineered t (trunk d J)) =
      ∑ x : Fin k → Board G d,t^(depth x) • p x := by
    rw [Tensor.diagonal,chip_expansion]; apply Finset.sum_congr rfl
    intro i hi; unfold p depth
    simp_rw [chip_scale,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]; rw [smul_smul]
  rw [funext he]
  rw [lead_sum (n:=n) _ (fun i (t : ℝ) => t^(depth i) • p i) (by intros; fun_prop)]
  simp_rw [lead_monomial]
  unfold tile; rw [map_sum,Finset.sum_filter]; apply Finset.sum_congr rfl
  intro i _; by_cases hn : n=depth i
  · rw [if_pos hn,if_pos hn.symm,map_mul,map_prod]
    simp_rw [Labels.read, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
    unfold p
    rw [Complex.real_smul,Complex.ofReal_prod]; simp_rw [read_chip]; exact mul_comm ..
  rw [if_neg hn,if_neg (Ne.symm hn)]
end YM.WardBin
