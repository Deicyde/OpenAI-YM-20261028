import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Sequences
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-!
# Coarse anchoring with a fine-end boundary

Abstract UV Banach argument (single scalar coupling).

The inputs checked separately on any actual
application must be *strong*-norm and coupling estimates for common prescriptions.

The contraction
argument deals with simultaneous two-end conditions, not arbitrary pointwise small terms.
-/
noncomputable section
open Function Set Filter Topology
open scoped BigOperators
set_option autoImplicit false
namespace YM.Extension.UV.Tail
universe u
variable (E : ℕ → Type u) [∀ i, NormedAddCommGroup (E i)]

structure Rules where
  b : ℕ → ℝ
  radius : ℕ → ℝ
  eps : ℕ → ℝ
  band : ℕ → Set ℝ
  coarse : ℝ
  term : ℕ → (i : ℕ) → ℝ → E (i+1) → E i
  alpha : ℕ → ℕ → ℝ
  wobble : ℕ → (i : ℕ) → ℝ → E (i+1) → ℝ
  termLim : (i : ℕ) → ℝ → E (i+1) → E i
  alphaLim : ℕ → ℝ
  wobbleLim : (i : ℕ) → ℝ → E (i+1) → ℝ

variable {E} {R : Rules E}
variable {u : ℕ → ℝ} {v : ∀ i, E i}

structure Lipschitz (R : Rules E) : Prop where
  b_pos i : 0 < R.b i
  b_near i : R.b (i+1) ≤ 2*R.b i
  b_mono : Monotone R.b
  rad_pos i : 0 < R.radius i
  rad_mono : Monotone R.radius
  eps_pos i : 0 ≤ R.eps i
  small n : ∑ i∈Finset.range n, R.eps (i+1) / R.radius (i+1) ≤ 1/10
  bands i : IsCompact (R.band i)
  size i : ∀ x∈R.band i, |x| ≤ 2 *R.b i
  estimates N i (hi:i<N) (z z' : ℝ) (u u' : E (i+1)) :
    z ∈ R.band (i+1) → z'∈R.band (i+1) → ‖u‖ ≤ 1/4 → ‖u'‖ ≤ 1/4 →
     ‖R.term N i z u - R.term N i z' u'‖ ≤ (1/3)*‖u-u'‖ + (1/4)*(|z-z'|/R.radius (i+1)) ∧
      |R.wobble N i z u - R.wobble N i z' u'| ≤ R.eps (i+1) * ((4/3)*‖u-u'‖ + |z-z'|/R.radius (i+1))
  image N i (hi:i<N) z (hz: z ∈ R.band (i+1)) (x:E (i+1)) (hx : ‖x‖ ≤ 1/4) : ‖R.term N i z x‖ ≤ 1/4

structure Limits (R : Rules E) : Prop where
  scalar i : Tendsto (fun N => R.alpha N i) atTop (𝓝 (R.alphaLim i))
  slots i z : z∈R.band (i+1) → ∀ x:E (i+1), ‖x‖ ≤ 1/4 →
    Tendsto (fun N => R.term N i z x) atTop (𝓝 (R.termLim i z x)) ∧
    Tendsto (fun N => R.wobble N i z x) atTop (𝓝 (R.wobbleLim i z x))

structure FiniteCourse (R : Rules E) (z : ℕ → ℕ → ℝ) (v : ℕ→ ∀ i, E i) : Prop where
  beta N i : i ≤ N → z N i ∈ R.band i
  cap N i : i ≤ N → ‖v N i‖ ≤ 1/4
  coarse N : z N 0 = R.coarse
  goes N i : i < N → v N i = R.term N i (z N (i+1)) (v N (i+1)) ∧
      z N i = z N (i+1) + R.alpha N i + R.wobble N i (z N (i+1)) (v N (i+1))

structure InfiniteCourse (R : Rules E) (z : ℕ→ℝ) (v : ∀ i, E i) : Prop where
  beta i : z i ∈ R.band i
  cap i : ‖v i‖ ≤ 1/4
  coarse : z 0=R.coarse
  goes i : v i = R.termLim i (z (i+1)) (v (i+1)) ∧
      z i = z (i+1) + R.alphaLim i + R.wobbleLim i (z (i+1)) (v (i+1))

variable {s d : ℕ→ℝ}
private theorem improve (h:Lipschitz R) (hs : ∀ i, s i ≤ 1)
    (step : ∀ i, s i ≤ (1/3)*s (i+1) + (1/4)*(d (i+1)/R.radius (i+1))) (K : ℝ)
    (hk : 0≤ K) (hd : ∀ i, d i ≤ K* R.b i) (hw : ℕ) (m : ℕ) :
     s m ≤ (1/3)^hw+(3/2)*(K*R.b m/R.radius m) := by
  induction hw generalizing m with
  | zero => calc _ ≤ _ := hs m
                 _ ≤ _ := by have hR := h.rad_pos m; have hb:=h.b_pos m; rw [pow_zero]; apply le_add_of_nonneg_right; positivity
  | succ w ih =>
    have h₀ := h.b_near m
    have h₁ : R.radius m ≤ R.radius (m+1) := h.rad_mono (by omega)
    have h₃ := h.rad_pos m
    have h₂ : K*R.b (m+1)/R.radius (m+1) ≤ 2*(K*R.b m / R.radius m) := by
      calc _ ≤ (K*(2*R.b m))/R.radius (m+1) := by have := h.rad_pos (m+1); gcongr
           _ ≤ K*(2*R.b m)/R.radius m := by have := h.b_pos m; gcongr
           _ = _ := by ring
    have hd' : d (m+1)/R.radius (m+1) ≤ 2*(K*R.b m/R.radius m):= by
      apply le_trans (div_le_div_of_nonneg_right (hd _) (h.rad_pos _).le) h₂
    rw [pow_succ]; have := ih (m+1); have := step m
    linarith

lemma inward (h:Lipschitz R) (hs : ∀ i, s i ≤ 1)
    (step : ∀ i, s i ≤ (1/3)*s (i+1) + (1/4)*(d (i+1)/R.radius (i+1))) (K : ℝ)
    (hk : 0≤ K) (hd : ∀ i, d i ≤ K* R.b i) (m : ℕ) : s m ≤ (3/2)*(K*R.b m/R.radius m) := by
  have h₀ : Tendsto (fun n:ℕ=> (1/3:ℝ)^n) atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h₁ := h₀.add_const ((3/2)*(K*R.b m/R.radius m))
  apply ge_of_tendsto (x:=atTop) (f:=fun n:ℕ=>_) (show Tendsto _ _ (𝓝 ((3/2)*(K*R.b m/R.radius m))) from ?_) (Eventually.of_forall (fun (n:ℕ)=> improve h hs step K hk hd n m))
  simpa only [zero_add] using h₁

lemma telescope (h:Lipschitz R) (h₀ : d 0 ≤ 0) (hd : ∀ i,d (i+1) ≤ d i+R.eps (i+1)*((4/3)*s (i+1)+d (i+1)/R.radius (i+1)))
    {K : ℝ} (hk : 0≤ K) (hs : ∀ i, s i ≤ (3/2)*(K*R.b i /R.radius i)) (hK : ∀ i,d i ≤ K*R.b i) (m : ℕ) : d m ≤ (K/2)*R.b m := by
  have ht i : i ≤ m → d i ≤ ((3*K)*R.b m)*(∑ j∈Finset.range i,R.eps (j+1) / R.radius (j+1)) := by
    induction i with
    | zero => simp [h₀]
    | succ i ih =>
      intro hi; rw [Finset.sum_range_succ, mul_add]
      have hb' := h.b_mono hi
      have hT : (4/3)*s (i+1)+d (i+1)/R.radius (i+1) ≤ 3*K*R.b m / R.radius (i+1) := by
        calc _ ≤ (4/3)*((3/2)*(K*R.b (i+1)/R.radius (i+1))) + K*R.b (i+1) / R.radius (i+1) := by
               gcongr
               · exact hs _
               · exact (h.rad_pos _).le
               exact hK _
             _ = 3*K*R.b (i+1)/R.radius (i+1) := by ring
             _ ≤ _ := by have := h.b_pos m; have := h.rad_pos (i+1); gcongr
      apply (hd i).trans
      apply add_le_add (ih (by omega))
      calc _ ≤ R.eps (i+1) * (3*K*R.b m/R.radius (i+1)) := by gcongr; exact (h.eps_pos _)
           _ = _ := by ring
  apply (ht _ le_rfl).trans
  have hK':0≤K*R.b m := mul_nonneg hk (h.b_pos _).le
  have := h.b_pos m
  have := mul_le_mul_of_nonneg_left (h.small m) (show 0≤3*K*R.b m from by positivity)
  linarith

lemma squeezing (h:Lipschitz R) (hs : ∀ i, s i ≤ 1)
    (step : ∀ i, s i ≤ (1/3)*s (i+1) + (1/4)*(d (i+1)/R.radius (i+1)))
    (h₀ : d 0 ≤ 0) (hd : ∀ i,d (i+1) ≤ d i+R.eps (i+1)*((4/3)*s (i+1)+d (i+1)/R.radius (i+1)))
    (hK : ∀ i,d i ≤ 4*R.b i) (m : ℕ) : d m ≤ 0 ∧ s m ≤ 0 := by
  have ht (k i:ℕ) : d i ≤ 4*(1/2)^k*R.b i := by
    induction k generalizing i with
    | zero => simpa only [pow_zero,mul_one] using hK i
    | succ k ih =>
      rw [pow_succ]
      convert telescope h h₀ hd (by positivity : 0 ≤ 4*(1/2:ℝ)^k) (inward h hs step (4*(1/2)^k) (by positivity) ih) ih i using 1 
      ring
  have hv m : d m ≤ 0 := by
    apply ge_of_tendsto (x:=atTop) (f:=fun n:ℕ => 4*(1/2)^n*R.b m) ?_ (Eventually.of_forall (fun i=> ht i m))
    simpa only [mul_zero,zero_mul] using (((tendsto_pow_atTop_nhds_zero_of_lt_one (show 0 ≤(1/2:ℝ) by norm_num) (by norm_num)).const_mul 4).mul_const (R.b m))
  exact ⟨hv m,by simpa only [zero_mul,zero_div,mul_zero] using inward h hs step 0 le_rfl (fun i => by rw [zero_mul]; exact hv i) m⟩

lemma unique_infinite (h:Lipschitz R) (hL: Limits R) {z z':ℕ→ℝ} {v v':∀ i,E i} (hv : InfiniteCourse R z v) (hv' : InfiniteCourse R z' v') : z=z' ∧ v=v' := by
  let d i:= |z i-z' i|
  let s i:= ‖v i-v' i‖
  have hh i : s i ≤ (1/3)*s (i+1) + (1/4)*(d (i+1) / R.radius (i+1)) ∧
     |R.wobbleLim i (z (i+1)) (v (i+1))- R.wobbleLim i (z' (i+1)) (v' (i+1))| ≤ R.eps (i+1) * ((4/3)*s (i+1) + d (i+1)/R.radius (i+1)):= by
    dsimp [s]; rw [(hv.goes i).1,(hv'.goes i).1]
    have H:=hL.slots i _ (hv.beta (i+1)) _ (hv.cap _)
    have H':=hL.slots i _ (hv'.beta (i+1)) _ (hv'.cap _)
    refine ⟨le_of_tendsto ((H.1.sub H'.1).norm) ?_, le_of_tendsto ((H.2.sub H'.2).abs) ?_⟩
    all_goals filter_upwards [eventually_gt_atTop i] with n hn
    · exact (h.estimates n i hn _ _ _ _ (hv.beta _) (hv'.beta _) (hv.cap _) (hv'.cap _)).1
    · exact (h.estimates n i hn _ _ _ _ (hv.beta _) (hv'.beta _) (hv.cap _) (hv'.cap _)).2
  have hd i : d (i+1) ≤ d i+R.eps (i+1)*((4/3)*s (i+1)+d (i+1)/R.radius (i+1)) := by
    refine le_trans ?_ (add_le_add_right (hh i).2 (d i))
    unfold d; rw [(hv.goes i).2,(hv'.goes i).2]
    generalize z (i+1)=x,z' (i+1)=y,R.alphaLim i=a
    generalize R.wobbleLim i x (v (i+1))=w, R.wobbleLim i y (v' (i+1))=W
    calc |x-y| = |(x+a+w-(y+a+W))+(W-w)| := by ring_nf
         _ ≤ |x+a+w-(y+a+W)|+|W-w| := abs_add_le ..
         _ = _ := by rw [abs_sub_comm W w]
  have hs i : s i ≤ 1 := by unfold s; linarith [norm_sub_le (v i) (v' i),hv.cap i,hv'.cap i]
  have h₀ : d 0 ≤ 0 := by simp [d,hv.coarse,hv'.coarse]
  have H i : d i ≤ 4*R.b i := by dsimp only [d]; linarith [abs_sub (z i) (z' i),h.size _ _ (hv.beta i),h.size _ _ (hv'.beta i)]
  have hy i := squeezing h hs (fun i=> (hh i).1) h₀ hd H i
  constructor <;> ext i
  · apply sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm (hy i).1 (abs_nonneg _)))
  exact sub_eq_zero.mp (norm_le_zero_iff.mp (hy i).2)


def iterate (R : Rules E) (z : ℕ → ℕ → ℝ) (N : ℕ) : (k i : ℕ) → E i
| 0, _ => 0
| k+1, i => R.term N i (z N (i+1)) (iterate R z N k (i+1))

lemma iterate_cap (h:Lipschitz R) (z : ℕ → ℕ→ℝ) (hz : ∀ N i, i ≤ N → z N i∈R.band i) (N : ℕ) (k : ℕ) {i : ℕ} (hi : i+k ≤ N) : ‖iterate R z N k i‖ ≤ 1/4 := by
  induction k generalizing i with
  | zero => simp [iterate]
  | succ k ih => apply h.image _ _ (by omega) _ (hz _ _ (by omega)) _ (ih (by omega))

variable {zN : ℕ → ℕ→ℝ} {vN : ℕ→ ∀ i, E i}

lemma iterate_close (h:Lipschitz R) (hc : FiniteCourse R zN vN) (N : ℕ) (k : ℕ) {i : ℕ} (hi : i+k ≤ N) : ‖vN N i-iterate R zN N k i‖ ≤ (1/3)^k*(1/4) := by
  induction k generalizing i with
  | zero => simpa only [iterate,sub_zero,pow_zero,one_mul] using hc.cap N i (by omega)
  | succ k ih =>
    let t:=iterate R zN N k (i+1); let V:=zN N (i+1)
    rw [(hc.goes N i (by omega)).1,iterate]
    have hx : V∈R.band _ := hc.beta N _ (by omega)
    apply le_trans (b:=(1/3)*‖vN N (i+1)-t‖+(1/4) * (|V-V|/R.radius (i+1)))
    · exact (h.estimates _ _ (by omega) V V _ t hx hx (hc.cap N (i+1) (by omega)) (iterate_cap h _ hc.beta N k (by omega))).1
    have hg := ih (i:=i+1) (by omega); change ‖vN N (i+1)-t‖ ≤ _ at hg
    simp only [sub_self,abs_zero,zero_div,mul_zero,add_zero]; rw [pow_succ]; linarith

lemma extract_beta (h:Lipschitz R) (hc : FiniteCourse R zN vN) (g : ℕ→ℕ) (hg : Tendsto g atTop atTop) :
    ∃ φ : ℕ→ ℕ, StrictMono φ ∧ ∃ z : ℕ → ℝ, z∈pi univ R.band ∧ Tendsto (zN ∘g ∘ φ) atTop (𝓝 z) := by
  classical
  let Z (k i : ℕ) := if i ≤ g k then zN (g k) i else zN i i
  have hz n : Z n ∈ pi univ R.band := by
    rintro i hi; unfold Z; split
    next h=> exact hc.beta _ _ h
    next h=> exact hc.beta _ _ le_rfl
  obtain ⟨t, ht₀, φ,hφ,ht⟩:= (isCompact_univ_pi h.bands).tendsto_subseq hz
  refine ⟨φ,hφ,t,ht₀,tendsto_pi_nhds.2 fun i=> ?_⟩
  apply (tendsto_pi_nhds.1 ht i).congr'
  filter_upwards [(hg.comp hφ.tendsto_atTop).eventually_ge_atTop i] with k hi
  exact if_pos hi

lemma ground_limit (h:Lipschitz R) (hL : Limits R) (g : ℕ→ℕ) (hg : Tendsto g atTop atTop) (i : ℕ)
    (z : ℕ→ℝ) {z' : ℝ} (hb : Tendsto z atTop (𝓝 z')) (hb' : z'∈ R.band (i+1)) (hz : ∀ᶠ k in atTop,z k∈ R.band (i+1))
    {x : ℕ→ E (i+1)} {x' : E (i+1)} (hc : Tendsto x atTop (𝓝 x')) (hc' : ‖x'‖ ≤ 1/4) (hx : ∀ᶠ k in atTop,‖x k‖ ≤ 1/4):
    Tendsto (fun k=>R.term (g k) i (z k) (x k)) atTop (𝓝 (R.termLim i z' x')) ∧ Tendsto (fun k=>R.wobble (g k) i (z k) (x k)) atTop (𝓝 (R.wobbleLim i z' x')) := by
  obtain ⟨hw,hW⟩:=hL.slots i z' hb' x' hc'
  have H (a b : ℝ) : Tendsto (fun k=> a*‖x k - x'‖+b*|z k-z'|) atTop (𝓝 0) := by
    simpa using (((hc.sub_const x').norm.const_mul a).add ((hb.sub_const z').abs.const_mul b))
  have he := (hg.eventually_gt_atTop i).and (hz.and hx)
  constructor
  · apply (hw.comp hg).congr_dist
    refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ (H (1/3) ((1/4)/R.radius (i+1)))
    filter_upwards [he] with k hk
    rw [dist_eq_norm]; exact ((h.estimates (g k) i hk.1 z' (z k) x' (x k) hb' hk.2.1 hc' hk.2.2).1).trans_eq (by rw [norm_sub_rev x',abs_sub_comm]; ring)
  apply (hW.comp hg).congr_dist
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ (H (R.eps (i+1)*(4/3)) (R.eps (i+1)/R.radius (i+1)))
  filter_upwards [he] with k hk
  rw [Real.dist_eq]; exact ((h.estimates (g k) i hk.1 z' (z k) x' (x k) hb' hk.2.1 hc' hk.2.2).2).trans_eq (by rw [norm_sub_rev x',abs_sub_comm]; ring)

lemma iterate_converges (h:Lipschitz R) (hL : Limits R) (hc : FiniteCourse R zN vN) (g : ℕ→ℕ) (hg : Tendsto g atTop atTop) {z : ℕ→ℝ} (hZ : z∈pi univ R.band) (hZ' : Tendsto (zN ∘g) atTop (𝓝 z)) (k i : ℕ) : ∃ x:E i, ‖x‖ ≤ 1/4 ∧ Tendsto (fun n=> iterate R zN (g n) k i) atTop (𝓝 x) := by
  induction k generalizing i with
  | zero => exact ⟨0,by simp,tendsto_const_nhds⟩
  | succ k ih =>
    obtain ⟨x,hx,hx'⟩:= ih (i+1)
    have hu n : ∀ᶠ j in atTop, zN (g j) n∈R.band n := (hg.eventually_ge_atTop n).mono fun a hₐ=> hc.beta _ _ hₐ
    have hv k n : ∀ᶠ j in atTop, ‖iterate R zN (g j) k n‖ ≤ 1/4 := (hg.eventually_ge_atTop (n+k)).mono fun a hₐ=> iterate_cap h _ hc.beta _ k hₐ
    have hw := ground_limit h hL g hg i (fun j=> zN (g j) (i+1)) (tendsto_pi_nhds.1 hZ' (i+1)) (hZ _ trivial) (hu _) hx' hx (hv k (i+1))
    refine ⟨_,le_of_tendsto hw.1.norm ?_,hw.1⟩
    exact hv (k+1) i

variable [∀ i, CompleteSpace (E i)]

lemma entries_converge (h:Lipschitz R) (hL : Limits R) (hc : FiniteCourse R zN vN) (g : ℕ→ℕ) (hg : Tendsto g atTop atTop) {z : ℕ→ℝ} (hZ : z∈pi univ R.band) (hZ' : Tendsto (zN ∘g) atTop (𝓝 z)) : ∃ x:∀ i,E i, Tendsto (vN ∘ g) atTop (𝓝 x) := by
  have hh (i : ℕ) : CauchySeq (fun n=>vN (g n) i) := by
    apply Metric.cauchySeq_iff.2
    intro ε hε
    have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (show 0≤(1/3:ℝ) by norm_num) (by norm_num)
    obtain ⟨k,hk⟩:= (ht.eventually (Iio_mem_nhds hε)).exists
    have H := Metric.cauchySeq_iff.1 (iterate_converges h hL hc _ hg hZ hZ' k i |>.choose_spec.2.cauchySeq)
    obtain ⟨M,hM⟩:= H (ε/3) (by positivity)
    obtain ⟨J,hJ⟩:= eventually_atTop.1 (hg.eventually_ge_atTop (i+k))
    refine ⟨max M J, fun j hj m hm=>?_⟩
    let P (n) := iterate R zN (g n) k i
    have hp (n : ℕ) (hn : J ≤ n) : dist (vN (g n) i) (P n) ≤ ε/4 := by
      rw [dist_eq_norm]; dsimp [P]; apply (iterate_close h hc _ k (hJ _ hn)).trans
      change (1/3:ℝ)^k < ε at hk
      linarith
    calc _ ≤ _ := dist_triangle_right _ _ (P m)
         _ ≤ _ := add_le_add_left (dist_triangle _ (P j) (P m)) _
         _ < _ := by linarith [hp _ ((le_max_right ..).trans hj),hp _ ((le_max_right ..).trans hm),show dist (P j) (P m) < ε/3 from hM j ((le_max_left ..).trans hj) m ((le_max_left ..).trans hm)]
  choose x hx using fun i => cauchySeq_tendsto_of_complete (hh i)
  exact ⟨x,tendsto_pi_nhds.mpr hx⟩

lemma walk (h:Lipschitz R) (hL : Limits R) (hc : FiniteCourse R zN vN) (g : ℕ→ℕ) (hg : Tendsto g atTop atTop) :
    ∃ φ : ℕ→ℕ, StrictMono φ ∧ ∃ (z : ℕ→ℝ) (x : ∀ i,E i), InfiniteCourse R z x ∧ Tendsto (zN ∘ g ∘ φ) atTop (𝓝 z) ∧ Tendsto (vN ∘g∘ φ) atTop (𝓝 x) := by
  obtain ⟨φ,hφ,z,hz,hZ⟩:= extract_beta h hc _ hg
  have ht:=hg.comp hφ.tendsto_atTop
  obtain ⟨x,hx⟩:=entries_converge h hL hc _ ht hz hZ
  refine ⟨φ,hφ,z,x,?_,hZ,hx⟩
  rw [tendsto_pi_nhds] at hZ hx
  have h₁ i := ht.eventually_ge_atTop i
  have h₂ i : ‖x i‖ ≤ 1/4:= le_of_tendsto (hx i).norm ((h₁ i).mono fun j hj=> hc.cap (g (φ j)) i hj)
  refine ⟨fun i=> hz i trivial,h₂, tendsto_nhds_unique (hZ 0) (tendsto_const_nhds.congr fun _=>(hc.coarse _).symm),fun i=>?_⟩
  have H:= ground_limit h hL _ ht i (x:=fun j=> vN (g (φ j)) (i+1)) (fun j=> zN (g (φ j)) (i+1)) (hZ (i+1)) (hz _ trivial) ((h₁ (i+1)).mono fun j hj=> hc.beta (g (φ j)) (i+1) hj) (hx (i+1)) (h₂ _) ((h₁ (i+1)).mono fun j hj=> hc.cap (g (φ j)) (i+1) hj)
  have h₀:= (h₁ (i+1)).mono fun j hj=> hc.goes (g (φ j)) i (by simpa only [Function.comp_apply,Nat.succ_le_iff] using hj)
  exact ⟨tendsto_nhds_unique (hx i) (H.1.congr' (h₀.mono fun j hj=> hj.1.symm)),tendsto_nhds_unique (hZ i) ((((hZ (i+1)).add ((hL.scalar i).comp ht)).add H.2).congr' (h₀.mono fun j hj=> hj.2.symm))⟩

theorem strong_limit (h:Lipschitz R) (hL : Limits R) (hc : FiniteCourse R zN vN) : ∃ (z: ℕ→ℝ) (x : ∀i, E i), InfiniteCourse R z x ∧ Tendsto zN atTop (𝓝 z) ∧ Tendsto vN atTop (𝓝 x) := by
  obtain ⟨φ,hφ,z,x,hz,h₁,h₂⟩:= walk h hL hc id tendsto_id
  suffices H : Tendsto (fun n=>(zN n,vN n)) atTop (𝓝 (z,x)) by exact ⟨z,x,hz,(continuous_fst.tendsto _).comp H,(continuous_snd.tendsto _).comp H⟩
  apply tendsto_of_subseq_tendsto
  intro g hg
  obtain ⟨φ,hφ,z',x',hz',h₁,h₂⟩:= walk h hL hc g hg
  obtain ⟨rfl,rfl⟩:= unique_infinite h hL hz hz'
  exact ⟨φ,h₁.prodMk_nhds h₂⟩

omit [∀ i, CompleteSpace (E i)]

structure OnePath (R : Rules E) (N : ℕ) (start : ℝ → E N) (t : ℝ) (z : ℕ→ℝ) (v : ∀i,E i) : Prop where
  beta i : i ≤ N → z i ∈ R.band i
  cap i : i ≤ N → ‖v i‖ ≤ 1/4
  coarse : z 0=t
  begins : v N=start (z N)
  goes i : i<N → v i=R.term N i (z (i+1)) (v (i+1)) ∧ z i=z (i+1)+R.alpha N i+R.wobble N i (z (i+1)) (v (i+1))

theorem inward_finite (h:Lipschitz R) (N : ℕ) (hN: s N ≤ d N / R.radius N)
    (step : ∀ i, i < N → s i ≤ (1/3)*s (i+1) + (1/4)*(d (i+1)/R.radius (i+1))) (K : ℝ)
    (hk : 0≤ K) (hd : ∀ i ≤ N, d i ≤ K* R.b i) {m : ℕ} (hm : m ≤ N) : s m ≤ (3/2)*(K*R.b m/R.radius m) := by
  induction hm using Nat.decreasingInduction with
  | self =>
    apply le_trans (hN.trans (div_le_div_of_nonneg_right (hd N le_rfl) (h.rad_pos N).le))
    have :=h.rad_pos N; have:=h.b_pos N; have : 0 ≤ K*R.b N/R.radius N:=by positivity
    linarith
  | of_succ i hi ih =>
    have h₁ : R.radius i ≤ R.radius (i+1) := h.rad_mono (by omega)
    have h₃ := h.rad_pos i
    have h₂ : K*R.b (i+1)/R.radius (i+1) ≤ 2*(K*R.b i / R.radius i) := by
      calc _ ≤ (K*(2*R.b i))/R.radius (i+1) := by have:=h.rad_pos (i+1); gcongr; exact h.b_near _
           _ ≤ K*(2*R.b i)/R.radius i := by have := h.b_pos i; gcongr
           _ = _ := by ring
    have hd' : d (i+1)/R.radius (i+1) ≤ 2*(K*R.b i/R.radius i):= by
      apply le_trans (div_le_div_of_nonneg_right (hd _ hi) (h.rad_pos _).le) h₂
    have H := step i hi
    linarith

theorem squeezing_finite (h:Lipschitz R) (N : ℕ) (hN: s N ≤ d N / R.radius N)
    (d_pos : 0 ≤ d N)
    (step : ∀ i, i<N → s i ≤ (1/3)*s (i+1) + (1/4)*(d (i+1)/R.radius (i+1)))
    (h₀ : d 0 ≤ 0) (hd : ∀ i,i<N → d (i+1) ≤ d i+R.eps (i+1)*((4/3)*s (i+1)+d (i+1)/R.radius (i+1)))
    (hK : ∀ i ≤ N,d i ≤ 4*R.b i) (m : ℕ) (hm : m ≤ N) : d m ≤ 0 ∧ s m ≤ 0 := by
  let s' (i:ℕ):= if i≤N then s i else 0
  let d' (i:ℕ):= if i≤N then d i else 0
  have hT K (hk : 0≤ K) (hK : ∀ i≤N,d i≤K*R.b i) : ∀ i, d' i ≤ (K/2)* R.b i := by
    have h₁ := @inward_finite _ _ _ s d h N hN step K hk hK
    have hb i : d' i ≤ K*R.b i := by unfold d'; split; exact hK _ ‹_›; have :=h.b_pos i; positivity
    have hs i : s' i ≤ 3/2*(K*R.b i/R.radius i) := by dsimp only [s']; split; exact h₁ ‹_›; have :=h.b_pos i; have := h.rad_pos i; positivity
    have hz i : d' (i+1) ≤ d' i+R.eps (i+1)*((4/3)*s' (i+1)+d' (i+1)/R.radius (i+1)) := by
      by_cases hi : i<N
      · simpa only [s',d',if_pos (show i+1≤N from hi), if_pos hi.le] using hd i hi
      simp only [s',d', if_neg (show ¬i+1≤N from hi),mul_zero,zero_div,add_zero]
      by_cases h': i≤N
      · rw [if_pos h',show i=N by omega]; exact d_pos
      rw [if_neg h']
    exact telescope h (s:=s') (d:=d') (by simpa only [d', if_pos (Nat.zero_le _)] using h₀) hz hk hs hb
  have ht (k i:ℕ) (hi : i ≤ N) : d i ≤ 4*(1/2)^k*R.b i := by
    induction k generalizing i with
    | zero => simpa only [pow_zero,mul_one] using hK i hi
    | succ k ih =>
      rw [pow_succ]
      convert hT _ (by positivity : 0 ≤ 4*(1/2:ℝ)^k) ih i using 1
      rw [show d' i=d i from if_pos hi]; ring_nf
  have hv m (hm : m ≤ N) : d m ≤ 0 := by
    apply ge_of_tendsto (x:=atTop) (f:=fun n:ℕ => 4*(1/2)^n*R.b m) ?_ (Eventually.of_forall (fun i=> ht i m hm))
    simpa only [mul_zero,zero_mul] using (((tendsto_pow_atTop_nhds_zero_of_lt_one (show 0 ≤(1/2:ℝ) by norm_num) (by norm_num)).const_mul 4).mul_const (R.b m))
  exact ⟨hv m hm,by simpa only [zero_mul,zero_div,mul_zero] using inward_finite h N hN step 0 le_rfl (fun i hi => by rw [zero_mul]; exact hv i hi) hm⟩

theorem unique_one (h:Lipschitz R) {N : ℕ} {z z':ℕ→ℝ} {v v':∀ i,E i} {start : ℝ→ E N} (hs : ∀ x∈R.band N,∀ y∈R.band N, ‖start x-start y‖ ≤ |x-y|/R.radius N) {t : ℝ} (hv : OnePath R N start t z v) (hv' : OnePath R N start t z' v') : ∀ i≤N,z i=z' i ∧ v i=v' i := by
  let d i:= |z i-z' i|
  let s i:= ‖v i-v' i‖
  have hh i (hi:i<N): s i ≤ (1/3)*s (i+1) + (1/4)*(d (i+1) / R.radius (i+1)) ∧
     |R.wobble N i (z (i+1)) (v (i+1))- R.wobble N i (z' (i+1)) (v' (i+1))| ≤ R.eps (i+1) * ((4/3)*s (i+1) + d (i+1)/R.radius (i+1)):= by
    dsimp [s]; rw [(hv.goes i hi).1,(hv'.goes i hi).1]
    exact h.estimates N i hi _ _ _ _ (hv.beta _ hi) (hv'.beta _ hi) (hv.cap _ hi) (hv'.cap _ hi)
  have hd i (hi:i<N): d (i+1) ≤ d i+R.eps (i+1)*((4/3)*s (i+1)+d (i+1)/R.radius (i+1)) := by
    refine le_trans ?_ (add_le_add_right (hh i hi).2 (d i))
    unfold d; rw [(hv.goes i hi).2,(hv'.goes i hi).2]
    generalize z (i+1)=x,z' (i+1)=y,R.alpha N i=a
    generalize R.wobble N i x (v (i+1))=w, R.wobble N i y (v' (i+1))=W
    calc |x-y| = |(x+a+w-(y+a+W))+(W-w)| := by ring_nf
         _ ≤ |x+a+w-(y+a+W)|+|W-w| := abs_add_le ..
         _ = _ := by rw [abs_sub_comm W w]
  have h₀ : d 0 ≤ 0 := by simp [d,hv.coarse,hv'.coarse]
  have H i (hi : i ≤ N) : d i ≤ 4*R.b i := by dsimp only [d]; linarith [abs_sub (z i) (z' i),h.size _ _ (hv.beta i hi),h.size _ _ (hv'.beta i hi)]
  have hS : s N ≤ d N / R.radius N := by unfold s d; rw [hv.begins,hv'.begins]; exact hs _ (hv.beta _ le_rfl) _ (hv'.beta _ le_rfl)
  intro i hi
  have hy := squeezing_finite h N hS (abs_nonneg _) (fun i hi=> (hh i hi).1) h₀ hd H i hi
  constructor
  · apply sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm (hy.1) (abs_nonneg _)))
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hy.2)

end YM.Extension.UV.Tail
