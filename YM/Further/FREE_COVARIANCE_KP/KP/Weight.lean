import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.LinearAlgebra.Trace
import YM.Analysis.SmoothJets
import YM.Gauge.MatrixGroup
import YM.Space.Orthogonal


/-!
# Further estimate for reading these free probe matrices

Power with one independently
selectable uniform price per symbol derivative order (fixed **before** the
family index is used). All punctured on frequency, no contact assertion.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Further.FreeCovariance.KP
open Filter Set Function Metric
open scoped Topology ContDiff BigOperators

structure Window where
  look : Set E4
  ok : IsOpen look
  hole : 0 ∉ look

instance : Membership E4 Window := ⟨fun U p => p ∈ U.look⟩
def whole : Window := ⟨{0}ᶜ,isOpen_compl_singleton,fun h => h rfl⟩

variable {ι : Type*} {U V : Window}
lemma Window.out {p : E4} (h : p∈U) : p≠0 := fun e => U.hole (e ▸ h)

/-- Power here is the *actual* power, positive for a small symbol;
negative for a pole. All mixed price queries bound operator norm on
unit Euclidean inputs. -/
structure Weight (U : Window) (k : ℤ) (f : ι → E4 → ℂ) : Prop where
  smooth i : ContDiffOn ℝ ∞ (f i) U.look
  quotes n : ∃ C : ℝ, 0≤C ∧ ∀ i,∀ p, p∈U → ‖iteratedFDeriv ℝ n (f i) p‖ ≤ C * ‖p‖^(k-n : ℤ)

namespace Weight
variable {f g : ι → E4 → ℂ} {k l : ℤ}
lemma reindex {μ : Type*} (h : Weight U k f) (a : μ → ι) : Weight U k (f ∘ a) where
  smooth i := h.smooth _
  quotes n := by obtain ⟨C,hC,h⟩ := h.quotes n; exact ⟨C,hC,fun i => h (a i)⟩
lemma use (h : Weight U k f) (hv : V.look ⊆ U.look) : Weight V k f where
  smooth i := (h.smooth i).mono hv
  quotes n := by obtain ⟨C,hC,h⟩ := h.quotes n; exact ⟨C,hC,fun i _ hp => h i _ (hv hp)⟩
lemma stay (h : Weight U k f) (hg : ∀ i, EqOn (f i) (g i) U.look) : Weight U k g where
  smooth i := (h.smooth i).congr (hg i).symm
  quotes n := by
    obtain ⟨C,hC,H⟩ := h.quotes n
    refine ⟨C,hC,fun i p hp => ?_⟩
    have he : f i =ᶠ[𝓝 p] g i := by filter_upwards [U.ok.mem_nhds hp] with q hq using hg i hq
    exact (EventuallyEq.iteratedFDeriv ℝ he n).eq_of_nhds ▸ H i p hp
lemma sum (hf : Weight U k f) (hg : Weight U k g) : Weight U k (fun i p => f i p + g i p) where
  smooth i := (hf.smooth i).add (hg.smooth i)
  quotes n := by
    obtain ⟨A,hA,ha⟩ := hf.quotes n; obtain ⟨B,hB,hb⟩ := hg.quotes n
    refine ⟨A+B,by positivity,fun i p hp => ?_⟩
    change ‖iteratedFDeriv ℝ n (f i+g i) p‖ ≤ _
    have hs := U.ok.mem_nhds hp
    rw [iteratedFDeriv_add_apply (((hf.smooth i).contDiffAt hs).of_le (by exact_mod_cast (le_top : (↑n:ℕ∞)≤⊤)))
      (((hg.smooth i).contDiffAt hs).of_le (by exact_mod_cast (le_top : (↑n:ℕ∞)≤⊤))),add_mul]
    exact (norm_add_le ..).trans (add_le_add (ha _ _ hp) (hb _ _ hp))
lemma within_price (n : ℕ) (f : E4 → ℂ) {p : E4} (h : p∈U) : iteratedFDerivWithin ℝ n f U.look p=iteratedFDeriv ℝ n f p :=
  iteratedFDerivWithin_of_isOpen _ U.ok h
lemma times (hf : Weight U k f) (hg : Weight U l g) : Weight U (k+l) (fun i p => f i p*g i p) where
  smooth i := (hf.smooth i).mul (hg.smooth i)
  quotes n := by
    choose A hA ha using hf.quotes
    choose B hB hb using hg.quotes
    refine ⟨∑ j∈Finset.range (n+1),(n.choose j:ℝ)*A j*B (n-j),Finset.sum_nonneg (fun j _ => by have a := hA j; have b := hB (n-j); positivity),fun i p hp => ?_⟩
    have hr := norm_pos_iff.mpr (U.out hp)
    have hs := norm_iteratedFDerivWithin_mul_le (hf.smooth i) (hg.smooth i) (U.ok.uniqueDiffOn)
       hp (show (n:ℕ∞ω)≤∞ by exact_mod_cast (le_top : (↑n:ℕ∞)≤⊤))
    simp_rw [within_price _ _ hp] at hs
    refine hs.trans ?_; rw [Finset.sum_mul]; refine Finset.sum_le_sum fun j hj => ?_
    have hj := Finset.mem_range_succ_iff.mp hj
    calc
      _ ≤ ((n.choose j:ℝ)*(A j * ‖p‖^(k-(j:ℤ))))*(B (n-j)*‖p‖^(l-((n-j:ℕ):ℤ))) := by
        have a := hA j
        have b := hB (n-j)
        gcongr
        exacts [ha _ _ _ hp,hb _ _ _ hp]
      _ = _ := by
        rw [show k+l-n = (k-j)+(l-((n-j:ℕ):ℤ)) by omega,zpow_add₀ hr.ne']; ring

lemma spare (U : Window) (c : ℂ) : Weight (ι:=ι) U 0 (fun _ _ => c) := by
  constructor
  · exact fun i => contDiffOn_const
  rintro (_|n)
  · exact ⟨‖c‖,norm_nonneg _,by simp⟩
  exact ⟨0,le_rfl, fun i p hp => by rw [iteratedFDeriv_succ_const]; simp⟩
lemma vanish (U : Window) (k) : Weight (ι:=ι) U k (fun _ _ => 0) := by
  constructor
  · exact fun i => contDiffOn_const
  exact fun n => ⟨0,le_rfl,fun i p hp => by cases n <;> simp⟩
lemma scale (hf : Weight U k f) (c : ℂ) : Weight U k (fun i p => c*f i p) := zero_add k ▸ (spare U c).times hf
lemma opposite (hf : Weight U k f) : Weight U k (fun i p => -f i p) := by simpa using hf.scale (-1)
lemma diff (hf : Weight U k f) (hg : Weight U k g) : Weight U k (fun i p => f i p-g i p) := by
  simpa only [sub_eq_add_neg] using hf.sum hg.opposite
lemma conjugated (h : Weight U k f) : Weight U k (fun i p => star (f i p)) := by
  let L := Complex.conjCLE.toContinuousLinearMap
  constructor
  · exact fun i => L.contDiff.comp_contDiffOn (h.smooth i)
  intro n; obtain ⟨C,hC,H⟩ := h.quotes n
  refine ⟨‖L‖*C,by positivity,fun i p hp => ?_⟩
  rw [mul_assoc]
  apply le_trans (L.norm_iteratedFDeriv_comp_left ((h.smooth i).contDiffAt (U.ok.mem_nhds hp)) (show (n:ℕ∞ω)≤∞ by exact_mod_cast (le_top : (↑n:ℕ∞)≤⊤)))
  gcongr
  exact H _ _ hp
lemma sum_finite {κ : Type*} (S : Finset κ) (f : κ → ι → E4 → ℂ) (h : ∀ i∈S, Weight U k (f i)) : Weight U k (fun a p => ∑ j∈S, f j a p) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using vanish U k
  | insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h _ (Finset.mem_insert_self ..)).sum (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma soften (hf : Weight U k f) (R : ℝ) (hR : 0<R) (bound : ∀ p:E4, p∈U→‖p‖≤R) (hk : l≤k) : Weight U l f where
  smooth := hf.smooth
  quotes n := by
    obtain ⟨A,hA,H⟩ := hf.quotes n
    refine ⟨A*R^(k-l),by positivity,fun i p hp => ?_⟩
    have ht := H i p hp
    have hx := norm_pos_iff.mpr (U.out hp)
    apply ht.trans
    rw [show k-(n:ℤ) = (k-l)+(l-n) by omega,zpow_add₀ hx.ne',mul_assoc]
    gcongr; exact zpow_le_zpow_left₀ (by omega) hx.le (bound p hp)

/-- Uniform scalar inversion on the order zero window. -/
lemma reverse (hf : Weight U 0 f) (b : ℝ) (hb : 0<b) (hx : ∀ i,∀ p:E4,p∈U → b≤‖f i p‖) : Weight U 0 (fun i p => (f i p)⁻¹) := by
  let S : Set ℂ := {0}ᶜ
  let G (z : ℂ) := z⁻¹
  have ht : IsOpen S := isOpen_compl_singleton
  have hG : ContDiffOn ℝ ∞ G S := contDiffOn_id.inv fun x hx => hx
  have he (i : ι) : MapsTo (f i) U.look S := fun p hp => norm_pos_iff.mp (hb.trans_le (hx i p hp))
  refine ⟨fun i => hG.comp (hf.smooth i) (he i),fun n => ?_⟩
  choose A hA H using hf.quotes
  let K := closedBall (0:ℂ) (A 0) ∩ {z : ℂ | b≤‖z‖}
  have hK : IsCompact K := (isCompact_closedBall ..).inter_right (isClosed_le continuous_const continuous_norm)
  have HK : K ⊆ S := fun x hx => norm_pos_iff.mp (hb.trans_le hx.2)
  have Hs (j : ℕ) : ∃ C : ℝ, 0≤C ∧ ∀ z∈K, ‖iteratedFDerivWithin ℝ j G S z‖ ≤ C := by
    have H := (hG.continuousOn_iteratedFDerivWithin (show (j:ℕ∞ω)≤∞ by exact_mod_cast (le_top : (↑j:ℕ∞)≤⊤)) ht.uniqueDiffOn).norm.mono HK
    obtain ⟨B,hB⟩ := hK.bddAbove_image H
    exact ⟨max 0 B,le_max_left ..,fun z hz => (hB (mem_image_of_mem _ hz)).trans (le_max_right ..)⟩
  choose B hB HB using Hs
  let c := ∑ j∈Finset.range (n+1),B j
  let d := 1+ ∑ j∈Finset.range (n+1),A j
  have hc : 0≤c := Finset.sum_nonneg fun _ _ => hB _
  have hd : 1≤d := (le_add_iff_nonneg_right 1).2 (Finset.sum_nonneg fun _ _ => hA _)
  refine ⟨(n.factorial:ℝ)*c*d^n,by have hp : 0 < d := zero_lt_one.trans_le hd; positivity,fun i p hp => ?_⟩
  have hr := norm_pos_iff.mpr (U.out hp)
  have hz : f i p ∈ K := ⟨by simpa using H 0 i p hp,hx i p hp⟩
  have h := norm_iteratedFDerivWithin_comp_le hG (hf.smooth i) (show (n:ℕ∞ω)≤∞ by exact_mod_cast (le_top : (↑n:ℕ∞)≤⊤)) ht.uniqueDiffOn U.ok.uniqueDiffOn (he i) hp (C:=c) (D:=d*‖p‖⁻¹)
    (fun j hj => (HB j _ hz).trans (Finset.single_le_sum (fun j _ => hB j) (Finset.mem_range_succ_iff.2 hj))) (fun j h1 hj => ?_)
  · rw [within_price _ _ hp,mul_pow] at h
    simpa only [zero_sub,zpow_neg,zpow_natCast,inv_pow,mul_assoc,comp_def,G] using h
  rw [within_price _ _ hp]
  apply (H j i p hp).trans; rw [zero_sub,zpow_neg,zpow_natCast,mul_pow,inv_pow]; gcongr
  exact le_trans ((Finset.single_le_sum (fun j _ => hA j) (Finset.mem_range_succ_iff.mpr hj)).trans (le_add_of_nonneg_left zero_le_one)) (le_self_pow₀ hd (Nat.one_le_iff_ne_zero.mp h1))

/-- Exact dilation permits negative powers. -/
lemma template (ι : Type*) (k : ℤ) (f : E4 → ℂ) (hf : ContDiffOn ℝ ∞ f whole.look) (hh : ∀ a : ℝ, 0<a → ∀ p : E4, f (a • p)=(a^k : ℝ) • f p) :
    Weight (ι:=ι) whole k (fun _ => f) := by
  refine ⟨fun _ => hf, fun n => ?_⟩
  let S := sphere (0:E4) 1
  have ht : S ⊆ whole.look := fun z hz => by intro he; change z=0 at he; rw [he] at hz; simp [S] at hz
  have hn : (n:ℕ∞ω) ≤ ∞ := by exact_mod_cast (le_top : (↑n:ℕ∞)≤⊤)
  obtain ⟨C,hC⟩ := (isCompact_sphere (0:E4) 1).bddAbove_image ((hf.continuousOn_iteratedFDerivWithin hn whole.ok.uniqueDiffOn).norm.mono ht)
  refine ⟨max 0 C,le_max_left ..,fun _ p hp => ?_⟩
  let a := ‖p‖
  have ha : 0<a := norm_pos_iff.mpr (whole.out hp)
  let w := a⁻¹ • p
  let L := a • ContinuousLinearMap.id ℝ E4
  have hw : w∈S := by simp [w,S,norm_smul, (show ‖p‖≠0 from ha.ne'),a]
  have hh' : L w = p := smul_inv_smul₀ ha.ne' _
  have ho : L ⁻¹' whole.look=whole.look := by ext x; simp [whole,L,ha.ne']
  have he : iteratedFDerivWithin ℝ n (f ∘ L) (L ⁻¹' whole.look) w = _ := L.iteratedFDerivWithin_comp_right hf whole.ok.uniqueDiffOn (by rw [ho]; exact whole.ok.uniqueDiffOn) (hh' ▸ hp) hn
  rw [ho, within_price _ _ (ht hw),hh', within_price _ _ hp] at he
  have hv : f ∘ L = (a^k) • f := funext fun x => hh _ ha x
  rw [hv,iteratedFDeriv_const_smul_apply ((hf.contDiffAt (whole.ok.mem_nhds (ht hw))).of_le hn)] at he
  rw [show (iteratedFDeriv ℝ n f p).compContinuousLinearMap _ = a^n • iteratedFDeriv ℝ n f p from ?_] at he
  · have ht' := (show ‖iteratedFDerivWithin ℝ n f whole.look w‖ ≤ C from hC (mem_image_of_mem _ hw))
    rw [within_price _ _ (ht hw)] at ht'
    change _ ≤ _*a^_
    have H := congr_arg norm he
    simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (pow_pos ha n),abs_of_pos (zpow_pos ha k)] at H
    rw [zpow_sub₀ ha.ne',zpow_natCast,← mul_div_assoc,le_div_iff₀ (pow_pos ha n),mul_comm,← H,mul_comm]; gcongr; exact ht'.trans (le_max_right ..)
  ext v
  change iteratedFDeriv ℝ n f p (fun i => a • v i) = a^n • _
  simpa using (ContinuousMultilinearMap.map_smul_univ (iteratedFDeriv ℝ n f p) (fun _ => a) v)

end Weight
end YM.Further.FreeCovariance.KP
