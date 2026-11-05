import YM.Contacts.Harvest.Estimate
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Integral.DominatedConvergence
/-! # Absoluteness of sums and controlling one open layer

Only L1 of the precisely regulated sums; not absolute correlations of the separate polynomial
or forest terms (for a single choice of test it is crucial that we already summed those pieces).
Include auxiliary estimate being proved by induction. Can choose **any election**, even while
calling the IH on a forest changing one block. Supplies root-annular absolute summed estimates
for other current groups from the parameterized estimate.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Harvest
open Function Filter Set Metric MeasureTheory Submodule Table Spec Normal MultipleContact OPE Layers
open scoped Topology Classical BigOperators ContDiff InnerProductSpace MeasureTheory NNReal ENNReal
section series
variable {E X I : Type*} [MeasureSpace E] [NormedAddCommGroup X][NormedSpace ℝ X] {f g : E→ X} {c d : ℝ}
structure Dust (f : E→X) (c:ℝ) : Prop where
   integrated : Integrable f
   price : (∫ x, ‖f x‖) ≤ c
namespace Dust
-- eventually equality, not replacing shells by disjoint supports of their point-wise integrands.
omit [NormedSpace ℝ X]
lemma mono (h : Dust f c)(hm : c ≤ d) : Dust f d :=⟨h.integrated,h.price.trans hm⟩
lemma dry (h : Dust f c) : 0≤ c:= (integral_nonneg (fun _=> norm_nonneg _)).trans h.price
lemma transfer (h : Dust f c)(hx : f =ᵐ[volume] g) : Dust g c := ⟨h.integrated.congr hx, by rw [← integral_congr_ae (g:=fun x=>‖g x‖) (f:=fun x=>‖f x‖) (hx.fun_comp norm)]; exact h.price⟩
lemma zero (hc : 0 ≤ c) : Dust (0:E→X) c:= ⟨integrable_zero .., by simpa only [Pi.zero_apply, norm_zero,integral_zero] using hc⟩
lemma plus (h : Dust f c)(k : Dust g d) : Dust (f+g) (c+d):= by
   have hf:= h.integrated; have hg:= k.integrated; refine ⟨hf.add hg, le_trans (integral_mono (hf.add hg).norm (hf.norm.add hg.norm) fun x=> norm_add_le ..) ?_⟩; rw [integral_add' hf.norm hg.norm]; exact add_le_add h.price k.price
lemma finite {c : I → ℝ}{f : I → E→ X} (p : Finset I) (h : ∀ i∈p,Dust (f i) (c i)): Dust (fun x=>∑ i∈p,f i x) (∑ i∈p,c i):= by
   induction p using Finset.induction with
   | empty=> simp_rw [Finset.sum_empty]; exact Dust.zero le_rfl
   | insert i p hi ih=> simp_rw [Finset.sum_insert hi]; exact (h i (by simp)).plus (ih fun j hj=> h _ (Finset.mem_insert_of_mem hj))
lemma holds [NormedSpace ℝ X] (h : Dust f c) : ‖∫ x, f x‖≤ c := (norm_integral_le_integral_norm f).trans h.price

variable [CompleteSpace X][Countable I] {T : I→ E→X}{C : I→ℝ}
omit [CompleteSpace X] [Countable I] in
lemma norm_paid (hh : ∀ i,Dust (T i) (C i))(h : Summable C) : Summable fun i=> ∫ t, ‖T i t‖:= Summable.of_nonneg_of_le (fun _=>integral_nonneg fun _=>norm_nonneg _) (fun i=> (hh i).price) h
omit [CompleteSpace X] in
lemma suffices_absolute [NormedSpace ℝ X] (hh : ∀ i,Dust (T i) (C i))(h : Summable C) (hs : ∀ᵐ x:E, HasSum (fun i=> T i x) (f x)) : HasSum (fun i=>∫ x,T i x) (∫ x,f x):= by
    have ht:= hasSum_integral_of_summable_integral_norm (fun i=> (hh i).integrated) (norm_paid hh h); rw [integral_congr_ae (hs.mono fun x hx=> hx.tsum_eq)] at ht; exact ht
omit [NormedSpace ℝ X]
lemma collected (hh : ∀ i,Dust (T i) (C i))(h : Summable C) : ∃ f, Dust f (∑' i,C i) ∧ ∀ᵐ x:E, HasSum (fun i=> T i x) (f x) := by
   let g i:= (hh i).integrated.toL1 (T i); have hv i : ‖g i‖ ≤ C i:= (L1.norm_of_fun_eq_integral_norm (hh i).integrated).trans_le (hh i).price
   have hp:= Summable.of_nonneg_of_le (fun i=> norm_nonneg _) hv h
   let f:= ∑' i,g i; have hk : ‖f‖ ≤ ∑' i,C i:= (norm_tsum_le_tsum_norm hp).trans (hp.tsum_le_tsum hv h)
   refine ⟨f, ⟨L1.integrable_coeFn f, (L1.norm_eq_integral_norm f).symm.trans_le hk⟩,?_⟩ -- coe here f→L1?
   filter_upwards [Lp.hasSum_coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr hp),ae_all_iff.mpr fun i=> (hh i).integrated.coeFn_toL1] with x hx h; have he : (fun i=>g i x)=(fun i=> T i x) := funext fun i=> h i; change HasSum _ (f x); rw [← he]; exact hx
omit [Countable I] in
lemma reunites {f : ℕ → E→X}{p : E→X} {c : ℕ→ℝ} (h : Summable c)(hp : ∀ i, Dust (f i) (c i))(hm : ∀ᵐ x:E,∀ᶠ i in (atTop:Filter ℕ),(∑ j∈Finset.range i,f j x)=p x) : Dust p (∑' i,c i) ∧ ∀ᵐ x:E, HasSum (fun i=> f i x) (p x):= by
   obtain ⟨g,hg,hG⟩:= collected hp h; have H : g =ᵐ[volume] p:= by
      filter_upwards [hm,hG] with x hx hh; exact tendsto_nhds_unique (hh.tendsto_sum_nat) (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm (g:=(fun _ : ℕ=>p x)) hx))
   exact ⟨hg.transfer H, (H.and hG).mono fun x hx=>hx.1 ▸ hx.2⟩
end Dust

lemma geometric_dyadic {γ : ℝ}(h:0<γ) : Summable fun i=> (dyad i)^γ:=by
    let z:=(1/2:ℝ); apply Summable.congr (f:=fun n:ℕ=>(z^γ)^n) (summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num [z]) γ) (Real.rpow_lt_one (by norm_num [z]) (by norm_num [z]) h)) ?_
    intro i; change (z^γ)^i=(z^i)^γ; rw [← Real.rpow_mul_natCast (by norm_num [z]),mul_comm,Real.rpow_natCast_mul (by norm_num [z])]
end series

variable {G : Gauge}{C : Family G}{S: Table C.book}{F: Extraction.Order}{Z : Final C F S}
variable {E X W I : Type}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E][MeasureSpace E][BorelSpace E][(volume:Measure E).IsAddHaarMeasure]
 [NormedAddCommGroup X][NormedSpace ℝ X][NormedSpace ℂ X][IsScalarTower ℝ ℂ X][CompleteSpace X]
variable {k : ℕ}{d:Fin k→ℕ}{g : Normal.Group k}{P : E→ₗᵢ[ℝ] Points k}{Q:Pieces g}
variable (M : Devices Z.sector.derivatives)
namespace Route
variable (r : Route P Q I W)(D : Reader E W X k Z.sector.derivatives)(T : W→ Cells S d)
local notation "GN" => Normal.Group k
local notation "F'" => Board (Normal.Group k) (Letter Z.sector.derivatives)
def scoreAt (w:W)(p : SmoothTests E)(F : Score E (Board (Normal.Group k) (Letter Z.sector.derivatives)))(x:E):= D w x (action x p F)
def windings (f : Menu k)(w : W)(p : SmoothTests E): E→ X := scoreAt D w p ((r.components M T w).election P (r.length w) f Q)
/-- Final estimate (inductively even with smaller shell readers). Derivative order not a cut
choice. Does not assume scale separation other than paid for by taking smaller loans. -/
structure Achieves [Fintype I] (Z : Final C F S) (M : Devices Z.sector.derivatives) (r : Route P Q I W) (T : W→ Cells S d) (B : W→ℝ) (D : Reader E W X k Z.sector.derivatives) (γ : ℝ)(c : ℝ): Prop where
   estimates (f : Menu k)(w : W) (p : SmoothTests E){m : ℝ}(hp: tsupport p.val ⊆ r.stage w)
       (hx: Jet (stairs d Q) univ (composed (r.frame w) p).val m) : Dust (r.windings M D T f w p) (c*m*r.bag d B w (generosity Q γ)* shadow Q f γ)

end Route
end YM.Contacts.Harvest
