import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Weights
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Extend
/-!
# Absolutized flags: true power series, on REAL jets, radius certificates

Since all the primitive energy estimates are on *real* group fields with
untouched indicator queries, use series for the real probes before, not after,
taking signed sums. Real scalar throughout, not analytically continuing any V
point. This allows multiplication and inference of uniform Banach analytic
germs without ever pricing in displaced-field domains (differentiating along
V may still need particular changes in integral chart).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Ray
open Filter Set Function RG Push.AbsoluteSums
open scoped Topology BigOperators NNReal ENNReal ContDiff
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {a v p c d : ℝ} {f g : ℝ → E}
def sun := Set.Icc (-1:ℝ) 1
structure Scout (R : ℝ) (f : ℝ → E) (C : ℝ) : Prop where
  ray : 1≤R
  scored : ∃ b:ℕ→E, SumBudget (fun i=> ‖b i‖) C ∧∀ s∈sun, HasSum (fun i=>(s/R)^i • b i) (f s)
lemma ratio_le (h:1≤v) {s:ℝ} (hs:s∈sun): |s/v|≤ 1:=by rw [abs_div,abs_of_nonneg (zero_le_one.trans h)]; exact (div_le_one (zero_lt_one.trans_le h)).mpr ((abs_le.mpr hs).trans h)
lemma at_flight (c:ℝ) (hc:‖c‖≤ 1) {b:ℕ→E} (h:SumBudget (fun i=> ‖b i‖) a):SumBudget (fun i=> ‖c^i • b i‖) a:= budget_mono h (fun _=>norm_nonneg _) (fun i=>by rw [norm_smul]; apply mul_le_of_le_one_left (norm_nonneg _); rw [Real.norm_eq_abs, abs_pow]; exact pow_le_one₀ (abs_nonneg _) hc)
namespace Scout
lemma nonneg (h:Scout p f c) : 0≤c:=budget_nonneg h.scored.choose_spec.1
lemma enlarged (h : Scout p f c) (hv:c≤d) : Scout p f d:= by obtain ⟨b,hb,h⟩:= h.scored; exact ⟨‹Scout p f c›.ray,b,budget_loosen hb hv,h⟩
lemma replace (h:Scout p f c) (he: Set.EqOn f g sun): Scout p g c:= ⟨h.ray,h.scored.choose,h.scored.choose_spec.1,fun x hx=> he hx ▸ (h.scored.choose_spec.2 x hx)⟩
lemma held (h:Scout p f c) (hx:a ∈ sun): ‖f a‖ ≤ c:=by obtain ⟨hr,b,hH,hv⟩:= h; have hh:=at_flight (a/p) (ratio_le hr hx) hH; rw [← (hv a hx).tsum_eq]; exact (norm_tsum_le_tsum_norm hh.2.1).trans hh.2.2
lemma lessen (h:Scout p f c) (ha:1≤a)(hv:a≤p): Scout a f c:=by
  obtain ⟨hr,b,hb,h⟩:= h; have ha':=zero_lt_one.trans_le ha; have hp:=ha'.trans_le hv; let r:= a/p
  have hv: ‖r‖≤1:=by rw [Real.norm_of_nonneg (by unfold r; positivity : 0≤r)]; exact (div_le_one hp).mpr hv
  refine ⟨ha,(fun i=>r^i • b i),at_flight _ hv hb,fun s hs=>?_⟩; simp_rw [smul_smul,← mul_pow,show s/a*r=s/p from (by unfold r; field_simp)]; exact h s hs
lemma still (hp:1≤p) (z : E) : Scout p (fun _=> z) ‖z‖:= by
  let b : ℕ→E :=fun i=> if i=0 then z else 0
  refine ⟨hp,b,⟨fun i=>norm_nonneg _,?_,?_⟩,?_⟩
  · apply (hasSum_single (b:=0) ?_).summable; intro i hi; simp [b,hi]
  · rw [tsum_eq_single 0 (fun i hi=> by simp [b,hi])]; simp [b]
  intro s hs; convert (hasSum_single (f:=fun i=>(s/p)^i • b i) (b:=0) ?_); simp [b]
  intro i hi; simp [b,hi]
lemma line (hp:1≤p): Scout p id p:= by
  let b : ℕ→ℝ:=fun i=> if i=1 then p else 0; have hz:= zero_lt_one.trans_le hp
  refine ⟨hp,b,⟨fun i=>norm_nonneg _, (hasSum_single (b:=1) (f:=fun i=>‖b i‖) (fun i hi=>by simp [b,hi])).summable,?_⟩,fun i hi=>?_⟩
  · rw [tsum_eq_single 1 (fun i hi=>by simp [b,hi])]; simp [b,Real.norm_of_nonneg hz.le]
  have hi: id i=(i/p)^(1:ℕ) • b 1:=by simp [b,hz.ne']
  rw [hi]; exact hasSum_single (b:=1) (fun j hj=>by simp [b,hj])
lemma pair (h:Scout p f c) (hk:Scout p g d) : Scout p (fun i=> f i+g i) (c+d):=by
  obtain ⟨hr,b,hb,h⟩:= h; obtain ⟨r,hF,hk⟩:= hk.scored
  refine ⟨hr, (fun i=>b i+r i), budget_mono (budget_plus hb hF) (fun i=>norm_nonneg _) (fun i=>norm_add_le ..),?_⟩; intro s hs; simp_rw [smul_add]; exact (h s hs).add (hk s hs)
lemma scale (h:Scout p f c) (b : ℝ) : Scout p (fun x=> b • f x) (‖b‖*c):=by
  obtain ⟨h,z,hz,hb⟩:= h; refine ⟨h,(fun i=> b • z i),?_ ,?_⟩
  · simp_rw [norm_smul]; exact budget_scale (norm_nonneg _) hz
  intro x hx; simp_rw [smul_comm _ b]; exact (hb x hx).const_smul b
lemma pieces {ι : Type*} (s : Finset ι) (F:ι→ℝ→E) (b : ι→ℝ) (hp : 1≤p) (h : ∀ i∈s,Scout p (F i) (b i)):Scout p (fun x=>∑ i∈s,F i x) (∑ i∈s,b i):=by
  classical induction s using Finset.induction_on with
  | empty => simpa using! still hp (0:E)
  | insert i s hi ht => simp_rw [Finset.sum_insert hi]; exact (h i (Finset.mem_insert_self ..)).pair (ht fun j hj=> h j (Finset.mem_insert_of_mem hj))
end Scout
end YM.FullVolume.Ray
