import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Brush
import YM.UVExtension.Limits

/-!
 Wobbling probe twins. The angular chart at which a level-wise UV estimate is
 tested need not be fixed or convergent. Distinguish C^n-near and bounded at
 those positions from equicontinuity in the chart, which is not always needed or true.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Steady
open Filter Function Metric Set ConnectedActivityE6 Blaze
open scoped Topology Classical ContDiff BigOperators
variable {ι J : Type*} {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G]
variable (v: Filter ι)
-- Norm-bounded eventually: no order filter required.
def Together (f:ι→ Bool→F) := (∃ r:ℝ, ∀ᶠ n in v,∀ i,‖f n i‖≤r)∧ Tendsto (fun n=> dist (f n true) (f n false)) v (𝓝 0)
def apart (p:ι→Prop):= v⊓𝓟 {n|p n}
lemma gathered {p q r :ι→Prop}(hp:∀ᶠ i in apart v r,p i) (hq:∀ᶠ i in apart v (fun n=>¬r n),q i): ∀ᶠ i in v,(r i → p i)∧(¬r i → q i):=(eventually_inf_principal.mp hp).and (eventually_inf_principal.mp hq)
namespace Together
variable {v} {f g:ι→ Bool→ F}{h:ι→ Bool→ G}
lemma steady (f: F): Together v (fun _ _=> f):=⟨⟨‖f‖,by simp⟩,(tendsto_const_nhds (x:=(0:ℝ))).congr' (by filter_upwards with i; simp)⟩
lemma finely (p:Together v f) {q : Filter ι}(hq:q≤v):Together q f:= ⟨let ⟨b,h⟩:=p.1; ⟨b,hq h⟩,p.2.mono_left hq⟩
lemma excites (p:Together v f) {w:Filter J}{q:J→ι}(h:Tendsto q w v):Together w (fun n i=> f (q n) i):=
   ⟨let ⟨b,hb⟩:=p.1; ⟨b,h.eventually hb⟩,p.2.comp h⟩
lemma shimmy (p:Together v f)(h:∀ᶠ i in v, f i=g i): Together v g:= by
   obtain ⟨⟨a,p⟩,hp⟩:=p; refine ⟨⟨a,(p.and h).mono fun x hx=>hx.2 ▸ hx.1⟩,hp.congr' ?_⟩; filter_upwards [h] with i hi; rw [hi]
lemma compact {K:Set F}(hK:IsCompact K)(p:Together v f)(hm:∀ᶠ i in v,∀ n,f i n∈ K){T:F→G}(h:ContinuousOn T K): Together v (fun i t=> T (f i t)):=by
   obtain ⟨z,hz⟩:= ((hK.image_of_continuousOn h).isBounded).exists_norm_le
   refine ⟨⟨z,hm.mono fun n hn i=> hz _ (mem_image_of_mem _ (hn i))⟩,?_⟩
   rw [Metric.tendsto_nhds]
   intro ε he; obtain ⟨δ,hδ,h⟩:= Metric.uniformContinuousOn_iff.mp (hK.uniformContinuousOn_of_continuous h) ε he
   filter_upwards [hm,p.2.eventually (gt_mem_nhds he),p.2.eventually (gt_mem_nhds hδ)] with i hi hv hV
   rw [Real.dist_eq,sub_zero,abs_of_nonneg dist_nonneg]; exact h _ (hi _) _ (hi _) hV
lemma continuous [ProperSpace F] (p:Together v f) {T:F→G}(h:Continuous T) : Together v (fun i t=> T (f i t)):=by
   obtain ⟨r,hr⟩:= p.1; exact compact (isCompact_closedBall 0 r) p (hr.mono fun n hn i=> mem_closedBall.mpr (by rw [dist_zero_right]; exact hn i)) h.continuousOn
lemma prod (p:Together v f)(q:Together v h): Together v (fun x t=> (f x t,h x t)):=by
  obtain ⟨b,hb⟩:=p.1; obtain ⟨k,hk⟩:=q.1; refine ⟨⟨max b k,(hb.and hk).mono fun n h j=>max_le_max (h.1 _) (h.2 _)⟩,?_⟩
  simpa only [max_self] using! p.2.max q.2
lemma add (p:Together v f)(q:Together v g):Together v (fun x t=>f x t+g x t):=by
  obtain ⟨b,hb⟩:=p.1; obtain ⟨k,hk⟩:=q.1
  refine ⟨⟨b+k,(hb.and hk).mono fun n h j=>(norm_add_le ..).trans (add_le_add (h.1 _) (h.2 _))⟩,squeeze_zero' (Eventually.of_forall fun i=> dist_nonneg) (Eventually.of_forall fun i=> dist_add_add_le (f i true) (g i true) _ _) (by simpa only [add_zero] using p.2.add q.2)⟩ -- arg check
lemma cap (p:Together v f)(ε:ℝ)(h:0<ε): ∀ᶠ i in v, ‖f i true-f i false‖≤ε:=by
  filter_upwards [p.2.eventually_le_const h] with x hx; exact (dist_eq_norm ..).symm.trans_le hx
lemma of_cap (f:ι→ Bool→F) (p:∃ r:ℝ,∀ᶠ x in v,∀ i,‖f x i‖≤r) (h:∀ ε:ℝ,0<ε → ∀ᶠ n in v, ‖f n true-f n false‖≤ε):Together v f:=by
  refine ⟨p,Metric.tendsto_nhds.mpr (fun ε he=> ?_)⟩; filter_upwards [h (ε/2) (half_pos he)] with n hn; rw [Real.dist_eq,sub_zero,abs_of_nonneg dist_nonneg,dist_eq_norm]; exact hn.trans_lt (half_lt_self he)
lemma split (r:ι→Prop)(p:Together (apart v r) f)(q:Together (apart v (fun n=>¬r n)) f):Together v f:=by
   obtain ⟨b,hb⟩:=p.1; obtain ⟨k,hk⟩:= q.1; refine of_cap f ⟨max b k,?_⟩ (fun ε he=>?_)
   · filter_upwards [gathered v hb hk] with n h i; by_cases hy:r n
     exact (h.1 hy i).trans (le_max_left ..); exact (h.2 hy i).trans (le_max_right ..)
   filter_upwards [gathered v (p.cap ε he) (q.cap ε he)] with n h; exact by_cases h.1 h.2
lemma scalar [NormedSpace ℝ F] [NormedSpace ℝ G] (p:Together v f) (L:F→L[ℝ] G): Together v (fun n i=> L (f n i)):=by
   obtain ⟨k,hk⟩:=p.1; refine ⟨⟨‖L‖*k,hk.mono fun n h i=> (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (h _) (norm_nonneg _))⟩,?_⟩
   apply squeeze_zero' (Eventually.of_forall fun _=>dist_nonneg) (Eventually.of_forall fun i=> ?_) ((mul_zero (‖L‖)) ▸ p.2.const_mul ‖L‖)
   rw [dist_eq_norm,dist_eq_norm,← map_sub]; exact L.le_opNorm _
end Together
end YM.UVExtension.Steady
