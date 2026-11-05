import YM.FullVolume.Ray.Veer
/-! Stock and full actual Gaussian ratio (submarginal). Weigh exponential with positive radius away from zero. Nodes prerouted. Exponent real-value along V shape — no bound on exponent as long as priced at all farther real nodes. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Ray.Fold
open Filter Function Set RG ConnectedActivityE6.Blaze Planned.AtomRegular Next.Foundations Finset
open scoped Topology BigOperators NNReal ContDiff
variable {R δ c b:ℝ} {k i n:ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h:Fold R δ) (L Γ:E→ℝ) (n:ℕ)
-- indicator label power (evaluated V germs); `pulse`. weight exponent lambda real positive
abbrev jet (t:ℝ) (y:E):= L y*h.flow t^n*Real.exp (h.sqcost t*Γ y)
def charge (k : ℕ):ℝ:= max (ink.pay (mirror (k:=2*k) (-1))) (ink.pay (mirror (k:=2*k) 1))
lemma holds (z:ℝ) (k): ink.pay (h.seat (k:=2*k) z)≤charge k:=by unfold seat pole; split; exact le_max_left ..; exact le_max_right ..
variable {h L n Γ} {x:E}
lemma scores (hv:ContDiffAt ℝ k L x) (hg:ContDiffAt ℝ k Γ x) (hc:0≤c) (ht:0≤b) (p :∀ i:Fin (2*k+1), Brush k c b (jet h L Γ n (R*h.seat (Γ x) i)) x):
    Weigh k x R ((charge k)*(1+δ)^n*c) b (jet h L Γ n):= by
  let q:= Γ x; let f:= seat (k:=2*k) h q; let w t:= h.flow t ^ n * Real.exp (h.sqcost t*q)
  have hw(i): Scout R w ((1+δ)^n*Real.exp (h.sqcost (R*f i)*q)):= (h.pulse.power n).multiplies ((h.unveils q).enlarged (Real.exp_monotone (h.landing q i)))
  have he : ∀ t:ℝ, ContDiffAt ℝ k (jet h L Γ n t) x := fun i=> ((hv.mul contDiffAt_const).mul ((contDiffAt_const.mul hg).exp))
  have hf (i): R*h.seat q i=R*f i:=rfl
  refine ⟨ht,fun t _=> he t,fun y hy j hj=>?_⟩
  obtain ⟨g,hg,hZ⟩:= measured (u:=fun t=> h.flow t^n) h.printed (hv.of_le (Nat.cast_le.mpr hj)) (hg.of_le (Nat.cast_le.mpr hj)) y
  have hp (i): ‖g (R*f i) * w (R*f i)‖≤ c*b^j:= Eq.trans_le (congr_arg (‖·‖) (hZ _).symm) (point_norm (p _) hj hy) -- norm
  have hR:=h.full.2.2
  let K i t:= g (R*f i)*w t*ink.lamp f i (t/R)
  let T i:=(1+δ)^n*(c*b^j)*ink.prices f i
  have hK i: Scout R (K i) (T i):=by
    have hσ: |R*f i|≤6*R:= by unfold f; rw [abs_mul,abs_of_pos h.full.1,mul_comm _ R]; exact mul_le_mul_of_nonneg_left (h.realms ..) h.full.1.le
    have hv: 1≤h.flow (R*f i):=(h.moves _ hσ).1
    refine Scout.enlarged (((hw i).scale (g (R*f i))).multiplies (ink.vitals f i h.price)) (mul_le_mul_of_nonneg_right ?_ (ink.price_pos f i))
    let e:=Real.exp (h.sqcost (R*f i)*q)
    have h' := hp i; dsimp only [w] at h'; rw [norm_mul,Real.norm_of_nonneg (show 0≤ _ * Real.exp _ from mul_nonneg (pow_nonneg (zero_le_one.trans hv) n) (Real.exp_nonneg _))] at h'
    rw [mul_left_comm]; apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by linarith) n)
    apply le_trans _ h'; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); exact le_mul_of_one_le_left (Real.exp_nonneg _) (one_le_pow₀ hv)
  refine ((Scout.pieces _ _ _ h.price (fun i (_:i∈Finset.univ)=> hK i)).enlarged ?_).replace fun t he=> ?_
  · change ∑ i,T i≤_
    unfold T; rw [← mul_sum]; exact (mul_le_mul_of_nonneg_left (h.holds q k) (show 0≤ (1+δ)^n*(c*b^j) by positivity)).trans_eq (by ring)
  symm; rw [show marked j _ x y=_ from hZ t]; change g t*w t = ∑ i,K i t
  rw [ink.token f (hg.rise (Nat.mul_le_mul_left _ hj)) (image (k:=2*k) _ (fun H=> by have h':=h.poles q; rw [H,abs_zero] at h'; norm_num at h')) h.full.1, sum_mul]; apply sum_congr rfl; intro i _; unfold K; ring
end YM.FullVolume.Ray.Fold
