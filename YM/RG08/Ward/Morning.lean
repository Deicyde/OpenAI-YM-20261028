import YM.RG08.Ward.Far
/-! # Limit *in the stencil norm*, hence fallout in the family of Ward identities.
Beacon persists, including scalar coefficient (common curtains). Does not assert bulk=false physical Ward. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Reflect
open Filter MeasureTheory
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent FreeResolvent Profiles Finset Next.Free
open PertExtension.Series.Tested PertExtension.Series.Radial Matrix
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {c f m d n : Side} {G : Gauge} {r : ℕ} {u X : Type}
section charge
variable {V : ℕ→Shale X r} {F : Shale X r} [Fintype X]
theorem recital_weight {w A : ℝ} (h : Glow F w A) (hp : 0 ≤ w) : ‖recital F m‖ ≤ Fintype.card (Site m) * A := by
  have he : 0≤A:= h.nonneg
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity); intro x
  have hf:=h.summable (ling_one hp)
  let k: Beads X r→ ℝ := fun i=> ling w i*‖F i‖
  let C := ∏ i,‖x i‖; have hx:0≤C:= by unfold C; positivity
  rw [recital_eval _ hf]
  refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=> A*C) (fun i _=> (norm_tsum_le_tsum_norm (bead_summable _ _ hf i|>.norm)).trans ?_)).trans_eq ?_)
  · refine (Summable.tsum_le_tsum (g:=fun j=> k j * C) ?_ (bead_summable _ x hf i|>.norm) (h.2.1.mul_right C)).trans ?_
    · intro j; rw [norm_mul]; exact mul_le_mul (le_mul_of_one_le_left (norm_nonneg _) (ling_one hp j)) (rosary_bill ..) (norm_nonneg _) (h.1 _)
    rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right h.2.2 hx
  simp [C,mul_assoc]
lemma recital_waning (h : Mending V F) (m) : Tendsto (fun i=> recital (V i) m) atTop (𝓝 (recital F m)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr; have hm:= h.2; obtain ⟨w,δ,hp,H,hB⟩:= hm
  refine squeeze_zero (fun i=> norm_nonneg _) (g:=fun i=> ↑(Fintype.card (Site m)) * δ i) (fun i=> ?_) (by simpa using! H.const_mul (↑(Fintype.card (Site m)):ℝ))
  rw [← recital_sub (h.ever i|>.summable) h.1.summable m]; exact recital_weight (hB i) hp.le
variable {p : ℝ→ PAC X m} {c : ℝ→ℝ}
def appeal (p : ℝ→ PAC X m) (c : ℝ→ℝ)(h : ContDiffAt ℝ ∞ p 0) (he : ContDiffAt ℝ ∞ c 0) (j : ℕ) : (Tensor.T (PAC X m) ℝ r)→L[ℝ] ℝ := LinearMap.toContinuousLinearMap {
  toFun x:= ink (fun t=> c t*Tensor.diagonal x (p t)) j
  map_add' := fun x y=> by
    let P (x : Tensor.T (PAC X m) ℝ r) := fun t=> c t* Tensor.diagonal x (p t)
    have hP x : ContDiffAt ℝ ∞ (P x) 0 := he.mul ((Tensor.diag_smooth x ∞).contDiffAt.comp _ h) -- order?
    change ink (P (x+y)) j= _
    rw [show P (x+y)=P x+P y from funext fun i=> mul_add (c i) _ _, ink_add (hP x) (hP y)]; rfl
  map_smul' := fun t x=> by
    have hp : ContDiffAt ℝ ∞ (fun t=> c t*Tensor.diagonal x (p t)) 0 := he.mul ((Tensor.diag_smooth x ∞).contDiffAt.comp _ h)
    rw [show (fun i=> c i*Tensor.diagonal (t • x) (p i))= t • (fun i=> c i*Tensor.diagonal x (p i)) from funext fun i=>mul_left_comm (c i) t _, ink_c t hp]; rfl }
lemma seals (c : ℝ→ℝ)(hs : ContDiffAt ℝ ∞ c 0)(h : Mending V F) (hp : ContDiffAt ℝ ∞ p 0) (j) :
    Tendsto (fun i=> ink (fun t=> c t*stanza (V i) m (p t)) j) atTop (𝓝 (ink (fun t=> c t*stanza F m (p t)) j)) :=
  ((appeal p c hp hs j (r:=r)).continuous.continuousAt.tendsto).comp (recital_waning h _)
end charge
variable {F : Air G} {V : ℕ → Air G} (Q P : Pot G 2)
-- allow variable P_i
variable (R : ℕ → Pot G 2)
lemma obliging (v : ℝ→Link G n) (h : AnalyticAt ℝ v 0) (p : Air G) (Q : Pot G 2)(k) : ContDiffAt ℝ ∞ (fun t=> oblige Q p k t (v t)) 0 := (
    ((stanza_smooth Q n).contDiffAt.comp _ h.contDiffAt).add (ContDiffAt.sum (f:=fun i t=> t^i * grand (i+2) (p i) n (v t)) (s:=range (k+1)) (fun i _=> (contDiffAt_id.pow _).mul ((opus_whole (p i) (i+2) n).smooth.contDiffAt.comp _ h.contDiffAt)))).of_le le_top
lemma appeals (h : ∀ i j, Mending (fun p=> V p i j) (F i j)) (H : Mending R P) (v : ℝ→Link G n) (hp : AnalyticAt ℝ v 0) (k j) :
    Tendsto (fun i=>ink (fun t=> oblige (R i) (V i) k t (v t)) j) atTop (𝓝 (ink (fun t=> oblige P F k t (v t)) j)) := by
  let p (A : Air G)(i l : ℕ):= fun t:ℝ=> t^i * stanza (A i l) n (v t)
  have hh A i l : ContDiffAt ℝ ∞ (p A i l) 0 := (contDiffAt_id.pow _).mul (((stanza_smooth ..).contDiffAt.comp _ hp.contDiffAt).of_le le_top)
  have ht (A : Air G)(X : Pot G 2) : ink (fun t=> oblige X A k t (v t)) j= ink (stanza X n∘v) j + ∑ i∈ range (k+1),∑ l∈range (i+2+1), ink (p A i l) j := by
    have hu : ∀ i, ContDiffAt ℝ ∞ (fun t=>∑ l∈range (i+2+1),p A i l t) 0 := fun i=> ContDiffAt.sum (fun _ _=> hh A i _)
    rw [show (fun t=> oblige X A k t (v t))=(stanza X n ∘ v)+(fun t=> ∑ i∈ range (k+1),∑ l∈range (i+2+1),p A i l t) from funext fun t=> by unfold oblige grand; simp [Finset.sum_apply, Finset.mul_sum,p],ink_add (((stanza_smooth ..).contDiffAt.comp _ hp.contDiffAt).of_le le_top) (ContDiffAt.sum (fun i _=> hu i))];
    rw [Pi.add_apply, ink_list (range (k+1)) (fun i t=>∑ l∈range (i+2+1),p A i l t) (fun i _=> hu i)]; simp_rw [ink_list _ (p A _) (fun i _=> hh A _ i)]
  simp_rw [ht]
  refine Tendsto.add ?_ (tendsto_finsetSum (x:=atTop (α:=ℕ)) _ (fun i _=> tendsto_finsetSum (s:=range (i+2+1)) (fun l _=> ?_)))
  · simpa only [one_mul] using! seals (fun _=>(1:ℝ)) contDiffAt_const H (hp.contDiffAt.of_le le_top) j
  exact seals _ (contDiffAt_id.pow i) (h i l) (hp.contDiffAt.of_le le_top) j
lemma fashions (h : ∀ i j, Mending (fun p=> V p i j) (F i j)) (H : Mending R P) (n : Side) (he : ∀ i, Beacon n (V i) (R i)) : Beacon n F P := by
  intro i v w hv hw hx; refine pulse_bound (fun j hj=> ?_) (obliging v hv _ _ _) (obliging w hw _ _ _)
  exact tendsto_nhds_unique_of_eventuallyEq (appeals P R h H v hv i j) (appeals P R h H w hw i j) (Eventually.of_forall (fun k=> aspiredV (he k i v w hv hw hx) (ink_aspire (obliging v hv _ _ _)) (ink_aspire (obliging w hw _ _ _)) (Nat.le_of_lt_succ (mem_range.mp hj))))
end YM.RG08.Reflect
