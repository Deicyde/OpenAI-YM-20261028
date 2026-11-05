import YM.Pert.Rig.Tiles
/-! Joint moving quadrature criterion for compact tests off bad sets. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
set_option maxRecDepth 3000
namespace YM.Pert.Rig

open Maxwell Lattice Extraction Set MeasureTheory Function Filter Full Topology Next.Rank.Radian Metric
variable {r : ℕ} {A : Type*}
structure Motion where
  side : ℕ → Side
  denom : ℕ → Side
  t : ℕ → ℝ
  positive : ∀m,0<t m
  exch : ∀m,t m=((denom m).val:ℝ)⁻¹
  shrinks : Tendsto t atTop (𝓝 0)
  available : Tendsto (fun i=>t i * ((side i).val:ℝ)) atTop atTop

def Motion.reindex (m : Motion) (i : ℕ→ℕ) (hi:Tendsto i atTop atTop) : Motion := ⟨m.side ∘ i,m.denom ∘ i,m.t ∘i,fun j=>m.positive (i j), fun j=>m.exch (i j),m.shrinks.comp hi,m.available.comp hi⟩

variable (m : Motion) (y : ℕ→ Points r)
def plot (i:ℕ) := place (m.side i) (address (m.t i) (y i))
def spot (i:ℕ) := tag (m.t i) (address (m.t i) (y i))
variable {m y}
lemma spot_limit (m : Motion) {y : ℕ→Points r} {z : Points r} (hy : Tendsto y atTop (𝓝 z)) : Tendsto (spot m y) atTop (𝓝 z) := by
  rw [tendsto_iff_dist_tendsto_zero] at hy ⊢
  have he i : dist (spot m y i) (y i) ≤ (4*r:ℝ)*m.t i := approximate (m.positive i) (y i)
  apply squeeze_zero (fun _=> @dist_nonneg (Points r) _ _ z) (fun j : ℕ => (dist_triangle (spot m y j) (y j) z).trans (add_le_add_left (he j) (dist (y j) z)))
  simpa only [mul_zero,zero_add] using ((m.shrinks.const_mul ((4*r):ℝ)).add hy)
lemma available_rule (m : Motion) (R : ℕ) : ∀ᶠ i in atTop, 2 * (R*(m.denom i).val) < (m.side i).val := by
  filter_upwards [m.available.eventually (eventually_gt_atTop (2*(R:ℝ)))] with i he
  have hp : (0:ℝ)<(m.denom i).val := by exact_mod_cast (m.denom i).pos
  rw [m.exch,←div_eq_inv_mul] at he
  have he:=lt_of_lt_of_le he le_rfl; apply lt_div_iff₀ hp |>.1 at he
  exact_mod_cast (mul_assoc (2:ℝ) .. ▸ he) -- careful orientation
lemma spot_emb (m : Motion) {y : ℕ→Points r} {z : Points r} (hy : Tendsto y atTop (𝓝 z)) : ∀ᶠ i in atTop, embedding (m.t i) ((plot m y) i) = (spot m y) i := by
  let R:=Nat.ceil ‖z‖+1
  have hR : ‖z‖ < R := by push_cast; exact lt_of_le_of_lt (Nat.le_ceil _) (by unfold R;push_cast; exact lt_add_one _) -- type cast issues
  filter_upwards [available_rule m R,(spot_limit m hy).norm.eventually (gt_mem_nhds hR)] with i he hn
  rw [plot,spot,tent_eq _ R (tent_valid _ (by rw [←m.exch]; exact hn.le)) he] -- hn on spot, spot=i concrete

variable (m) (K : ∀i,Grid (m.side i) r → ℂ) (f : Points r→ℂ)
variable {z : Points r}
def F (i:ℕ) (x:Points r) := f x * K i (place (m.side i) (address (m.t i) x))
def chosen (i:ℕ) (x:Points r) := F m K f i (tag (m.t i) (address (m.t i) x))
variable {ω : Set (Points r)} {G : Points r→ℂ}
-- Joint property along cofinal subsequences, to avoid arbitrary selection of lattice fibers.
def Arrives (ω : Set (Points r)) (G : Points r→ℂ) : Prop := ∀ (σ : ℕ→ℕ), Tendsto σ atTop atTop → ∀ z : Points r, z∈ω → ∀ o:∀i,Grid (m.side (σ i)) r,
 Tendsto (fun j=>embedding (m.t (σ j)) (o j)) atTop (𝓝 z) → Tendsto (fun j=>K (σ j) (o j)) atTop (𝓝 (G z))
-- binder G ambiguous
lemma chosen_limit (H : Arrives m K ω G) (h : Continuous f) (hω : tsupport f ⊆ ω) (x : Points r) :
    Tendsto (fun i=>chosen m K f i x) atTop (𝓝 (f x*G x)) := by
  let y (_:ℕ) := x
  have hy : Tendsto y atTop (𝓝 x) := tendsto_const_nhds
  have he := spot_limit m hy
  have htab : ∀ i, chosen m K f i x = f (spot m y i) * K i ((plot m y) i) := by
    intro i; dsimp only [chosen,F,spot,plot,y]; rw [center_eq _ (m.positive _).ne']
  by_cases hx:x∈tsupport f
  · have hj := H id tendsto_id x (hω hx) (plot m y) (he.congr' ((spot_emb m hy).mono (fun _ h=>h.symm)))
    simp_rw [htab]; exact ((h.continuousAt.tendsto.comp he).mul hj)
  rw [image_eq_zero_of_notMem_tsupport hx,zero_mul] -- name
  apply (@tendsto_const_nhds _ _ _ (0:ℂ) atTop).congr' -- args
  filter_upwards [he.eventually ((isClosed_tsupport f).isOpen_compl.mem_nhds hx)] with j hh
  rw [htab, image_eq_zero_of_notMem_tsupport hh,zero_mul]

lemma bounded_fee (hc : HasCompactSupport f) (hω : tsupport f ⊆ ω) (H : Arrives m K ω G) : ∃ C : ℝ,0≤C ∧ ∀ᶠ i in atTop, ∀ x:Points r,x∈tsupport f → ‖K i ((plot m (fun _ => x)) i)‖ ≤ C := by
  classical
  by_contra! he
  have hchoose (i : ℕ) : ∃ n≥i,∃ x:Points r,x∈tsupport f ∧ (i:ℝ) < ‖K n ((plot m (fun _=>x)) n)‖ := by
    have hf := he (i:ℝ) (by positivity)
    exact frequently_atTop.1 hf i -- shape
  choose n hge x hx h using hchoose
  obtain ⟨z,hz,σ,hσ,Hσ⟩ := ((hc : IsCompact (tsupport f)).isSeqCompact hx)
  let a:=n ∘ σ
  have ht := hσ.tendsto_atTop
  have ha : Tendsto a atTop atTop := (tendsto_atTop_mono (f:=id) hge tendsto_id).comp ht
  let y:=x ∘ σ
  let m' := m.reindex a ha
  let O := plot m' y
  have hb := H a ha z (hω hz) O (by change Tendsto (fun i=> embedding (m'.t i) (O i)) atTop (𝓝 _) ; apply (spot_limit m' Hσ).congr' ((spot_emb m' Hσ).mono (fun _ h=>h.symm)))
  have hd := hb.norm.eventually (gt_mem_nhds (lt_add_one ‖G z‖))
  obtain ⟨i,hi,hu⟩ := (hd.and ((tendsto_natCast_atTop_atTop.comp ht).eventually (eventually_ge_atTop (‖G z‖ + 2)))).exists
  have hf : (σ i :ℝ)<‖K (a i) (O i)‖ := h (σ i)
  linarith only [hi, (show ‖G z‖+2≤ (σ i : ℝ) from hu),hf]

end YM.Pert.Rig
