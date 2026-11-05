import YM.Extra.MULTISOURCE_TRAJECTORIES.Capacity
import YM.Extra.MULTISOURCE_TRAJECTORIES.Price

/-!
# RMixed including birth, ancestor separation and post-birth costs

Larger opening and marker power requests available before making any cutoffs
or adjusting prices; transferred unmasked cumulant/attachment controls below N
remain real producer hypotheses. No eventual-all-period exchange of limits.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Trajectories
open RG Wilson Lattice Function Filter MeasureTheory Finset Overlay Mix Stock Marker Asymptotics
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge} {C : Family G}

lemma ticket_mono {w t : ℝ} {N p m i : ℕ} {h : m ≤ N} (H : ticket C t N p m i h) (hw : w≤t) : ticket C w N p m i h :=
    ⟨H.1,H.2.1,fun r hi hN x y hxy => (mul_le_mul_of_nonneg_left hw (sq_nonneg _)).trans (H.2.2 r hi hN x y hxy)⟩
lemma opens_mono {t w : ℝ} {a : Levels G} {j i : ℕ} (H : Tabs.opens a t i j) (hw : w ≤ t) : Tabs.opens a w i j :=
    ⟨H.1,(mul_le_mul_of_nonneg_right hw (sq_nonneg _)).trans H.2⟩

lemma toll_mono {V : Type*} [DecidableEq V] {R : Census V} (s : R.Mode) {w v : V → ℝ} (hw : ∀ i,0 ≤ w i) (he : w ≤ v) :
    Poly.toll w s ≤ Poly.toll v s := prod_le_prod (fun i _ => hw i) (fun i _ => he i)

lemma expenses_smaller {V : Type} [DecidableEq V] {R : Census V} {α : Type*} {n : Side} {P : Rep G n} {X : Layers P R α} {t w : ℝ}
    (h : X.Expenses t) (hw : 0 < w) (ht : w≤t) : X.Expenses w := by
  obtain ⟨hu,Q,⟨hd,hp,hc,γ,hγ,hf,hB,hG⟩,v,δ,ht',hQ⟩ := h
  refine ⟨fun i => (mul_le_mul_of_nonneg_right ht (norm_nonneg _)).trans (hu i),Q,
    ⟨hd,hw,fun i => budget_smaller (hc i) (fun j => ?_) (fun j => ?_) le_rfl,γ,hγ,hf,hB,fun x => ?_⟩,v,δ,ht.trans ht',hQ⟩
  · split
    · exact mul_nonneg (Poly.worth (fun _ => hw) _).le (mul_nonneg (Real.exp_pos _).le (Q.nonnegative _))
    rfl
  · split
    · exact mul_le_mul_of_nonneg_right (toll_mono _ (fun _ => hw.le) (fun _ => ht)) (mul_nonneg (Real.exp_pos _).le (Q.nonnegative _))
    rfl
  apply budget_smaller (hG x) (fun i => ?_) (fun i => ?_) le_rfl
  · split
    · exact mul_nonneg (Layers.rent_nn Q _ (fun i => hw) _ _) (Real.exp_pos _).le
    rfl
  split
  · refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    unfold Layers.rental; cases i
    · exact le_rfl
    next i _ =>
      dsimp only [Sum.elim_inr]; split
      · exact mul_le_mul_of_nonneg_right (toll_mono _ (fun _ => hw.le) (fun _ => ht)) (Q.basic_nn (Sum.inr i))
      rfl
  rfl

open Prices
lemma expensive_open (C : Family G) (hG : G.Simple) (w : ℝ) : ∃ t : ℝ, w ≤ t ∧ ∀ i j,
    Tabs.opens C.path.levels t i j → ∀ k,j ≤ k → 8 ≤ B C k := by
  obtain ⟨K,hK⟩ := eventually_atTop.mp ((diverge C hG).eventually_ge_atTop 8)
  let f (q : ℕ × ℕ) := (C.S.a q.1/C.S.a q.2) / ((B C q.2:ℝ)^2)
  obtain ⟨D,hD⟩ := (((Set.finite_le_nat K).prod (Set.finite_le_nat K)).image f).bddAbove
  refine ⟨max w (D+1),le_max_left ..,fun i j ht k hk => hK k ?_⟩
  by_contra! h'
  have hb := (C.path.levels.budget j).B_pos
  have he : (B C j:ℝ)^2 > 0 := by
    have := show (0:ℝ) < B C j by exact_mod_cast hb
    positivity
  have hv : max w (D+1) ≤ f (i,j) := (le_div_iff₀ he).mpr ht.2
  have H := ht.1.trans hk
  exact not_le_of_gt (lt_of_lt_of_le (lt_add_one D) (le_max_right ..)) (hv.trans (hD ⟨(i,j),⟨by exact H.trans h'.le,by exact hk.trans h'.le⟩,rfl⟩))

/-- One explicit (possibly too costly) price request AFTER birth. There are
no Active, representation/recursion, integrability, or limit conclusions in
the request. `layers` computes the mixed finite-cutoff Haar quantities in it.
-/
def After (C : Family G) (d : ℕ) (u : ℝ) := ∃ a t k, 0 < a ∧ (1:ℝ) ≤ t ∧ ∀ m i, C.ref d ≤ m → Tabs.opens C.path.levels t m i →
    ∀ᶠ N in atTop, ∀ (h : m ≤ N) (p), ticket C t N p m i h → ∀ v : C.label d, ‖v‖ ≤ u →
      ∀ j,i ≤ j → j < N → Aperture (C.path.rep N p j) ∧ ∃ W : Windows (C.side j p),
        ((Probes.center C p h v).layers (census _) W).Expenses (width C a k j)

theorem earned (H : C.Makes) (hG : G.Simple) {l d : ℕ} (hI : InitialRoom C l) {u : ℝ} (hu : 0≤u)
    (h : After C d u) : Offers C d u := by
  obtain ⟨a,w,k,ha,hw,h⟩ := h
  let k' := k+l+degree C d+2
  obtain ⟨t,ht,hT⟩ := expensive_open C hG w
  refine ⟨a,t,k',ha, hw.trans ht, fun m i hm hi => ?_⟩
  have he := opens_mono hi ht
  filter_upwards [initial_expenses C H hG ha hu (k:=k') (d:=d) (by unfold k'; omega) hI,h m i hm he,eventually_ge_atTop i] with N hN hS h₁
  refine ⟨hi.1.trans h₁,h₁,fun p hh v hv => ?_⟩
  have h₂ := hS (hi.1.trans h₁) p (ticket_mono hh ht) v hv
  let Q := Probes.center C p (hi.1.trans h₁) v
  have solve (j) : ∃ W : Windows (C.side j p),i ≤ j → j ≤ N → Aperture (C.path.rep N p j) ∧ 8 ≤ B C j ∧
      (Q.layers (census _) W).Expenses (width C a k' j) := by
    by_cases hj : i≤j ∧ j≤N
    swap; · exact ⟨Windows.whole _, fun h h' => (hj ⟨h,h'⟩).elim⟩
    rcases eq_or_lt_of_le hj.2 with h|h
    · subst j
      refine ⟨Windows.whole _,fun _ _ => ⟨(hN p).1,hT m i hi _ hj.1,(hN p).2 m i _ hj.1 (ticket_mono hh (hw.trans ht)) v hv _⟩⟩
    obtain ⟨hA,W,hW⟩ := h₂ j hj.1 h
    have hg := g_pos C j; have ht := envelope_pos C ha j
    refine ⟨W, fun _ _ => ⟨hA,hT m i hi _ hj.1,expenses_smaller hW (div_pos (pow_pos hg _) ht) (div_le_div_of_nonneg_right
      (pow_le_pow_of_le_one hg.le (g_one ..) (show k≤k' by unfold k'; omega)) ht.le)⟩⟩
  choose W hW using solve
  exact ⟨W,hW⟩
end YM.Extra.Trajectories
