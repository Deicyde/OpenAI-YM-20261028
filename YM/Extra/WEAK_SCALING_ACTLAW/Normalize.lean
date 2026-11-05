import YM.Extra.WEAK_SCALING_ACTLAW.Jets

/-!
# Normalization and stress limit on the very same weak coordinates

The finite-dimensional Maxwell line calculation and the physically nontrivial
centered choice of IR stress are exposed inputs. NOT consequences assumed in
`Pre`. Positive scales normalize the full coefficient tensor; its normalized
vacuum entry is zero no matter how small xi gets. No lower bound for xi. A
sign subsequence may be necessary -- one sign on cofinal demands suffices,
and flipping the Lighthouse flips kappa **with** its J even in the actual
translation/angular laws.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.WeakScaling
open Function Set Filter Table Ward Org Climb
open scoped Topology ContDiff
variable {G : Gauge} {L : Register G} {S : Table L}

def flip (T : Lighthouse L) : Lighthouse L := { T with κ := -T.κ, hκ := neg_ne_zero.mpr T.hκ, J := -T.J }

private noncomputable local instance : AddCommGroup (Ward.SpinRows S) := by
  letI : ∀ d, AddCommGroup (Ortho.Skew→ₗ[ℝ] (S.Field d →ₗ[ℂ] S.Field d)) := fun d => by infer_instance
  infer_instance

lemma laws_neg (H : S.Hierarchy) {J : S.Stress} {p : Parts S} {Y : SpinRows S} (h : StressLaws S J p Y) :
    StressLaws S (-J) (-p) (-Y) := by
  refine ⟨fun {_ _} hx q {_} w b d B => ?_, fun {_ _} hx q {_} w g d B => ?_⟩
  · rw [← Work.A15.translationFlux_apply hx w H.smooth, map_neg,Work.A15.translationFlux_apply,
      h.translation hx q w, ← Work.A15.front_apply, ← Work.A15.front_apply,Pi.neg_apply,Pi.neg_apply,
      LinearMap.neg_apply,map_neg]
  have he : ((-Y) d g B) = -(Y d g B) := rfl
  rw [← Work.A15.angularFlux_apply hx w H.smooth,map_neg,Work.A15.angularFlux_apply,
    h.rotation hx q w, ← Work.A15.front_apply, ← Work.A15.front_apply, he,map_neg]

lemma goes_flip (H : (Bel L).Hierarchy) {T : Lighthouse L} (h : T.Goes L H.spin) : (flip T).Goes L H.spin := by
  refine { h with delta := ?_ }
  change StressLaws (Bel L) (-T.J) ((-T.κ) • T.W.deriv) ((-T.κ) • T.K.lie)
  rw [show (-T.κ) • T.W.deriv = -(T.κ • T.W.deriv) from neg_smul (M:=Parts (Bel L)) T.κ (T.W.deriv : Parts (Bel L)), neg_smul]; exact laws_neg H h.delta

variable {C : Family G}
def negative (W : MaxwellData C) : MaxwellData C := { W with T := flip W.T, lit := goes_flip W.hT W.lit }

def Centered (J : S.Stress) := ∀ a b, Work.A15.front (n:=0) 0 Fin.elim0 4 (J a b) = 0

/-- Identifies the free mean-zero conserved H tensor line on the exact free
quotient (requires a choice of Lighthouse with corresponding normalization,
not just any object with angular Ward identities). No physical hypothesis
in this test; see Criteria for simpler finite inputs. -/
def Line (T : Lighthouse L) (h : (Bel L).RealSpin) := ∀ P : (Bel L).Stress, Conserved T.W h P →
    RawTensor h P → Centered P → ∃ c : ℝ, P = c • T.J

lemma downwards {P : ℕ → Prop} (hp : ∀ᶠ i : ℕ in atTop, P i) {r : ℕ → ℝ} (hr : ∀ i, 0 < r i)
    (he : Tendsto r atTop (𝓝 0)) : ∃ s : ℕ → ℕ, StrictMono s ∧ StrictAnti (r ∘ s) ∧ ∀ i, P (s i) := by
  choose t ht hf h using fun i => ((eventually_gt_atTop i).and (hp.and (he.eventually (gt_mem_nhds (hr i))))).exists
  obtain ⟨z,hz⟩ := hp.exists
  let s : ℕ → ℕ := Nat.rec z fun _ i => t i
  refine ⟨s,strictMono_nat_of_lt_succ (fun n => ht _),strictAnti_nat_of_succ_lt (fun n => h _),?_⟩
  intro i; cases i with
  | zero => exact hz
  | succ i => exact hf _

namespace Curve
variable {S : Table C.book} {V : DiffPlan S} {T : Lighthouse C.book}
variable {h : S.RealSpin} {H : (Free C).RealSpin} {M D N m d : ℕ} {Q R : ℝ} (b : Curve V T.W h H M D Q)

/-- Unweighted weak coordinates before positive normalization. -/
def pull (J : S.Stress) (k : ℕ) : (Free C).Stress := fun a c => (b.X k 4).symm (J a c)
lemma pull_norm {J : S.Stress} (hJ : J ≠ 0) (k : ℕ) : 0 < ‖b.pull J k‖ := by
  apply norm_pos_iff.mpr
  intro e
  exact hJ (funext fun a => funext fun c => (b.X k 4).symm.injective ((congrFun (congrFun e a) c).trans (map_zero _).symm))

def micro (J : S.Stress) (k : ℕ) : (Free C).Stress := ‖b.pull J k‖⁻¹ • b.pull J k
lemma micro_norm {J : S.Stress} (hJ : J ≠ 0) (k : ℕ) : ‖b.micro J k‖ = 1 := by
  rw [micro,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (b.pull_norm hJ k)), inv_mul_cancel₀ (b.pull_norm hJ k).ne']

lemma micro_eval (J : S.Stress) (k a c) : b.X k 4 (b.micro J k a c) = (‖b.pull J k‖⁻¹:ℝ) • J a c := by
  dsimp only [micro,pull,Pi.smul_apply]
  simp [RCLike.real_smul_eq_coe_smul (K:=ℂ)]

private lemma converges_on {j : ℕ → (Free C).Stress} {z} (h : Tendsto j atTop (𝓝 z)) (a c : Axis) :
    Tendsto (fun k => j k a c) atTop (𝓝 (z a c)) := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h a) c

lemma survives (hQ : 0 < Q) (hd : 4 < D) (hn : 1 ≤ M) (hS : S.Hierarchy) (hV : V.Derivatives S) {J : S.Stress}
    (hv : Conserved V h J) (hw : RawTensor h J) (hz : Centered J) {σ : ℕ → ℕ} (hs : Tendsto σ atTop atTop)
    {j : (Free C).Stress} (he : Tendsto (b.micro J ∘ σ) atTop (𝓝 j)) : Conserved T.W H j ∧ RawTensor H j ∧ Centered j := by
  have hc (a c) : Tendsto (fun k => b.micro J (σ k) a c) atTop (𝓝 (j a c)) := converges_on he a c
  have hg := hs.eventually b.graded
  refine ⟨⟨fun a c => tendsto_nhds_unique (f:=fun k => b.micro J (σ k) c a) ?_ (hc c a), fun a c => ?_, fun c => ?_⟩,
    fun g a c => ?_, fun a c => ?_⟩
  · exact (hc a c).congr' (Eventually.of_forall fun k => (b.X (σ k) 4).injective (by rw [micro_eval,micro_eval,hv.symmetric a c]))
  · have ht := ((YM.Spin.cont_conj H 4).tendsto _).comp (hc a c)
    apply tendsto_nhds_unique (ht.congr' ?_) (hc a c)
    filter_upwards [hg] with k hk
    apply (b.X (σ k) 4).injective
    change b.X _ 4 ((Free C).conj H 4 _) = _
    have hh v : b.X (σ k) 4 ((Free C).conj H 4 v) = S.conj h 4 (b.X (σ k) 4 v) := (hk.1 4 hd.le).2.1 v
    rw [hh,b.micro_eval,RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smulₛₗ,RCLike.conj_ofReal,hv.real]
  · let F (k : ℕ) (a : Axis) := (b.X k 5).symm.toLinearMap.comp ((b.r k • V.deriv 4 a).comp (b.X k 4).toLinearMap)
    have hi (a : Axis) := Dash.arcing ((Dash.fit_plane (fun k => F k a) (T.W.deriv 4 a) (b.deriv 4 hd a)).comp hs) (hc a c)
    apply tendsto_nhds_unique ((tendsto_finsetSum Finset.univ (fun a _ => hi a)).congr' ?_) tendsto_const_nhds
    refine Eventually.of_forall fun k => (b.X (σ k) 5).injective ?_
    have hterm (a : Axis) (k) : b.X k 5 (F k a (b.micro J k a c)) = (b.r k*‖b.pull J k‖⁻¹ : ℝ) • V.deriv 4 a (J a c) := by
      simp only [F, LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,b.micro_eval,LinearMap.smul_apply,
        RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul,RCLike.ofReal_mul,mul_smul]; exact smul_comm ..
    change b.X _ 5 (∑ a, F _ a _) = b.X _ 5 0
    rw [_root_.map_sum,map_zero]; simp_rw [hterm,← Finset.smul_sum,hv.divergence,smul_zero]
  · let l (i j : Axis) := ((g.matrix i a * g.matrix j c : ℝ) : ℂ)
    have ht := (((Free C).mirror H 4 g).continuous_of_finiteDimensional.tendsto _).comp (hc a c)
    apply tendsto_nhds_unique (ht.congr' ?_) (tendsto_finsetSum Finset.univ (fun i _ => tendsto_finsetSum Finset.univ
      (fun j _ => (hc i j).const_smul (l i j))))
    filter_upwards [hg] with k hk
    have hh v : b.X (σ k) 4 ((Free C).mirror H 4 g v) = S.mirror h 4 g (b.X (σ k) 4 v) := (hk.1 4 hd.le).1 g v
    apply (b.X (σ k) 4).injective
    change b.X _ 4 ((Free C).mirror H 4 g _) = b.X _ 4 (∑ i, ∑ j, l i j • _)
    simp_rw [hh,_root_.map_sum,map_smul,b.micro_eval,RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul,hw g a c, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => smul_comm ..
  have ht := b.mixture (v := fun _ : Fin 1 => (⟨4,j a c⟩ : (Free C).Tag)) (w:=fun k _ => ⟨4,b.micro J (σ k) a c⟩)
    (x:=0) hS hV hQ hn (fun _ => ⟨4,le_rfl,_,_,hc a c,rfl,fun _ => rfl⟩) hd hs
    (show 0 ∈ apart Q 1 from ⟨by simpa,fun i j hij => False.elim (hij (Subsingleton.elim _ _))⟩) tendsto_const_nhds
  have hh (z : (Free C).Field 4) : (fun _ : Fin 1 => (⟨4,z⟩ : (Free C).Tag)) = Fin.cons ⟨4,z⟩ Fin.elim0 :=
    funext (Fin.cases rfl (fun i => i.elim0))
  rw [hh] at ht
  rw [Work.A15.front_apply]
  refine tendsto_nhds_unique (ht.congr' ?_) tendsto_const_nhds
  refine Eventually.of_forall fun k => ?_
  let v := b.micro J (σ k) a c
  have he : routed (forgetting b.X) (σ k) ∘ (fun _ : Fin 1 => (⟨4,v⟩ : (Free C).Tag)) = Fin.cons
      (⟨4,b.X (σ k) 4 v⟩ : S.Tag) Fin.elim0 := funext (Fin.cases rfl (fun i => i.elim0))
  change disc _ (b.r _ • (0 : Points 1)) = 0
  rw [he,disc,smul_zero, ← Work.A15.front_apply,b.micro_eval]
  simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul,hz a c,smul_zero]

lemma tracks (hr : 1 ≤ R) (hQ : R < Q) (hn : N ≤ M) (hd : d + m < D) (h₄ : 4 < D)
    (hS : S.Hierarchy) (hV : V.Derivatives S) (hH : (Free C).Hierarchy) (hW : T.W.Derivatives (Free C))
    {J : S.Stress} (hJ : J ≠ 0) {σ : ℕ → ℕ} (hs : Tendsto σ atTop atTop) {c : ℝ}
    (hpos : 0 < c) (he : Tendsto (b.micro J ∘ σ) atTop (𝓝 (c • T.J))) :
    ∃ X, Track X V T J h H N d m R := by
  obtain ⟨u,hu,ha,hp⟩ := downwards (hs.eventually b.graded) (fun i => b.pos (σ i)) (b.shrinks.comp hs)
  let s := σ ∘ u
  have ht : Tendsto s atTop atTop := hs.comp hu.tendsto_atTop
  let t k := b.r (s k)
  have hw k := b.pull_norm hJ k
  let X : Scaling S := ⟨b.X ∘ s, fun k => c*‖b.pull J (s k)‖*(t k)^4,t,fun k => by
      have hr := b.pos (s k); have := hw (s k); dsimp only [t]; positivity, fun k => b.pos _,ha,b.shrinks.comp ht⟩
  refine ⟨X,⟨⟨fun k e hb => ⟨((hp k).1 e (by omega)).1,((hp k).1 e (by omega)).2.1⟩,
    fun k e hb => ((hp k).1 e (by omega)).2.2,fun k i e h h' v => (hp k).2 i e h (by omega) v⟩,
    fun n hy j hj v hv ε hε => ht.eventually (b.tested hS hV hH hW hr hQ (hy.trans hn) v hv j (by omega) ε hε),
    fun i j => ?_⟩⟩
  have hi := (converges_on (he.comp hu.tendsto_atTop) i j).const_smul (c⁻¹ : ℝ)
  change Tendsto _ _ (𝓝 ((c⁻¹:ℝ) • c • T.J i j)) at hi
  rw [inv_smul_smul₀ hpos.ne'] at hi
  apply hi.congr
  intro k
  change (c⁻¹:ℝ) • b.micro J (s k) i j = (b.X (s k) 4).symm ((↑((_ : ℝ) * (t k)^4) : ℂ) • J i j)
  have hr : t k ≠ 0 := (b.pos _).ne'
  rw [map_smul,show (c*‖b.pull J (s k)‖*t k^4)⁻¹*t k^4 = c⁻¹*‖b.pull J (s k)‖⁻¹ by field_simp]
  exact (mul_smul (c⁻¹:ℝ) ‖b.pull J (s k)‖⁻¹ _).symm.trans (RCLike.real_smul_eq_coe_smul (K:=ℂ) _ _)

private def turn : Curve V (flip T).W h H M D Q := b
include b in
lemma choose_track (hr : 1 ≤ R) (hQ : R < Q) (hn : max N 1 ≤ M) (hd : max d 4 + m < D)
    (hS : S.Hierarchy) (hV : V.Derivatives S) (hH : (Free C).Hierarchy) (hW : T.W.Derivatives (Free C))
    {J : S.Stress} (hJ : J ≠ 0) (hv : Conserved V h J) (hw : RawTensor h J) (hz : Centered J)
    (hl : Line T H) : (∃ X, Track X V T J h H N d m R) ∨ (∃ X, Track X V (flip T) J h H N d m R) := by
  haveI : ProperSpace ((Free C).Stress) := FiniteDimensional.proper ℂ _
  obtain ⟨z,-,σ,hs,ht⟩ := (isCompact_closedBall (0 : (Free C).Stress) 1).tendsto_subseq
    (fun k => show b.micro J k ∈ Metric.closedBall _ _ by simp [b.micro_norm hJ k])
  have he : ‖z‖ = 1 := tendsto_nhds_unique ht.norm (by simp only [comp_apply, b.micro_norm hJ]; exact tendsto_const_nhds)
  obtain ⟨h₁,h₂,h₃⟩ := b.survives (by linarith) (by omega) (by omega) hS hV hv hw hz hs.tendsto_atTop ht
  obtain ⟨c,rfl⟩ := hl _ h₁ h₂ h₃
  have h : c ≠ 0 := by rintro rfl; simp at he
  rcases h.lt_or_gt with h | h
  · have hh : c • T.J = (-c) • (flip T).J := by simp [flip]
    exact Or.inr (b.turn.tracks (T:=flip T) hr hQ (by omega) (by omega) (by omega) hS hV hH hW hJ hs.tendsto_atTop (by linarith : 0 < -c) (hh ▸ ht))
  exact Or.inl (b.tracks hr hQ (by omega) (by omega) (by omega) hS hV hH hW hJ hs.tendsto_atTop h ht)
end Curve
end YM.Extra.WeakScaling
