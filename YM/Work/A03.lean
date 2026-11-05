import YM.Bid.Angular

/-!
# All positional jets of the transverse-component vector Ward tests

We work with mixed-cap words. We only need to pad to a single cap when
invoking the order-zero test (LineSum); all differentiations can then use
mixed caps. No line-sum identity for `p` is assumed at off-line
configurations near our point.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Work.A03
open Set Function Filter Bid Table Climb Ward Analysis
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius NNReal InnerProductSpace

variable {G : Gauge} {L : Register G} {S : Table L} {n : ℕ}

private def tick (p : Parts S) (j : Axis) (B : S.Tag) : S.Tag :=
  ⟨B.1+1, p B.1 j B.2⟩

/-- `diagram v (leaves p d j)`, but allowing different caps in the slots. -/
private def row (p : Parts S) (j : Axis) (q : Fin n → S.Tag) (x : Points n) : ℂ :=
  ∑ i, disc (update q i (tick p j (q i))) x

/-- Raising any ONE cap preserves the mixed-cap test (on conf). At the
marked slot this uses both `p`'s compatibility and the inclusion kernel
identity at the raised-by-one degrees. -/
private lemma row_raise_one (h : S.Hierarchy) (W : DiffPlan S) (inc : W.Inclusions S)
    (p : Parts S) (c : ColorLaw p W h.spin) {d e : ℕ} (hd : d ≤ e)
    (j : Axis) (q : Fin n → S.Tag) {x : Points n} (hx : x ∈ conf _)
    (k : Fin n) (B : S.Field d) :
    row p j (update q k ⟨e, W.rise hd B⟩) x = row p j (update q k ⟨d, B⟩) x := by
  unfold row
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hik : i = k
  · subst i
    simp only [update_self, update_idem]
    change disc (update q k ⟨e+1,p e j (W.rise hd B)⟩) x =
      disc (update q k ⟨d+1,p d j B⟩) x
    rw [c.incl d e hd]
    exact W.inclusion_slot inc h.laws.toSymmetric (Nat.succ_le_succ hd) hx k q (p d j B)
  simp only [update_of_ne hik]
  rw [update_comm (Ne.symm hik), update_comm (Ne.symm hik)]
  exact W.inclusion_slot inc h.laws.toSymmetric hd hx k _ B

/-- Extend LineSum itself to mixed caps, still with unrestricted labels. -/
private lemma all_line (h : S.Hierarchy) (W : DiffPlan S) (inc : W.Inclusions S)
    (p : Parts S) (c : ColorLaw p W h.spin) (hl : LineSum p)
    (b j : Axis) (hj : j ≠ b) (q : Fin n → S.Tag)
    {x : Points n} (hx : x ∈ conf _) (ht : onLine b x) : row p j q x = 0 := by
  classical
  let d := Finset.univ.sup fun i : Fin n => (q i).1
  have hd (i : Fin n) : (q i).1 ≤ d := Finset.le_sup (f := fun i => (q i).1) (Finset.mem_univ i)
  let v : Fin n → S.Field d := fun i => W.rise (hd i) (q i).2
  let F (s : Finset (Fin n)) (i : Fin n) := if i ∈ s then column v i else q i
  have boost (s : Finset (Fin n)) : row p j (F s) x = row p j q x := by
    induction s using Finset.induction_on with
    | empty => simp [F]
    | @insert k s hk ih =>
      have hu : F (insert k s) = update (F s) k (column v k) := by
        funext i
        by_cases hik : i = k
        · subst i; simp [F]
        simp [F,hik]
      have he : update (F s) k (q k) = F s := by
        funext i
        by_cases hik : i = k
        · subst i; simp [F,hk]
        simp [hik]
      rw [← ih, hu]
      calc
        _ = row p j (update (F s) k (q k)) x :=
          row_raise_one h W inc p c (hd k) j (F s) hx k (q k).2
        _ = row p j (F s) x := by rw [he]
  rw [← boost Finset.univ, show F Finset.univ = column v by simp [F]]
  exact hl d n b j hj v x hx ht

/-- Differentiate the test before any restriction to a line. -/
private lemma row_D (h : S.Hierarchy) (W : DiffPlan S) (der : W.Derivatives S)
    (p : Parts S)
    (delta : ∀ d b i u, W.deriv (d+1) b (p d i u) = p (d+1) i (W.deriv d b u))
    (j : Axis) (q : Fin n → S.Tag) {x : Points n} (hx : x ∈ conf _) (k : Fin n) (a : Axis) :
    D (Points.direction k a) (row p j q) x = row p j (update q k (rise W a (q k))) x := by
  have hd (i : Fin n) : DifferentiableAt ℝ (disc (update q i (tick p j (q i)))) x :=
    (cont_disc h _ hx).differentiableAt (by simp)
  unfold row D
  rw [fderiv_fun_sum (fun i _ => hd i), _root_.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  change D (Points.direction k a) (disc (update q i (tick p j (q i)))) x = _
  rw [fromD W h der hx]
  by_cases hik : i = k
  · subst i
    simp only [update_self, update_idem]
    have htag (B : S.Tag) : rise W a (tick p j B) = tick p j (rise W a B) := by
      rcases B with ⟨d,u⟩
      exact congr_arg (fun z : S.Field ((d+1)+1) => (⟨_,z⟩ : S.Tag)) (delta d a j u)
    rw [htag]
  rw [update_of_ne (Ne.symm hik), update_of_ne hik, update_comm hik]

private lemma expand_pts (u : Points n) :
    (∑ i : Fin n, ∑ a : Axis, u i a • Points.direction i a) = u := by
  apply WithLp.ofLp_injective 2
  funext k
  simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply,
    Points.direction, PiLp.ofLp_single, Pi.single_apply]
  rw [Finset.sum_eq_single k]
  · apply WithLp.ofLp_injective 2
    funext b
    simp [basis, Pi.single_apply]
  · intro i hi hik
    simp [Ne.symm hik]
  · simp

/-- `W.deriv` itself satisfies LineSum just by translation invariance
(indeed the line and component restrictions aren't needed here). -/
private lemma line_native (h : S.Hierarchy) (W : DiffPlan S) (der : W.Derivatives S) :
    LineSum W.deriv := by
  intro d n b j hj v x hx ht
  let q := column v
  let u := points fun _ : Fin n => basis j
  have hu : (∑ i : Fin n, Points.direction i j) = u := by
    simpa [u] using expand_pts u
  let F (t : ℝ) := x+t • u
  have hr : F 0 = x := by simp [F]
  have hh : HasDerivAt F u 0 := by
    have he := (ContinuousLinearMap.toSpanSingleton ℝ u).hasDerivAt (x := 0)
    simpa [F] using he.const_add x
  have he : (disc q ∘ F) = fun (_ : ℝ) => disc q x := by
    funext t
    exact h.translations n x hx (t • basis j) (fun i => ⟨(q i).1,S.representative _ (q i).2⟩)
  have hd : DifferentiableAt ℝ (disc q) (F 0) := by
    rw [hr]
    exact (cont_disc h q hx).differentiableAt (by simp)
  have hz : fderiv ℝ (disc q) x u = 0 := by
    have hp := hd.hasFDerivAt.comp_hasDerivAt 0 hh
    rw [he,hr] at hp
    exact hp.unique (hasDerivAt_const _ _)
  change row W.deriv j q x = 0
  rw [← hz, ← hu, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact (fromD W h der hx i j q).symm

/-- Iteration at the point. Use the germ of `row_D` (valid nearby in
`conf`, not a LineSum statement there), snoc convention for the last
direction, and linearity to reach every positional tensor component. -/
private lemma full_jet (h : S.Hierarchy) (W : DiffPlan S)
    (inc : W.Inclusions S) (der : W.Derivatives S)
    (p : Parts S) (c : ColorLaw p W h.spin)
    (delta : ∀ d b i u, W.deriv (d+1) b (p d i u) = p (d+1) i (W.deriv d b u))
    (hl : LineSum p)
    (b j : Axis) (hj : j ≠ b)
    {x : Points n} (hx : x ∈ conf _) (ht : onLine b x)
    (q : Fin n → S.Tag) (m : ℕ) (u : Fin m → Points n) :
    iteratedFDeriv ℝ m (row p j q) x u = 0 := by
  induction m generalizing q with
  | zero =>
    simpa using all_line h W inc p c hl b j hj q hx ht
  | succ m ih =>
    have hr : ContDiffAt ℝ ∞ (row p j q) x := by
      apply ContDiffAt.sum
      exact fun i _ => cont_disc h _ hx
    have hh : ContDiffAt ℝ (↑(m+1 : ℕ)) (row p j q) x :=
      hr.of_le (show ((↑(m+1 : ℕ)) : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
    let v := Fin.init u
    let g : Points n →L[ℝ] ℂ := (iteratedFDeriv ℝ (m+1) (row p j q) x).curryRight v
    have hb (k : Fin n) (a : Axis) : g (Points.direction k a) = 0 := by
      change iteratedFDeriv ℝ (m+1) (row p j q) x (Fin.snoc v (Points.direction k a)) = 0
      have hp :
          D (Points.direction k a) (row p j q) =ᶠ[𝓝 x] row p j (update q k (rise W a (q k))) := by
        filter_upwards [(conf_open _).mem_nhds hx] with y hy
        exact row_D h W der p delta j q hy k a
      rw [snoc_jet hh, (hp.iteratedFDeriv ℝ m).eq_of_nhds]
      exact ih _ _
    have ha (w : Points n) : g w = 0 := by
      rw [← expand_pts w, map_sum]
      simp [map_sum,hb]
    have hy := ha (u (Fin.last m))
    change iteratedFDeriv ℝ (m+1) (row p j q) x
      (Fin.snoc (Fin.init u) (u (Fin.last m))) = 0 at hy
    rwa [Fin.snoc_init_self] at hy

private lemma all_scenes (h : S.Hierarchy) (W : DiffPlan S)
    (inc : W.Inclusions S) (der : W.Derivatives S)
    (p : Parts S) (c : ColorLaw p W h.spin)
    (delta : ∀ d b i u, W.deriv (d+1) b (p d i u) = p (d+1) i (W.deriv d b u))
    (hl : LineSum p) : Climb.transverse p := by
  intro d s
  exact full_jet h W inc der p c delta hl s.a s.b s.offAxis s.strict
    s.positions (column s.v) s.m s.dirs

theorem answer : YM.Bid.A03 := by
  intro G L S h W inc der o p Y c hc hl
  refine ⟨all_scenes h W inc der p c hc.delta hl, ?_⟩
  exact all_scenes h W inc der W.deriv (native W h inc der o)
    (fun _ b i u => W.abelian h.laws.toSymmetric der h.smooth u b i)
    (line_native h W der)

end YM.Work.A03
