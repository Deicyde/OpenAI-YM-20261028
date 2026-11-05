import YM.RG08.Flat.Chain
import YM.Next.STATIONARY.Films.RankColor

/-!
# Post-block read from pre-block inversion strip on the repeated section

Keep coarse strip unchanged until spending fixed analytic-to-Width budget.
A qualitative tile cost after L is fine, provided it is assigned as a delay
cost on the schedule. It is *not* included among diagonal transfer factors.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open Function Filter Finset Laurent Lattice RG Exterior Precision Bloch Matrix
open Stationary
open scoped Topology BigOperators

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {G : Gauge} {c L : Side}

omit [Fintype α] [DecidableEq α] in
/-- Single-period probes separate matrices even when using the alias zero. -/
lemma jaunt_same {M N : CircM c α β} {F H : Momentum→CompM α β}
    (h : Jaunt M F 0) (hk : Jaunt N H 0)
    (hp : ∀ p : Site c,F (mon p)=H (mon p)) : M=N := by
  apply cancel_rotation c
  ext x ⟨p,b⟩
  have hh : (fun i : Co c β => rotations c β i (p,b))=tune p (Pi.single b 1) :=
    funext fun i => coef_wave ..
  have he : M*ᵥ tune p (Pi.single b 1)=N*ᵥ tune p (Pi.single b 1) := by
    rw [h p _ (rolls.refl _), hk p _ (rolls.refl _),hp]
  have hh : M*ᵥ _=N*ᵥ _ := hh ▸ he
  rw [Matrix.mul_apply, Matrix.mul_apply]
  exact congr_fun hh x

lemma dollars_continuous (α : Type) [Fintype α] [DecidableEq α] (L : Side) :
    Continuous (altarTile L α).tile := by
  have hg : Continuous ground := by unfold ground axes; fun_prop
  have hh : Continuous shadeK := by
    unfold shadeK slug Exterior.q
    fun_prop
  have hp : Continuous (fun p : Momentum => spice L α p) := continuous_pi fun i => by
    unfold spice
    apply Continuous.inv₀
    · unfold hill pebWeight aliasAt
      fun_prop
    exact fun _ => by exact_mod_cast (hill_pos ..).ne'
  exact Continuous.matrix_mul ((continuous_matrix fun i j => continuous_iff_continuousAt.mpr
    (fun p : Momentum => ((tile_lit (L:=L) (α:=α) p i j)).continuousAt)).matrix_mul
        hp.matrix_diagonal) continuous_const

lemma booth_continuous (G : Gauge) (L : Side) : Continuous (slabW G L).tile := by
  apply continuous_matrix
  intro i j; cases i <;> cases j <;> first
  | exact (dollars_continuous _ _).matrix_elem _ _
  | exact continuous_const

lemma unpin (X : Slab α) (hx : Continuous X.tile) {η : ℝ} (hs : 0<η) :
    ∃ M : ℝ, 0≤M ∧ ∀ F : Momentum→CompM α α,
      Poster η F → ∀ C : ℝ, 0 ≤ C → Freezer X.dual X F η C →
      ∀ p∈ strip η, vflux (F p)⁻¹ ≤ M*C := by
  let K := Metric.closedBall (0:Momentum) (Real.pi+η)
  have hK : IsCompact K := isCompact_closedBall ..
  have hu : Continuous (fun p => vflux (X.tile p)) := by
    open scoped Matrix.Norms.L2Operator in
    exact Continuous.norm hx
  obtain ⟨d,h⟩ := hK.exists_bound_of_continuousOn hu.continuousOn
  let D := max 0 d; have hD : 0≤D := le_max_left ..
  have ht {p : Momentum} (hk : p ∈ K) : vflux (X.tile p) ≤ D :=
    (le_trans (le_abs_self _) (h _ hk)).trans (le_max_right ..)
  refine ⟨D*D,mul_nonneg hD hD,fun F hp C hC hf q hq => ?_⟩
  obtain ⟨p,hp',hr⟩ := Nave.roll q
  have hhP : p ∈ strip η := by
    -- real shift
    obtain ⟨x,rfl⟩ := hr
    intro i
    have he := hq i
    simpa [reciprocal] using he
  have hk : p∈K := by
    rw [Metric.mem_closedBall,dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ Real.pi+η)).2 fun i => ?_
    calc
      _ ≤ |(p i).re| + |(p i).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ _ := add_le_add (hp' i) (hhP i).le
  have hn : -p ∈ K := by simpa [K] using hk
  rw [← hp.shifts hr hhP]
  let Y := (F p)⁻¹
  let Z := carryM X X.dual p p Y
  have hz : Y=X.tile p * Z * (X.dual.tile p)⁻¹ := by
    unfold Z carryM; simp only [Matrix.mul_assoc]
    rw [mul_nonsing_inv (X.dual.tile p) (X.dual.whole _),mul_one,
      ← Matrix.mul_assoc,Matrix.mul_nonsing_inv _ (X.whole p), Matrix.one_mul]
  change vflux Y≤_
  conv_lhs => rw [hz]
  apply le_trans (flux_power ..)
  rw [Slab.inverse_dual,back_flux]
  apply (mul_le_mul ((flux_power ..).trans (mul_le_mul (ht hk) (hf.price p hhP)
    (flux_nonneg _) hD)) (ht hn) (flux_nonneg _) (mul_nonneg hD hC)).trans_eq
  ring

/-- `Freezer` pays a real inverse `Row` with WHOLE period agreement. Consume
    the width after fixing it uniformly as in `Stationary.post_cert`.
    Constants may depend on X (hence P/L), NOT on F, nor on period m. -/
lemma freezer_row (X : Slab α) (hx : Continuous X.tile) {η C : ℝ}
    (hs : 0 < η) (hC : 0 ≤ C) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ F : Momentum → CompM α α, Poster η F →
      Freezer X.dual X F η C → (∀ p, star p=p → (F (-p))ᵀ=(F p)ᴴ) →
      ∃ B : Row α α, B.strip (η/4) M ∧ ∀ (m : Side) (U : Matrix (Co m α) (Co m α) ℝ),
        Jaunt (approached U) F 0 → U*B.acts m=1 := by
  obtain ⟨K,hK,Hk⟩ := unpin X hx hs
  let w := η/4
  have hw : 0<w := by unfold w; positivity
  have ha : w+w<η := by unfold w; linarith
  let M := (K*C)*(2*((1+w)/w))^(Fintype.card Axis)
  refine ⟨M,by unfold M; positivity, fun F hp hf h => ?_⟩
  let A (p : Momentum) := (F p)⁻¹
  have hr i j : Firm η (K*C) (fun p => A p i j) := by
    refine ⟨⟨hs,fun p hv => ?_, fun p hv y => ?_⟩,fun p hv =>
      (flux_tilt ..).trans (Hk F hp C hC hf p hv)⟩
    · exact BillD.take (hp.shape hv) (hf.period p hv) i j
    unfold A; rw [show F p=F (p+reciprocal y) from hp.shifts (show rolls p (p+reciprocal y) from ⟨_,rfl⟩) hv]
  let R (x y : α) := Laurent.market (fun p => A p x y) 0
  have hR x y : Width w M (R x y) := (hr x y).1.issues (hr x y).2 w w hw.le hw ha
  let B : Row α α := fun i j x => (R i j x).re
  have hB : B.strip w M := fun i j => Work.F07.widthRealPart (hR i j)
  have hu (p : Momentum) (hh : star p=p) : B.read p=A p := by
    have hd : (A (-p))ᵀ=(A p)ᴴ := by
      unfold A; rw [Matrix.transpose_nonsing_inv, Matrix.conjTranspose_nonsing_inv,h p hh]
    ext i j
    have he : star (A (-p) i j)=A p i j := by rw [show A (-p) i j=star (A p i j) from congr_fun (congr_fun hd j) i,star_star]
    unfold B; rw [Row.read,Matrix.of_apply,Work.F07.readRealPart (hR i j) hw hh]; unfold R
    rw [(hr i j).1.paints (hr i j).2 p (Work.F07.realStrip _ hs hh),
      (hr i j).1.paints (hr i j).2 _ (Work.F07.realStrip _ hs (p:=-p) (by rw [star_neg,hh])),he]
    ring
  refine ⟨B,hB,fun m U ht => ?_⟩
  apply prom_inj; rw [prom_mul, prom_one']
  refine jaunt_same (ht.hoist (Jaunt.row B (Row.rights _ _ hB hw.le))) Jaunt.noop (fun p => ?_)
  have hq : star (mon p) = mon p := real_frequency p
  rw [hu _ hq]; exact Matrix.mul_nonsing_inv _ (hf.period _ (Work.F07.realStrip _ hs hq))

end YM.RG08
