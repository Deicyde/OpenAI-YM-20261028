import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import YM.Next.BOUNDARY.Coordinates
import YM.Next.ROTATIONS.Response
import YM.Next.SCHEDULE.Blocks
import YM.Next.UV_STRESS.Across
import YM.Push.BETA_TRANSPORT.Comparisons
import YM.Push.COMMON_WITNESSES.Link
import YM.Push.CUTOFF_PROJECTORS.Along
import YM.Push.PRICE_COMPILER.Suppression

set_option warningAsError false

/-!
# Ancestors and mirrors of true shell nodes

Here using the shifted site chambers of `NodeBound`.

In the linked interval
below cutoff, follow *actual* parents.

In particular all terms in each
allowed selection remain separated (the two names at zero are alternatives)
even for arbitrarily fine grid presentations of the node.

This is not a
covariance assumption on labelled presentations or a license to replace the
field arguments by parent roots when evaluating at the cutoff.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.Annulus
open Function Set Filter MeasureTheory Analysis Extraction Table Ward Lattice Wilson Overlay Marker Cells RG
open Next.UVStress
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {S : Schedule} {v c m k N p r d : ℕ}

section mirror
variable {n f t : Side} (q : Ratio n f)

lemma embed_comp (b : Ratio t n) (z : Ratio t f) (x : Site t) : q.embed (b.embed x)=z.embed x := by
  rw [Ratio.embed,b.lift_embed,smul_smul,← Work.B15.count_trans q b z]; rfl



lemma embed_location (q : Ratio (S.side m p) (S.side k p)) (h : r ≤ m) (hk : m ≤ k) (x : Cover) :
    q.embed (location S r m p x) = location S r k p x := by
  rw [location,dif_pos h, location,dif_pos (h.trans hk),embed_comp]

variable (hv : v+1≤m) (h : m ≤ k) (q : Ratio (S.side m p) (S.side k p))

lemma embed_bias (i : Site (S.side v p)) :
    q.embed ((terrace S v hv p).bias i)=(terrace S v (hv.trans h) p).bias i := by
  let B : Cover := fun j => if ((terrace S v hv p).omega i).flip j then 1 else 0
  have he {t : ℕ} (h : v+1≤t) : (terrace S v h p).bias i = location S v t p B := by
    rw [location,dif_pos ((Nat.le_succ v).trans h),Ratio.embed_wrap]; ext1 j
    let T := terrace S v h p
    change T.bias i j = (((T.side.val • B : Cover) j : ℤ) : Per (S.side t p))
    change (if (T.omega i).flip j then (T.side.val : Per _)-(Kind.site.shift:Per _) else 0)=_
    change _=((T.side.val • (if (T.omega i).flip j then (1:ℤ) else 0) : ℤ) : Per (S.side t p))
    split <;> simp [Kind.shift]
  rw [he hv,he (hv.trans h), embed_location q ((Nat.le_succ v).trans hv) h]

lemma embed_mirror (i : Site (S.side v p)) :
    q.embed ((terrace S v hv p).translateBy i)=(terrace S v (hv.trans h) p).translateBy i := by
  unfold Tiling.translateBy Tiling.starts
  simp only [← q.root_embed,map_add,map_sub]; simp only [Ratio.root_embed]
  rw [q.signed, embed_comp q (terrace S v hv p).units (terrace S v (hv.trans h) p).units,embed_bias hv h q,
    base_coarse S v hv, base_coarse S v (hv.trans h), embed_location q hv h]; rfl



lemma center_spaced (i j : Site (S.side v p)) (hi : i≠j) :
    let T := terrace S v hv p
    Cells.span S hv p ≤ separation (T.copyMap i 0) (T.copyMap j 0) := by
  let g := S.toDepth hv p; let Z := terrace S v (N:=v+1) le_rfl p
  have hx (i) : g.embed (Z.copyMap i 0) = (terrace S v hv p).copyMap i 0 := by
    simp only [Tiling.copyMap,affine,Signed.act_zero,zero_add]; exact embed_mirror _ hv g i
  have hZ : 0 ∈ Z.chamber 0 := by
    have hh := buffered S v (N:=v+1) le_rfl p 0; rw [location_origin,map_zero] at hh; exact hh.1
  have he : Z.copyMap i 0 ≠ Z.copyMap j 0 := fun h => hi <|
    (Z.which_chamber (Z.enumerate i hZ)).symm.trans ((congr_arg Z.which h).trans (Z.which_chamber (Z.enumerate j hZ)))
  have hz : 1 ≤ separation (Z.copyMap i 0) (Z.copyMap j 0) :=
    Nat.pos_of_ne_zero fun e => he ((Corona.line_home ..).symm.trans (Corona.line_end _ _ e.le))
  dsimp only; rw [← hx,← hx]
  exact (le_mul_of_one_le_right (Nat.zero_le _) hz).trans (Corona.below g _ _)
end mirror



























private lemma hat_deep (hG : G.Simple) (a : Levels G) : Tendsto a.clock.hatBeta atTop atTop :=
  tendsto_atTop_add_const_left _ _ (a.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos hG))

lemma opens_radius (hG : G.Simple) (a : Levels G) {s b : ℝ} (hs : 1 ≤ s) (hb : 0 < b) : ∀ᶠ k in atTop,
    16*s*(a.clock.coverSize k:ℝ)^2 ≤ a.clock.monitor k ^ b := by
  have hx := Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp (hat_deep hG a))
  filter_upwards [(hx.const_mul_atTop hb).eventually_ge_atTop (4+64*s), hx.eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp (hat_deep hG a)).eventually_ge_atTop 1] with k hk hk' hL
  let y := Real.log (a.clock.hatBeta k)
  change 1 ≤ y at hL; change 1 ≤ Real.log y at hk'; change 4+64*s ≤ b * Real.log y at hk
  have he : 64*s+4*Real.log y ≤ (Real.log y)^2*b := by nlinarith [mul_le_mul_of_nonneg_right hk (by linarith : 0≤Real.log y)]
  have hB : (a.clock.coverSize k:ℝ) ≤ 2*y^2 := (Nat.ceil_lt_add_one (sq_nonneg y)).le.trans (by nlinarith)
  calc
    _ ≤ 16*s*(2*y^2)^2 := by gcongr
    _ = (64*s)*y^4 := by ring
    _ ≤ Real.exp (64*s)*y^4 := mul_le_mul_of_nonneg_right
      (by linarith only [Real.add_one_le_exp (64*s)]) (by positivity)
    _ ≤ Real.exp ((Real.log y)^2 * b) := by
        nth_rw 1 [show y^4=Real.exp ((4:ℕ)*Real.log y) from (Real.exp_nat_mul ..).symm ▸ by rw [Real.exp_log (by positivity : 0<y)]]
        rw [← Real.exp_add]; apply Real.exp_monotone; exact he
    _ = _ := Real.exp_mul ..





lemma cover_grows (hG : G.Simple) (a : Levels G) : Tendsto a.clock.coverSize atTop atTop :=
  tendsto_nat_ceil_atTop.comp ((tendsto_pow_atTop (by decide : (2:ℕ)≠0)).comp (Real.tendsto_log_atTop.comp (hat_deep hG a)))



def Spacing (C : Family G) (v ℓ : ℕ) (s : ℝ) : Prop :=
    v+1≤ℓ ∧ ∀ (m p : ℕ), ℓ ≤ m → ∀ (h : v+1 ≤ m), 8 ≤ (C.path.levels.budget m).B ∧
      let T := terrace C.S v h p
      ∀ i j : T.Cell, i≠j → s*(C.path.levels.budget m).B^2 ≤ (separation (T.copyMap i 0) (T.copyMap j 0) : ℝ)

lemma spacing_late (hG : G.Simple) (v : ℕ) {s : ℝ} (hs : 0≤s) (h : Stock.Tabs C.path.levels) : ∀ᶠ ℓ in atTop, Spacing C v ℓ s := by
  obtain ⟨ℓ₀,H,hV⟩ := Stock.Tabs.mayOpen _ s h (v+1)
  obtain ⟨f,hf⟩ := eventually_atTop.mp ((cover_grows hG C.path.levels).eventually_ge_atTop 8)
  filter_upwards [eventually_ge_atTop ℓ₀,eventually_ge_atTop f] with ℓ hℓ hF
  refine ⟨H.trans hℓ, fun m p hm hv => ⟨hf _ (hF.trans hm),fun i j hij => ?_⟩⟩
  apply le_trans ((Stock.Tabs.open_later _ s h ⟨H,hV⟩ (hℓ.trans hm) hs).2)
  exact div_bound hv i j hij
where
  div_bound {m p} (hv : v+1≤m) i j hij : C.S.a (v+1)/C.S.a m ≤ (separation ((terrace C.S v hv p).copyMap i 0)
      ((terrace C.S v hv p).copyMap j 0):ℝ) := by
    rw [← C.S.embeds_scale (C.S.toDepth hv p), mul_div_cancel_left₀ _ (C.S.a_pos _).ne']
    exact_mod_cast (center_spaced hv (S:=C.S) i j hij)
end YM.UVNext.Annulus
