import YM.Planned.STATIONARY_JET_PORT.Measured
import YM.Planned.STATIONARY_JET_PORT.Moment
import YM.Progress.STATIONARY_SCENES.Response



set_option warningAsError false

/-!
# Playing in the actual matching and Green function coordinates

E.g. estimate the existing plane wave tests with the real FDeriv directions
in the type (arbitrary finite arity, may repeat the same color or momentum).
Conversion to real derivative at these x and x=0 explicit. ℋ slots in the
matrix packs analogous. Volume here is in COARSE sites. Factor L^4 is not
lost inadvertently going from fine- to coarse-site costs (we sum externally;
the fixed-L factors needed at intermediate fine sites were ALREADY absorbed
in Before). Even compare across the older `Response.source` API.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.JetPort
open Push Push.Uniform Filter Function Set Metric Lattice Matrix RG Precision Tree Bid
open Progress.StationaryScenes Progress.StationaryScenes.Green
open scoped Topology ContDiff BigOperators Classical ComplexConjugate Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {c f : Side} {S : StepData c f} {B : Forest S.ratio}

lemma lights (i : Primary c G) : tint G _ (bolt i)=Response.source i := by
  funext j; ext k
  obtain ⟨i,l⟩ := i
  change bolt _ (j,k)=((Pi.single i (EuclideanSpace.basisFun G.ColorIndex ℝ l)) : In G c) j k
  by_cases h : j=i
  · subst j; simp only [Pi.single_eq_same, EuclideanSpace.basisFun_apply]; simp [bolt,Pi.single_apply]
  rw [Pi.single_eq_of_ne h]; simp [bolt,h]





section Generic
variable {ι τ E : Type} [Fintype ι] [Fintype τ] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : Positions (ι × G.ColorIndex)}

/-- Arbitrary evaluator in the old coordinates, without an analytic assumption
on the target phrasing (derive from the port). -/
lemma swallow {u : (ι → G.Color) → E} (h : ContDiffAt ℝ ω (u ∘ tint G ι) x) (k : ℕ) (v : Fin k → (ι → G.Color)) :
    iteratedFDeriv ℝ k u (tint G ι x) v =
      iteratedFDeriv ℝ k (u ∘ tint G ι) x (fun i => (tint G ι).symm (v i)) := by
  let L := tint G ι; let F := u ∘ L
  have hh : ContDiffAt ℝ ω F (L.symm (L x)) := by rwa [ContinuousLinearEquiv.symm_apply_apply]
  have he := iter_lin_at (L:=L.symm.toContinuousLinearMap) (k:=k) (f:=F) (x:=L x) (hh.of_le le_top)
  have hA : F ∘ L.symm.toContinuousLinearMap=u := funext fun y => by
    change u (L (L.symm y))=_; rw [L.apply_symm_apply]
  rw [hA] at he
  change iteratedFDeriv ℝ k u (L x) v = _; rw [he]
  change iteratedFDeriv ℝ k F (L.symm (L x)) _ = _; rw [L.symm_apply_apply]; rfl

lemma upright {u : (ι → G.Color) → E} (h : ContDiffAt ℝ ω (u ∘ tint G ι) x) :
    ContDiffAt ℝ ω u (tint G _ x) := by
  let L := tint G ι
  have he : ContDiffAt ℝ ω (u ∘ L) (L.symm (L x)) := by rw [L.symm_apply_apply]; exact h
  have ht := he.comp (L x) L.symm.contDiff.contDiffAt; have hu : (u ∘ L ∘ L.symm) = u := by
    ext; simp
  change ContDiffAt ℝ ω (u ∘ L ∘ L.symm) (L x) at ht; rwa [hu] at ht
end Generic

/-- charge normalized by Binder *coarse* volume. `cost` no volume. -/
def reception (G : Gauge) (K k : ℕ) (a C : ℝ) := (1+(Fintype.card (Exterior.TypeFace 1 × G.ColorIndex):ℝ)) * C * rollCall (a/2) K k
lemma reception_pos {K k : ℕ} {a C : ℝ} (ha : 0<a) (hc : 0<C) : 0<reception G K k a C :=
  mul_pos (mul_pos (by positivity) hc) (roll_pos (half_pos ha) K k)


lemma packed_vol (G : Gauge) (c : Side) : (Fintype.card (Primary c G):ℝ) ≤
    (Fintype.card (Site c):ℝ)*(1+(Fintype.card (Exterior.TypeFace 1 × G.ColorIndex):ℝ)) := by
  change (Fintype.card ((Site c × _) × _):ℝ) ≤ _
  rw [Fintype.card_prod,Fintype.card_prod,Fintype.card_prod]; push_cast
  rw [mul_add,mul_assoc]; exact le_add_of_nonneg_left (by positivity)

/-- Size bound including wave/box directions. A real-domain fderiv invoice
for every positive order (zero treated separately via Taylor difference if
wanted: no absolute score or det claim at order zero!). Not an α theorem or
period-error statement. -/
def Busy {n : Side} (l : Primary c G → Site n) (K N : ℕ) (a C : ℝ) (F : In G c → ℝ) (x : In G c) :=
    ContDiffAt ℝ ω F x ∧ 0<a ∧ 0<C ∧
    Scatter l a N (F ∘ tint G _) ((tint G _).symm x) C ∧
    ∀ k : ℕ, k ≠ 0 → k ≤ N → ∀ v : Fin k → In G c,
      |iteratedFDeriv ℝ k F x v| ≤ (Fintype.card (Site c):ℝ) * reception G K k a C * ∏ i, ‖(tint G _).symm (v i)‖

variable {K N k : ℕ} {a C : ℝ} {x : Positions (Primary c G)} {u : In G c → ℝ}

lemma ampere {l : Primary c G → Site f} (h : Multiplicity l K) (ht : Scatter l a N (u ∘ tint G _) x C)
    (hu : ContDiffAt ℝ ω (u ∘ tint G _) x) (ha : 0 < a) (hc : 0 < C) : Busy l K N a C u (tint G _ x) := by
  refine ⟨upright hu,ha,hc, (show _ by rw [(tint G _).symm_apply_apply]; exact ht),fun k hk hv v => ?_⟩
  rw [swallow hu]
  apply (invoice ht hc.le ha h hv ⟨0,Nat.pos_of_ne_zero hk⟩ _).trans
  refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
  unfold reception
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (packed_vol G c) hc.le)
    (roll_pos (half_pos ha) _ _).le).trans_eq (by ring)



-- absolute response read, physical basis and WDirections (old classical and thermal)



-- In external positions can also use their native rate, scaled with L
-- (possibly much smaller than a adequate C_J for recursion!). This uses the
-- ACTUAL root convention, includes wraps; not a strip estimate. Conservative
-- keep `a` on external positions as well, see positivity prices of `a`
-- itself (also saves exponential costs from increasing the rate).



-- Usage with actual AnalyticInput. Additional adapters to Calendar later.
variable {p : Clip} {R : PathData G} {Q : KernelChoices} {μ Λ : ℝ} {Y : ChartPrices}
    {O : ChartRatio G} {D : FiberFee O (N+1)} {Z : ℝ} {g : In G c → AxisChart G B}



-- locate Key of caisson; in TRUE parameter u space. Spending explicitly.


end YM.Planned.JetPort
