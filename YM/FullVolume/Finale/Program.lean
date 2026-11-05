import YM.FullVolume.Finale.Atlas
import YM.FullVolume.Fields.Filled
import YM.FullVolume.Finale.Cycle
/-!
 # Full ultraviolet fixed periodic space and analytic tuning

 Parameter coordinate is affine `Contest.ask` (read
 scale `beamWidth`). Unit disks and their strict interiors use THIS parameter;
 `Face.Fan.Spending` includes a further nonzero dilation for correlations. The
 argument δ to `july` prescribes the penalty of the Wilson *kernel*,
 not a tuning parameter!

 `Winter` has the vacuum statements written in the completed weighted
 Show norm (same anchored regular E and forced K, one common list, all
 housing prices, not raw functions evaluated *off* their domains). And includes
 paths with the stated strict reserve. No v estimate in this norm: v cannot
 have a finite UV limit. Successful trial = Competes for the fixed recursion
 (all p,N prescription `T.L.tunes`). Only uniqueness within this recursion,
 up to padding beyond N; not uniqueness among all conceivable
 representations.

 `PositionsUV` is for the reference Wilson family (the SAME family as in
 Spec.Final). Includes all fixed orders separately. Every p in this construction
 is admitted; in particular for interpolation and normalized coordinate
 differences on compact subsets of NoHit, with through-one-higher bounds on
 that same p, all finite additional fixed differences too. For fields dᵢ take N
 sufficiently large, in particular ≥ each (common, cutoff independent)
 reference level. Big estimates are eventual and N can depend also on p, counts
 and labels, fixed comparison neighborhood separated on torus, fixed finite
 orders/stencils (e.g. normalized SBP), the one-higher derivatives under use,
 tests. No claim of fine estimates if any of these are allowed to drift. Test
 convention is that of Spec: `Test` and `suitable`. Thus compact support,
 smooth, separated, inside period; on the covering lift, *positional*
 statements can also use neighborhoods of the seams and projections may tie.
 At other real b on the local disks read **actual Wilson correlation** on
 Face.novel (not the aux Family), not at its ghost level-zero params. Anchored
 literal Based calibration on that actual history. Local scope only in b (for
 analytic correlations, both finite and limiting); no fixed width claim for
 arbitrary geometry near collisions or as period grows. Radii for a finite
 program can also address the one-higher orders, see Travel. Do not read
 cutoff correlations outside the paid compacts/cutoff thresholds from
 padded Beam terms. Parameter derivatives of the limiting kernels in the
 same affine units are part of the convergence asserted there as well.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Final
open Function Filter Set MeasureTheory Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open YM.PhysicalNext YM.PhysicalNext.Repeat YM.PhysicalNext.Repeat.Legato
open Campaign Campaign.Face RG.Shoot Pass Muse Contest Ovens
open Extraction Extraction.Lease FullVolume.Amp FullVolume.Amp.Beam FullVolume.Ray
variable {G : Gauge} {R : Run G} (T : Campaign R)

/-- Success for bare inverse coupling r with target b. Uses the chosen entire
recipe (also used to produce the witness for CLOSED). -/
def successful (p N : ℕ) (b r : ℝ) : Prop :=
  ∃ y : Trail R.alloy.B.a p, Competes T.L.tunes p N 0 y ∧ (y 0).beta = b ∧ (y N).beta = r

lemma wins (h : Winter T) (p N : ℕ) (s : sun) :
    ∃! β : ℝ, successful T p N (ask R.alloy.B.a s.val) β := by
  obtain ⟨Y,hy⟩ := h.beta p N s
  refine ⟨(Y.trail N).beta, ⟨Y.trail,Y.rises,hy,rfl⟩, ?_⟩
  intro b hb
  obtain ⟨y,hP,hY,rfl⟩ := hb
  have hx : (y 0).beta ∈ nearby R.alloy.B.a := hY.symm ▸ onLine T.gains s
  let Q : Contest N p T.L := ⟨y,hP,hx⟩
  exact congr_arg Rep.beta (h.unique _ _ Q Y (hY.trans hy.symm) _ le_rfl)

lemma bareTrial (h : Winter T) (p N : ℕ) :
    ∃ X : ℂ → ℂ, AnalyticOnNhd ℂ X (Metric.ball 0 1) ∧ ∀ (s : sun) (β : ℝ),
      successful T p N (ask R.alloy.B.a s.val) β → X (s.val : ℂ) = (β : ℂ) := by
  obtain ⟨F,H,X,Y,hx,h1,h2,hA,hP⟩ := h.analytic p N
  refine ⟨_, (hA N).1, fun s β hs => ?_⟩
  obtain ⟨y,hb,hq,h⟩ := hs
  let Q : Contest N p T.L := ⟨y,hb,hq.symm ▸ onLine T.gains s⟩
  exact (hx N s Q le_rfl hq).1.trans (congr_arg Complex.ofReal h)

variable {T} {W : Pillars R T}

/-- Varying real b over period index p. Same schedule, sections and basis.
Always interpret F at p. `novel` to use the actual (varying) b, not the
auxiliary histories used to transact calls within the source proofs. -/
structure Travel (p : ℕ) (F : Fan T W p) : Prop where
  milestones : (F.film Fan.nucleus |>.novel) = R.family
  active (N : ℕ) (s : sun) : Competes T.L.tunes p N 0 ((F.film s |>.novel).path.rep N p)
  flight (s : sun) (N : ℕ) : let Y := (F.film s |>.novel);
      (Y.path.rep N p 0).beta = R.family.path.levels.clock.bar
        + (F.spin.val*beamWidth R.alloy.B.a)*s.val
  price (s : sun) (d N : ℕ) : R.family.ref d ≤ N →
    ((F.film s |>.novel).factory d N p).Based R.family.params (R.family.localSection d) (R.family.ref d)
  roads (s : sun) (N m : ℕ) (hn : m < N) :
    R.alloy.B.Move N m p ((F.film s |>.novel).path.rep N p m) ((F.film s |>.novel).path.rep N p (m+1))
  lenses (s u : sun) (d N : ℕ) (Z : Campaign.Face T W) : R.family.ref d ≤ N →
      0 < u.val → u.val ≤ 1/4 →
      (Z.novel.path.rep N p 0).beta = ((F.film (scaleSun u s)).novel.path.rep N p 0).beta →
      Z.novel.O N p (d:=d) = (F.film (scaleSun u s) |>.novel).O N p (d:=d)
  payments (n : ℕ) (V : Fin n → R.family.book.Token) (K : Set (Points n)) (h : ℕ) :
    IsCompact K → K ⊆ NoHit R.family.S p n → Fan.Spending F V K (h+1)

lemma clients (H : T.Winter) (h' : Jams.Wild R.kit.shape R.alloy.delay)
    (Θ : Luna.Tableau T.width 300) (v : ℕ → ℕ → ℝ) (hk : Campaign.Sky R T Θ v) (p : ℕ) :
    ∃ F : Fan T W p, Travel p F := by
  obtain ⟨F,hF⟩ := Fan.buys (T:=T) (W:=W) (p:=p)
  refine ⟨F, ?_, fun N s => pricedR _, fun s N => ?_,
    fun s d N => liftoff _ d N p, fun s N m hn => movedR _ _ _ _ hn,
    fun s u d N Z h₁ h₂ h₃ h₄ => Face.radiation Z F hk d N h₁ s u h₂.le h₃ h₄.symm,
    fun n V K h hv hp => Fan.standing F V H h' hk hv hp⟩
  · rw [hF]; exact centralR
  have hz := price_arc F Amp.Beam.noon N s
  rw [unitP] at hz
  dsimp only at hz
  exact hz.trans (by rw [mul_one])

/-- The Ordered smear readings already hold with full mesh followed by the
same per subsequence. Not asserting CellHyp etc on that order. -/
lemma from_spec (f : Extraction.Order) {S : Table R.family.book} (hv : Nonempty (Spec.Final R.family f S))
    (hp : PositionsUV R.family Extraction.Sequence.full) :
    (Extraction.Order.mk Extraction.Sequence.full f.per).Ordered R.family S := by
  obtain ⟨F⟩ := hv
  refine ⟨fun n v t => ?_⟩
  obtain ⟨ht,D,hD,hV⟩ := F.room.ordered.reads n v t
  refine ⟨ht,D,fun p h => ?_,hV⟩
  obtain ⟨g,hg,h₁,h'⟩ := hp p n v
  have hx := h₁ t h
  exact tendsto_nhds_unique (hx.comp (f.mesh.cofinal)) (hD p h) ▸ hx

/-- One Run with center prescription, Campaign and geometry. Can also produce
an (old) Final and use UV limits for reading off its S. No change after extraction.

Dome = open unit disk in `bar + beamWidth*z` coordinates. Travel correlations
use smaller widths as specified there, independent of N. -/
structure Jewel (R : Run G) (T : Campaign R) (W : Pillars R T) : Prop where
  actual : R.family.Makes
  shape : ∃ Θ v, Campaign.Sky R T Θ v
  sampler : ∀ f : Extraction.Order, ∃ (g : Extraction.Order) (S : Table R.family.book),
    Nonempty (Spec.Final R.family (f.refine g) S) ∧
    (Extraction.Order.mk Extraction.Sequence.full (f.refine g).per).Ordered R.family S
  primary (p N : ℕ) : Competes T.L.tunes p N 0 (R.family.path.rep N p)
  acquires (p N : ℕ) : T.L.tunes.Issues N p
  curves : Winter T
  unique (p N : ℕ) (s : sun) : ∃! β, successful T p N (Contest.ask R.alloy.B.a s.val) β
  tuning (p N : ℕ) : ∃ X : ℂ → ℂ, AnalyticOnNhd ℂ X (Metric.ball 0 1) ∧
    ∀ (s : sun) (β : ℝ), successful T p N (ask R.alloy.B.a s.val) β → X (s.val : ℂ) = (β : ℂ)
  costs (m p : ℕ) : (∃ c : ℝ, 0 < c ∧ ∀ N ≥ m, c ≤ stripped R.family.path N p m) ∧
    Tendsto (fun N => (R.family.path.rep N p m).v) atTop atBot
  deployed : FixedBounds R.family
  fullMesh : PositionsUV R.family Extraction.Sequence.full
  serves (p : ℕ) : ∃ F : Fan T W p, Travel p F

/-- Public endpoint.

Every p in this schedule. -/
theorem july (h : G.Simple) (δ : ℝ) (hd : 0 < δ) : ∃ (R : Run G) (T : Campaign R) (W : Pillars R T),
    R.family.path.levels.clock.kernel.penalty = δ ∧ Jewel R T W := by
  obtain ⟨R,T,hC,hJ,⟨W⟩,hD,v,Θ,hk⟩ := Campaign.operaShip h δ hd
  have H := offers T hC hJ
  have hP := realUV H W hJ
  refine ⟨R,T,W,hD,R.makes,⟨Θ,v,hk⟩,fun f => ?_,fun p N => T.goes N p,
    fun N p => T.L.supplier h, H, wins T H, bareTrial T H,
    fun m p => ⟨saved R.makes.wilson m p, field_independent R.makes.wilson h m p⟩,
    genuine _ h, hP, clients H hJ Θ v hk⟩
  obtain ⟨g,S,hS⟩ := (R.again h).2 f
  exact ⟨g,S,hS,from_spec (f.refine g) hS hP⟩

-- Some API in the conventions of RG.Shoot, without Beam arguments.
namespace Jewel
variable {S : Jewel R T W}

/-- Issues actually gives *all* startup trials in the hatted intervals. -/
theorem lookup (S : Jewel R T W) (p N : ℕ) (b : ℝ) (hb : b ∈ band R.alloy.B.a N) :
    ∃! y, y ∈ {x | Lives T.L.tunes N N p x ∧
      x.beta = b ∧ T.L.tunes.Starter N p x} := by
  obtain ⟨F, _, h⟩ := (S.acquires p N).initial
  obtain ⟨hu,hv,hs⟩ := h b hb
  refine ⟨F b, ⟨hv, hu, hs⟩, ?_⟩
  intro y hy
  change _ ∧ _ ∧ _ at hy
  exact hy.2.2.inits.2.symm.trans ((congr_arg _ (hy.2.1.trans hu.symm)).trans hs.inits.2)

/-- No extra mesh-picking or tuning-dependent filter inside the intermediate
    bands: output from a priced input is always there, and determined. It may
    have stepped out of the bands. -/
theorem query (S : Jewel R T W) (p N m : ℕ) (hm : m < N)
    (U : Rep G (R.family.side (m+1) p))
    (hU : Lives T.L.tunes N (m+1) p U) (h : U.beta ∈ band R.alloy.B.a (m+1)) :
    ∃! V, V ∈ {x | Lives T.L.tunes N m p x ∧ T.L.tunes.Relays N m p x U} := by
  have he : Curve (R.alloy.B.a.budget (m+1)) (fun _ => U) (Icc 0 0) :=
    hU.point ▸ (Rain.unchanged U (Icc 0 0))
  obtain ⟨a, H, hv⟩ := (S.acquires p N).advances m hm _ _ le_rfl (fun _ => U) he (fun _ _ => ⟨hU,h⟩)
  have hs := hv 0 ⟨le_rfl, le_rfl⟩
  refine ⟨a 0, hs, fun y hy => ?_⟩
  change _ ∧ _ at hy
  obtain ⟨r,hY⟩ := hy.2.continues.2
  obtain ⟨r',hS⟩ := hs.2.continues.2
  exact (T.L.prim N m p r).sails_singleton hY hS

/-- For convenience, here is the bare trial in b units. -/
theorem b_units (S : Jewel R T W) :
    ∃ r : ℝ, 0 < r ∧ ∀ p N : ℕ, ∃ X : ℂ → ℂ,
      let b₀ := R.family.path.levels.clock.bar
      AnalyticOnNhd ℂ X (Metric.ball (b₀ : ℂ) r) ∧
      ∀ b ∈ Metric.ball b₀ r, (∃! β : ℝ, successful T p N b β) ∧
        ∀ β : ℝ, successful T p N b β → X (b : ℂ) = ↑β := by
  let w := Contest.beamWidth R.alloy.B.a
  let b := R.family.path.levels.clock.bar
  have hw : 0 < w := S.curves.width
  let f := fun z : ℂ => (z - b) / w
  have hf (z : ℂ) : AnalyticAt ℂ f z := by fun_prop
  refine ⟨w, hw, fun p N => ?_⟩
  obtain ⟨V, H, hv⟩ := S.tuning p N
  refine ⟨V ∘ f, ?_⟩
  refine ⟨fun z hz => (H (f z) ?_).comp (hf z), fun y hy => ?_⟩
  · rw [mem_ball_zero_iff]
    unfold f
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hw.le, div_lt_one hw]
    exact dist_eq_norm (E := ℂ) z ↑b ▸ Metric.mem_ball.mp hz
  rw [Metric.mem_ball, Real.dist_eq] at hy
  have ht : |(y-b)/w| ≤ 1 := by
    rw [abs_div,abs_of_pos hw,div_le_one hw]
    exact hy.le
  let s : sun := ⟨(y-b)/w, abs_le.mp ht⟩
  have hp : ask R.alloy.B.a s.val = y := calc
    _ = b+(y-b)/w*w := rfl
    _ = y := by field_simp; ring
  refine ⟨hp ▸ S.unique p N s, fun β hb => ?_⟩
  change V (f _) = _
  rw [show f (y : ℂ) = (s.val:ℂ) by simp [s,f] ]
  exact hv s β (hp.symm ▸ hb)
-- View the strong norm as a Cauchy statement in the baseline deviation test.
open Lark.Glide Filter UniformSpace Urns Finset Push.AbsoluteSums
section priced
variable {n : Side} {P : Urns.Price G n} (f g : Show P) {x : ℝ}

private lemma sum_cover {v : ℕ → ℝ} {V : ℕ → Site n → Prop}
    [DecidableRel V] (h : ∀ j, 0 ≤ v j)
    (hp : ∀ j, ∃ s, V j s) (hh : ∀ s : Site n, SumBudget (fun i => if V i s then v i else 0) x) :
    SumBudget v ((Fintype.card (Site n) : ℝ) * x) := by
  apply budget_of_sum h
  intro t
  let w i s := if V i s then v i else 0
  calc
    _ ≤ ∑ j ∈ t, ∑ s, w j s := Finset.sum_le_sum (fun i _ => by
      obtain ⟨s, hv⟩ := hp i
      apply (if_pos (α:=ℝ) (t:=v i) (e:=0) hv).symm.trans_le
      apply Finset.single_le_sum (f:=w i)
      · intro j _; unfold w; split
        · exact h i
        rfl
      exact Finset.mem_univ s)
    _ = ∑ s, ∑ j ∈ t, w j s := Finset.sum_comm
    _ ≤ ∑ _s : Site n, x := Finset.sum_le_sum (fun s _ => budget_sum (hh s) t)
    _ = _ := by rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

private lemma quote {ε : ℝ} (h : dist f g ≤ ε) : deviation P.p f.proper g.proper
      ((Fintype.card (Site n) : ℝ) * max (ε * P.b) (ε * P.k)) := by
  let Q := f - g
  have hQ : ‖(Q:Show P)‖ ≤ ε := dist_eq_norm f g ▸ h
  obtain ⟨u,hu,hU⟩ := ((Show.budget _ _).mp hQ).2.2.1
  obtain ⟨k,hk,hK⟩ := ((Show.budget _ _).mp hQ).2.2.2
  have hf := (Show.budget f ‖f‖).mp le_rfl
  have hg := (Show.budget g ‖g‖).mp le_rfl
  refine ⟨u,k,fun i => ?_,fun i => ?_,?_,?_⟩
  · exact (AnalyticBridge.VerifiedReset.sup_varies (d:=f.proper.reg i)
      (hf.1.smooth i) (hg.1.smooth i)).mpr (hu i)
  · exact hk i
  · apply budget_loosen (sum_cover (V:=fun j s=>(Q.proper.reg j).site=s) ?_ ?_ hU)
    · gcongr
      apply le_max_left
    · intro j
      exact mul_nonneg (Real.exp_nonneg _) (hu j).1
    intro j
    exact ⟨_,rfl⟩
  apply budget_loosen (sum_cover (V:=fun j s=>s∈(Q.proper.forced j).support) ?_ ?_ hK)
  · gcongr; apply le_max_right
  · intro j; exact mul_nonneg (Real.exp_nonneg _) (hk j).1
  intro j
  exact (Q.proper.forced j).inventory_ne.mono (Q.proper.forced j).inventory_sup
end priced

/-- No reindexing of Rep.activities at fixed period; E measured on ALL its
    priced good-family germs, K on all configurations. This does not include
    the scalar. -/
theorem activity_cauchy (S : Jewel R T W) (p m : ℕ) (ε : ℝ) (hp : 0 < ε) :
    let I := stageP R.alloy.B.a m p
    ∀ᶠ M : ℕ in atTop, ∀ N₁ B : ℕ, M ≤ N₁ → M ≤ B →
      let F := (R.family.path.rep N₁ p m).activities
      let H := (R.family.path.rep B p m).activities
      F.reg = H.reg ∧ F.forced = H.forced ∧ deviation I.p F H ε := by
  intro I
  obtain ⟨_, F, _, hX⟩ := S.curves.convergence p (fun N => T.center N p) R.alloy.B.a.clock.bar
    (by
      have he (i : ℕ) : (T.center i p).bonusB = R.alloy.B.a.clock.bar := S.actual.wilson.reaches i p
      simp only [he]
      exact tendsto_const_nhds) m
  let i : ℝ := Fintype.card (Site (R.family.side m p))
  let U := max I.b I.k
  have hi : 0 < i := Nat.cast_pos.mpr Fintype.card_pos
  have hu : 0 < U := lt_of_lt_of_le I.b0 (le_max_left ..)
  let η := ε / (i * U)
  have hv : 0 < η := div_pos hp (mul_pos hi hu)
  obtain ⟨k,hk⟩ := Metric.cauchySeq_iff.mp hX.cauchySeq η hv
  filter_upwards [eventually_ge_atTop m,eventually_ge_atTop k] with M h hM
  intro N₁ B a b Q V
  obtain ⟨_, f, hf, h₁⟩ := S.curves.alignment p N₁ (T.center N₁ p) m (h.trans a)
  obtain ⟨_, g, hg, h₂⟩ := S.curves.alignment p B (T.center B p) m (h.trans b)
  have hc : dist (f : Show I) g ≤ η := Completion.dist_eq f g ▸ by
    rw [h₁,h₂]; exact (hk N₁ (hM.trans a) B (hM.trans b)).le
  rw [show Q = f.proper from hf.symm, show V = g.proper from hg.symm]
  have hE : i * max (η * I.b) (η * I.k) = ε := by
    rw [← mul_max_of_nonneg _ _ hv.le]
    change i * (η * U) = _
    unfold η; field_simp
  exact ⟨rfl,rfl,hE ▸ quote f g hc⟩

end Jewel

end YM.FullVolume.Final
#print axioms YM.FullVolume.Final.july
