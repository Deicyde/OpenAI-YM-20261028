import YM.Branch.Covariant

/-!
# Calendar issuance API

Orders & constants chosen BEFORE block ratio. Indices j are numeric including
j<start, use dummy/pad values there. High order requirements increasing only
in smoothing index. Clients instantiate monotone sequences with their proven
prices, including anticipated finitely-used constants (do not substitute
realized post-L costs in a pre-L requirement). Existence results here work for
*any already chosen* constants with these scopes. Thus choose arbitrarily large
post-L delay after all pre-L quota and ratios. Does NOT check that the RG
arguments actually fit that dependency schedule.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG.Supply
open Wilson Lattice Set Filter Function Finset
open scoped Matrix.Norms.Frobenius Topology BigOperators
variable {G : Gauge}

/-- Numerical and kernel data fixed before any block ratios. `floorL`
permits additional arithmetic/data thresholds at the same stage, clients
can for example represent the two possible transitions' asks by their `max`,
including neighbors' finite lists and their supports. -/
structure Sheet (G : Gauge) where
  kernel : KernelChoices
  has : ∀ P : Patch, P.Branches kernel G
  profile : ℕ → Stage
  first : ℕ
  cut : 4 ≤ first
  orders : Monotone fun i => (profile i).order
  powers : Monotone fun i => (profile i).power
  prices : Monotone fun i => (profile i).supportExponent
  floorL : ℕ → ℕ

/-- Numeric predicates at each smoothing stage (not physical step). Reserves
use the specified j even if two neighbors have same `profile`. -/
structure Large (p : Sheet G) (j : ℕ) (L : Side) : Prop where
  odd : Odd L.val
  size : 3 ≤ L.val
  need : p.floorL j ≤ L.val
  kick (hj : p.first ≤ j) : (p.profile j).drift / Real.log L.val ≤ G.slopeConstant/4
  slow (hj : p.first ≤ j) : (p.profile j).drift / Real.log L.val ≤ ((j:ℝ)^2)⁻¹
  fits (hj : p.first ≤ j) :
    let X := p.profile j
    Real.log (1 + X.paths + X.width⁻¹ + X.columns + X.clip.relaxation + X.supportExponent) /
      Real.log L.val ≤ ((j:ℝ)^2)⁻¹

structure Rolls (p : Sheet G) where
  L : ℕ → Side
  large : ∀ j, Large p j (L j)
  grow : Monotone fun j => (L j).val

lemma Rolls.eventually_large (p : Sheet G) (h : G.Simple) (i) : ∃ M : ℕ,
    ∀ n : Side, M ≤ n.val → Odd n.val → Large p i n := by
  let B := max 3 (p.floorL i)
  have hb : 3≤B := le_max_left ..
  have hc : p.floorL i≤B := le_max_right ..
  by_cases hi : p.first ≤ i
  · have hj : 0 < (i:ℝ) := by
      have := p.cut
      exact_mod_cast (show 0 < i by omega)
    have ha (x : ℝ) : Tendsto (fun n : ℕ => x / Real.log (n:ℝ)) atTop (𝓝 0) := by
      exact (tendsto_const_nhds (x := x)).div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    have he : ∀ᶠ n : ℕ in atTop, B ≤ n ∧
        (p.profile i).drift / Real.log (n:ℝ) ≤ G.slopeConstant/4 ∧
        (p.profile i).drift / Real.log (n:ℝ) ≤ ((i:ℝ)^2)⁻¹ ∧
        Real.log (1 + (p.profile i).paths + (p.profile i).width⁻¹ + (p.profile i).columns +
          (p.profile i).clip.relaxation+(p.profile i).supportExponent) / Real.log (n:ℝ)≤((i:ℝ)^2)⁻¹ := by
      refine (eventually_ge_atTop B).and ?_
      refine ((ha _).eventually (ge_mem_nhds (div_pos (Gauge.slopeConstant_pos h) (by norm_num)))).and
        (((ha _).eventually (ge_mem_nhds (by positivity))).and ((ha _).eventually (ge_mem_nhds (by positivity))))
    obtain ⟨M,H⟩ := eventually_atTop.1 he
    exact ⟨M,fun n hl ho ↦ ⟨ho,hb.trans (H n hl).1,hc.trans (H n hl).1, fun _ => (H n hl).2.1, fun _ => (H n hl).2.2.1,
      fun _ => (H n hl).2.2.2⟩⟩
  exact ⟨B, fun n hn ho => ⟨ho,hb.trans hn,hc.trans hn,fun u => False.elim (hi u),fun u => False.elim (hi u), fun u => False.elim (hi u)⟩⟩

theorem Rolls.exists_rolls (p : Sheet G) (h : G.Simple) : Nonempty (Rolls p) := by
  choose C H using fun i => eventually_large p h i
  let M := fun i => (range (i+1)).sup C
  have hm : Monotone M := fun i j hij ↦ sup_mono (range_mono (by omega))
  let L := fun i => (⟨2*M i+1, by omega⟩:Side)
  exact ⟨⟨L,fun i ↦ H i _ (by change C i ≤ 2*M i+1; have H₀ : C i≤M i := le_sup (mem_range.mpr (by omega)); omega) ⟨_,rfl⟩,fun i j hij => by change 2*M i+1 ≤ 2*M j+1; have := hm hij; omega⟩⟩

/-- After choosing L freeze a θ accommodating all contributing requests
(post-L powers). -/
structure Protection {p : Sheet G} (w : Rolls p) where
  theta : ℕ → ℝ
  pos j : 0 < theta j
  small j : p.first ≤ j → theta j ≤ (j:ℝ)⁻¹
  dec : Antitone theta

private def TMin (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => f 0
  | n+1 => min (TMin f n) (f (n+1))

lemma Protection.exists_margin {p : Sheet G} (w : Rolls p) (α : ℕ → ℝ) (h : ∀ j, 0 < α j) :
    ∃ P : Protection w, ∀ i, P.theta i ≤ α i := by
  let t (j : ℕ) : ℝ := min ((j:ℝ)+1)⁻¹ (α j)
  have ht (j : ℕ) : 0 < t j := lt_min (by positivity) (h j)
  have hT (j : ℕ) : 0 < TMin t j ∧ TMin t j ≤ t j := by
    induction j with
    | zero => rw [TMin]; exact ⟨ht _,le_rfl⟩
    | succ j ih => rw [TMin]; exact ⟨lt_min ih.1 (ht _),min_le_right ..⟩
  refine ⟨⟨TMin t,fun i ↦ (hT i).1,fun j hj => ?_,antitone_nat_of_succ_le fun j => ?_⟩, fun i ↦ (hT i).2.trans (min_le_right ..)⟩
  · have hn : 0 < (j:ℝ) := by
      have := p.cut
      exact_mod_cast (show 0 < j by omega)
    exact (hT j).2.trans ((min_le_left ..).trans (inv_anti₀ hn (by linarith)))
  change TMin t (j+1) ≤ _; rw [TMin]; exact min_le_left ..

/-- Deadline inputs after protection. Window requests for later weak/comparison
use may also be chosen after bar is fixed (never hidden inside betaEntry). -/
structure Delays {p : Sheet G} {w : Rolls p} (T : Protection w) where
  betaEntry : ℕ → ℝ
  scaleEntry : ℕ → ℝ → ℝ -- after bar, not used on first plateau
  /-- relative to output site count, with BOTH adjacent cover lengths -/
  shells : ℕ → ℕ
  growth : ℕ → ℕ

/-- Barrier for smallness independent of the first spacing which is one. -/
structure Bar {p : Sheet G} {w : Rolls p} {T : Protection w} (W : Delays T) where
  value : ℝ
  good : 1 < value
  ready : W.betaEntry p.first ≤ value
  threshold : ∀ x : ℝ, value ≤ x → (Real.sqrt x)⁻¹ * Real.exp ((Real.log (Real.log x))^2) ≤ 1

/-- Any finitely-asked requirements per j already accounted into these
functions. Request a work stretch with THIS window o(σ) (per FIXED j; not
necessarily bounded over j). Enough to request k-h..k for comparison,
extra positional comparison scales etc by summing bounds.
-/
structure Wait {p : Sheet G} {w : Rolls p} {T : Protection w} {W : Delays T} (Y : Bar W) where
  readyHere : ℕ → ℝ
  window : ℕ → ℝ → ℕ
  sublin j : Tendsto (fun s : ℝ => (window j s:ℝ)/s) atTop (𝓝 0)
  /-- absolute physical minimum. may be arbitrarily huge; all periods before p=0 discarded. -/
  minLength : ℕ

/-- Permanent record -- includes arbitrary entrance gates beforehand. Does not
follow that every Θ/num requirement of the physics has been anticipated.
Initial m=0 is coarse level, and step `m+1`→`m` already meets these gates;
use also the `Bar` fields at level 0. -/
structure Paid {p : Sheet G} {w : Rolls p} {T : Protection w} {W : Delays T} {Y : Bar W}
    (B : Wait Y) (a : Levels G) : Prop where
  kernel : a.clock.kernel = p.kernel
  bar : a.clock.bar=Y.value
  stage : a.clock.stage=p.profile
  firstZero : a.clock.J 0=p.first
  firstOne : a.clock.J 1=p.first
  lengths : a.clock.factor=w.L
  theta : a.clock.theta=T.theta
  pays m : W.betaEntry (a.clock.J (m+1)) ≤ a.clock.hatBeta m
  paysHigher m : p.first < a.clock.J (m+1) → W.scaleEntry (a.clock.J (m+1)) Y.value ≤ a.S.scale m
  periods i : B.minLength ≤ (a.S.period i).val
  volume m i :
    let j := a.clock.J (m+1)
    W.shells j * (1+a.clock.coverSize m+a.clock.coverSize (m+1))^(W.growth j) ≤ (a.S.side m i).val
  run (j : ℕ) : p.first ≤ j → ∃ k : ℕ,
    B.readyHere j ≤ a.S.scale k ∧ B.window j (a.S.scale k) ≤ k ∧
      ∀ i : ℕ, k-B.window j (a.S.scale k) ≤ i → i ≤ k+B.window j (a.S.scale k) → a.clock.J i=j
end YM.RG.Supply
