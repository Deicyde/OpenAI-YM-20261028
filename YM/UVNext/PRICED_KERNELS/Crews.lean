import YM.UVNext.PRICED_KERNELS.Missing
import YM.UVNext.PRICED_KERNELS.Peak



set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Ex ante budgeting the actual top, producing the first iteration input

Against Before. Uses layout quotes incl flexible convention thereafter if
wanted. Leaves `Below` for the nonlinear generated data after arbitrary first
stationary solve, for THIS engineered Levels and the installed prices incl all
pre-L choices. Doesn't try budgeting post quantities depending on L *before*
Rolls. The nonlinear estimates for the stationary passage itself are required
with the PathInputs/A coefficients already paid; peaks paid on actual objects
here NOT asked additionally of caller. Same V for all consumers. Keep even
canonical addresses exactly as billed. Branch choices and scalars in thermal
prescription as specified. No η caps on fields used at top. Doesn't incorporate
 decomposition on the ordinary / global-l version of the generator;
uses variant at top, also must back that choice in subsequent RG proofs if pursuing.
`sale` gives *ANY* M first ask (even with arbitrary Caps honoring terms),
subsequent *not* guaranteed, but `remaining` gives reusable conditional assembly.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.PricedKernels
open Filter Set Function Lattice RG RG.Supply Wilson Precision Craft Pressure Exterior Laurent Bloch Tree
open Push.PriceCompiler
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge} {n : Side}

/-- flat nonlinear quote piece (born). May equally buy for higher-than-active
input rates e.g. 2, even polynomial moments (all lengths here 16); doesn't
depend on other parts of the pricing loop. -/
def earn (G : Gauge) (p : Clip) (s : ℝ) := ∑ i ∈ few, (tipAtom (G:=G) p i).budget s
lemma enough (p : Clip) (s : ℝ) : SumBudget (fun i => (tipAtom (G:=G) p i).budget s) (earn G p s) := by
  have hn : ∀ i ∉ few, (tipAtom (G:=G) p i).budget s=0 := fun i hi => by
    rw [active_few _ hi]; simp [dormant,Atom.budget,Atom.magnitude]
  refine ⟨?_,summable_of_ne_finset_zero hn,(le_of_eq (tsum_eq_sum hn))⟩
  intro i; unfold Atom.budget Atom.magnitude; positivity

lemma amount_mono (p : Clip) {s t : ℝ} (h : s ≤ t) : earn G p s ≤ earn G p t := by
  apply Finset.sum_le_sum
  intro i _; unfold Atom.budget
  gcongr; unfold Atom.magnitude; positivity

/-- After layout asks but before opens committed. Doesn't interfere with canonical
or Ways asks. Doesn't affect loop caps except through later formulas for amounts;
Caps apply independent. Before.Openings see the correct asks and neither width nor L
needs to feed into the part in amounts seen by earn. -/
def covering (G : Gauge) (R : Charges) : Charges := { R with asks := fun c f K w =>
  let A := R.asks c f K w
  { A with born := fun i => max (A.born i) (earn G (c i) 2), born_pos := fun i => (A.born_pos i).trans_le (le_max_left ..) } }

lemma first_numbers (c : ℕ → Clip) (g : LayoutPrices) (R : Charges) (p : Before) (X : MapPrices) :
    let P := issue G p (flatOf X) c (g.requests (covering G R))
    ∀ i, earn G (P.clip i) 2 ≤ P.amount.born i := by
  intro P i
  obtain ⟨_,_,ht,_⟩ := linear_paths G p (flatOf X) c (g.requests (covering G R))
  exact (le_max_right ..).trans ((le_max_left ..).trans (ht i))

lemma first_crew {p : Clip} (H : Bed) (C : ℝ) (hs : 0 ≤ C) (s : ℝ) (h : earn G p s ≤ C) :
    Atoms s 0 C C (choice (G:=G) H p) := by
  obtain ⟨hh,h₁,-,hm,hj⟩ := base_atoms (G:=G) (σ:=s) H (le_refl (0:ℝ)) hs
  obtain ⟨hn,hS,hH⟩ := enough (G:=G) p s
  refine ⟨hh,h₁,⟨hn,hS,hH.trans h⟩,fun i => ⟨(hm i).1,(hm i).2.1,?_⟩,hj⟩
  unfold choice tipAtom
  dsimp
  split_ifs
  · intro u x; rw [AtomExact,AtomExact,polish_symm]
  exact (hm i).2.2

section Permit
variable {P : Before} {f : ℕ → ℕ} {D : Rolls (P.sheet G f)}
  {M : Preparations P D} {T : Protection D} {W : Delays T} {Y : Bar W} {I : Wait Y}
  {a : Levels G} (h : Permit M I a) {B V : Horizon a}

/-- Need this at ANY U.Wait/Bar/levels of sale. Top p.direct comes from
`a.params` clip (therefore agrees with `budgetPoint` etc in continuation if
using). The LayoutPrices amounts are buying with `(P.clip i)` at provisional;
`active` Clip modifies relaxation only, irrelevant! -/
lemma earn_direct {p q : Clip} (h : p.direct=q.direct) (s : ℝ) : earn G p s = earn G q s := by simp [earn,tipAtom,h]

include h
lemma on_budget {q : Before} {X : MapPrices} {c : ℕ → Clip} {g : LayoutPrices} {R : Charges}
    (hP : P = issue G q (flatOf X) c (g.requests (covering G R))) (N : ℕ) :
    StartAtoms P a N (choice (V.H N N) (a.params N).clip) := by
  unfold StartAtoms
  intro j i C _
  have hh : P.clip = c := hP ▸ rfl
  have hu : i.clip.direct=(P.clip j).direct := by
    unfold i; rw [params_eq h.paid]; rfl
  apply first_crew (V.H N N) C (P.amount.born_pos j).le i.width
  refine (amount_mono i.clip (s:=i.width) (t:=2) ?_).trans ((le_of_eq (earn_direct hu 2)).trans ?_)
  · unfold i; rw [params_eq h.paid]; change rateLo P.opening.offered j / 2 ≤ _; linarith [rateLo_one P.opening.offered j]
  unfold C; rw [hP]
  exact first_numbers c g R q X _

/-- Given canonical asks, deliver REAL top resources, including the estimates
needed for any ask at N-1 and peak (the f.Build uses unmasked terms). Keep `h`
Permit even at N=0. No cutoff pass price hypothesis here except funding at
shown tables and `Rewired` data which `preps` + `rewire` provide on that
exact Permit if honoring Caps. -/
theorem first {q : Before} {X : MapPrices} {c : ℕ → Clip} {g : LayoutPrices} {R : Charges}
    (hP : P = issue G q (flatOf X) c (g.requests (covering G R))) {l} (hv : Rewired P a X l B V) (N : ℕ) :
    let H := V.H N N; let p := (a.params N).clip; let Q := choice (G:=G) H p
    StartAtoms P a N Q ∧ Billed P a V N N Q ∧ Budgeted a N Q ∧
      ∀ n : Side,∀ j ≤ 4, SameJet j (fun x => mainTerm p Q (represent (x : Bid.Dir G n))) (fun x => Wilson.energy (represent x)) := by
  have hc : Canonical.Quotes (P.frozen G) P.opening P.amount := hP ▸ (linear_paths _ _ _ _ _).1
  intro H p Q
  have hh : StartAtoms P a N Q := on_budget h hP N
  have hu := charge_canonical h hv.finalCosts hc N N le_rfl Q rfl
  have hw : 2*(a.params N).width ≤ P.opening.born (a.clock.J N) := by rw [params_eq h.paid]; exact P.opening.born_ge _
  obtain ⟨he,hg⟩ := hu.merge (hh hw) (Or.inl (le_refl _))
  have he' : P.amount.born (a.clock.J N) ≤ (a.params N).paths := by rw [params_eq h.paid]; exact P.amount.born_le _
  have hx := hg.mono (a.params N).width_pos le_rfl he' ((show (0:ℝ) ≤ 2 by norm_num).trans (cap_ge a N)) he' he'
  have ht : Budgeted a N Q := hx.bounds he le_rfl le_rfl le_rfl
  exact ⟨hh,hu,ht,fun L => peak (n:=L) (G:=G) _ _ (hv.sameTrain.base N).1 (Canonical.direct_le_one ht.metric)⟩

end Permit
variable {P : Before} {f : ℕ → ℕ} {D : Rolls (P.sheet G f)}
  {M : Preparations P D} {T : Protection D} {W : Delays T} {Y : Bar W} {I : Wait Y}
  {a : Levels G} (h : Permit M I a) {B V : Horizon a} {q : Before} {X : MapPrices} {c : ℕ → Clip} {g : LayoutPrices} {R : Charges}
  (hP : P = issue G q (flatOf X) c (g.requests (covering G R))) {l} (hv : Rewired P a X l B V)
include h hP hv

/-- Standalone appointment service.

Uses choice's real roots and normalization
and actual F01 gap.

Get the exact frame/tag-consistent scene at ANY top→previous
and all periods, with issued gamma.

This p positivity theorem doesn't need Caller
to already have the series or any path constructors or Caps inequalities. -/
theorem at_top (m p : ℕ) (F : Forest (a.clock.op m p).ratio) :
    let N := m+1
    let X := (a.params N).clip; let Q := choice (G:=G) (V.H N N) X
    let η := M.gap (a.clock.J N)
    0 < η ∧ PriceGap F X Q η ∧ ∃ ρ, Critical F X Q ρ ∧
      Guessed F (installed (a.clock.op m p).ratio (V.towers N m).A0) ρ ∧ Bid.HeatG F X Q ρ (V.H N m) := by
  obtain ⟨-,he,ht,-⟩ := first h hP hv (m+1)
  exact ⟨M.scenes.pos _,h.called hv.finalCosts (m+1) m p (Nat.lt_succ_self m) F ht he.placed (hv.swears _ _ _ le_rfl)⟩

/-- A per-edge residual input to the still nonlinear path work. Caller doesn't
need to produce Critical anew! Take solution with `.heat` and Γ from Permit
by `h.called`, ANY again. Use in paying j=3,4 and wave estimates in `keeps`
for one choice & period family. Below exposes those exact α/choice/share estimates
together with the builder. q, alpha may be assembled by external coherence;
putting an arbitrary α table with no comparison is NOT enough. Include additional
Ready/keeps witnesses in e.g. LocalBuilder version if tying actual quartic
coefficients to rare vStep TK data. May instead generate and use a whole sequence
locally with `Installed`, `path_to_kinetic`, `Remaining` above.
-/
def Needs (M : Preparations P D) (q : AfterBill) (_V : Horizon a) (α : ℕ → ℕ → ℝ)
    (N m : ℕ) (F L : PathData G) :=
      let j := a.clock.J (m+1); let i := a.clock.J m
      |α N m + G.slopeConstant * Real.log (a.S.block m).val| ≤ P.slopePrices.kineticErr j i ∧
        ∀ p, ∃ (T : Forest (a.clock.op m p).ratio) (k : (a.clock.op m p).Choices),
          Expensive F L (a.params (m+1)).clip (a.params m).clip (α N m)
            (Next.Foundations.chart G) (M.gap j) (q.error j i) (q.decay j i) (a.clock.loopCap (m+1)) T k

structure Below (M : Preparations P D) (q : AfterBill) (V : Horizon a) (g : LayoutPrices) (α : ℕ → ℕ → ℝ)
    (Can : ℕ → ℕ → PathData G → Prop) : Prop where
  -- peak fixed; never asking customer to pay estimates on this choice
  feasibility N : Can N N (choice (V.H N N) (a.params N).clip)
  pour N m : m < N → ∀ R, Can N (m+1) R → Billed P a V N (m+1) R → Budgeted a (m+1) R →
    ∃ Q, NextAtoms P a m R Q ∧ Allowed (V.H N m) g (a.clock.J m) Q ∧ Can N m Q ∧ Needs M q V α N m R Q

-- keep the exact peak in the assembled sequence, ready incl Eq when m=N


omit h hP hv in
/-- Both numerical + actual existence, ∀ all provisional profile costs
at these K & issued openings, incl layout & top pull. Entry demo uses also
Sector consumer once B has all nonlinear arrays (`Below.thenKinetic`, etc),
not implying trajectory. Preserve the selected β/profile/Meters and Period
arrangements all the way. -/
theorem sale (hG : G.Simple) (p : Before) :
    ∃ X l γ b, Consecutive (p.kernelChoice G) X l γ b ∧
      ∀ (c : Caps p.first γ) (g : LayoutPrices) (R : Charges),
        let P := issue G p (flatOf X) c.clips (g.requests (covering G R))
        Canonical.Quotes (P.frozen G) P.opening P.amount ∧ Covers (P.frozen G) P g ∧
          ∀ e : ℕ → ℕ, ∃ f : ℕ → ℕ, Monotone f ∧ e ≤ f ∧ b ≤ f ∧ ∀ y : ℕ → ℕ, f ≤ y →
            Built G P X l y ∧ ∀ (D : Rolls (P.sheet G y)) (M : Preparations P D)
              (T : Protection D) (W : Delays T) (Y : Bar W) (I : Wait Y) (a : Levels G), Permit M I a →
              ∃ (B V : Horizon a), Rewired P a X l B V ∧
                (∀ N, let H := V.H N N; let p := (a.params N).clip; let Q := choice (G:=G) H p
                    Budgeted a N Q ∧ ∀ n : Side,∀ j ≤ 4, SameJet j (fun x => mainTerm p Q (represent (x : Bid.Dir G n))) (fun x => Wilson.energy (represent x))) ∧
                (∀ m p : ℕ, ∀ F : Forest (a.clock.op m p).ratio,
                  let N := m+1; let v := (a.params N).clip; let Q := choice (G:=G) (V.H N N) v; let η := M.gap (a.clock.J N)
                  0 < η ∧ PriceGap F v Q η ∧ ∃ ρ, Critical F v Q ρ ∧
                    Guessed F (installed (a.clock.op m p).ratio (V.towers N m).A0) ρ ∧ Bid.HeatG F v Q ρ (V.H N m)) := by
  obtain ⟨X,l,γ,b,hM,hK⟩ := both_compilers hG p
  refine ⟨X,l,γ,b,hM,fun c g R => ?_⟩
  obtain ⟨hn,ha⟩ := hK c (g.requests (covering G R))
  refine ⟨hn, g.covered _ _ _ _, fun e => ?_⟩
  obtain ⟨f,hf,he,hl,h⟩ := ha e
  refine ⟨f,hf,he,hl,fun y hy => ⟨(h y hy).1,fun D M T W Y I a hA => ?_⟩⟩
  obtain ⟨B,V,hV⟩ := (h y hy).2 D M T W Y I a hA
  -- rfl hP need specify q,c,R
  exact ⟨B,V,hV,fun N => (first (q:=p) (c:=c.clips) (g:=g) (R:=R) hA rfl hV N).2.2,
    fun m p' F => at_top (q:=p) (c:=c.clips) (g:=g) (R:=R) hA rfl hV m p' F⟩

end YM.UVNext.PricedKernels
