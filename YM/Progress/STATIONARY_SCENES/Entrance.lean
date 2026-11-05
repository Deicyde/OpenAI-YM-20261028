import YM.Progress.STATIONARY_SCENES.Dispatch

/-!
# Funding sanity & smaller invoices for the RScene input

In `issue`, does the implication on `Funded` ever kick in? For the linear
kernel lift part, YES. Use the actual H, not replacing its Gram root either,
provide path reads of unmasked `ℓ` in the correct widths, lengths in cover
units. Suffices with any nonlinear corrections supplied WITH their real
invoices. Can even fire RScene with NO corrections yet, at every period
and every depth on one schedule. That's the genuinely nonlinear canonical
base `quadratic` in the unmasked action (includes Ad) and actual blocking,
not a Gaussian or existence of an interacting trajectory. In particular
this does NOT earn high-order match against top Wilson, the cubic/quartic
match across levels or the thermal/suppression estimates that need the proper
curvature corrections. Change `Quote` as ALWAYS **before** rolls/using
`issue` (e.g. can include the linear lift estimates in each forecast).

Only a sufficient path prescription. API accepts any W with the true width
and layout, not necessarily shortest ties. No mask assertions (actual
`inChannels` etc for W can use the same slots).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Progress.StationaryScenes
open Filter Lattice RG RG.Supply Wilson Precision Bid Tree Function Exterior Bloch Matrix Laurent
open YM.Next YM.Next.Scheduling
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators

variable {G : Gauge}

section initial
variable {M : Bed} {R : PathData G} {p : Clip} {σ η A C : ℝ}

/-- The row normalization follows from FULL on-cover layout, not just
looking on a single block of a particular period. Floor really does
use any n incl side 1. -/
theorem base_symbols (he : Attached M R) (hp : 0 < σ)
    (hf : Floor M p (1 : Side) η A)
    (hg : ∀ a : PlaqAxes, SumBudget
      (fun i => |(R.row a i).1| * Real.exp (σ * (R.row a i).2.length)) C) :
    (∀ a b : PlaqAxes, Summable fun i => if (R.row a i).2.plaq = b then (R.row a i).1 else 0) ∧
      R.metric_zero p := by
  classical
  let n : Side := 1
  haveI : Subsingleton (Site n) := by change Subsingleton (Axis → ZMod 1); infer_instance
  let f (a b : PlaqAxes) (i : ℕ) := if (R.row a i).2.plaq = b then (R.row a i).1 else 0
  have hb (a b : PlaqAxes) : Summable (f a b) := by
    refine Summable.of_norm_bounded (hg a).2.1 ?_
    intro i
    unfold f; split
    · rw [Real.norm_eq_abs]
      apply le_mul_of_one_le_right (abs_nonneg _); exact Real.one_le_exp (by positivity)
    rw [norm_zero]; positivity
  have hz (i j : TypeFace 2) : M.metric.acts n (0,i) (0,j) =
      (1 : Matrix (TypeFace 2) (TypeFace 2) ℝ) i j := by
    apply Complex.ofReal_injective
    have hh (x : Cover) : 0 = 0 + wrap n x := Subsingleton.elim ..
    calc
      _ = M.metric.read 0 i j := by
        simp only [Row.acts,Matrix.of_apply,Row.read, Laurent.read,
          Laurent.mode_constant, one_smul, Complex.ofReal_tsum]
        apply tsum_congr
        intro x
        rw [if_pos (hh _)]
      _ = _ := by
        rw [hf.starts]; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have hs (a b : PlaqAxes) : M.roots.acts n (0,plaquette a) (0,plaquette b) = R.symbol0 a b := by
    have ha := ((hb a b).hasSum.tsum_fiberwise (fun i => (R.row a i).2.offset)).tsum_eq
    change _ = ∑' i, f a b i
    rw [← ha]
    refine tsum_congr fun x => ?_
    rw [tsum_subtype]
    rw [if_pos (Subsingleton.elim _ _)]
    rw [← (he.layout a b x).tsum_eq]; apply tsum_congr; intro i
    by_cases hx : (R.row a i).2.offset = x
    · rw [Set.indicator_of_mem (show i ∈ _ from hx)]
      simp [hx,f]
    rw [Set.indicator_of_notMem (show i ∉ _ from hx)]
    simp [hx]
  refine ⟨hb, fun a b => ?_⟩
  have h : ∑ w : Co n Layers2, M.full p n w (0,plaquette a)*M.full p n w (0,plaquette b) =
      M.metric.acts n (0,plaquette a) (0,plaquette b) :=
    congr_fun (congr_fun hf.roots (0,plaquette a)) (0,plaquette b)
  rw [hz, Fintype.sum_prod_type, Finset.sum_eq_single (0 : Site n)
    (fun i _ hg => False.elim <| hg (Subsingleton.elim ..)) (fun he => False.elim (he (Finset.mem_univ _))),
    Fintype.sum_sum_type] at h
  conv at h => lhs; lhs; rw [← Equiv.sum_comp plaqEquiv]
  conv at h => lhs; rhs; rw [← Equiv.sum_comp plaqEquiv]
  simp only [Bed.full,plaq_map,of_apply, Sum.elim_inl, Sum.elim_inr, hs,
    Matrix.one_apply, Prod.mk.injEq, true_and, plaq_iff] at h
  have hl : ∑ i : PlaqAxes,
      (Real.sqrt p.direct * (if i=a then (1:ℝ) else 0)) * (Real.sqrt p.direct * (if i=b then (1:ℝ) else 0)) =
      if a=b then p.direct else 0 := by
    rw [Finset.sum_eq_single a]
    · by_cases hi : a=b <;> simp [hi, Real.mul_self_sqrt p.quadratic_pos.le]
    · intro i _ hi; simp [hi]
    simp
  rw [hl] at h
  exact h
end initial

namespace Ell

def entry : ℕ ≃ PlaqAxes × Cover := Classical.choice (by
  haveI : Nonempty PlaqAxes := ⟨⟨(0,1),by decide⟩⟩
  exact nonempty_equiv_of_countable)

def assign (R : Bed) (a : PlaqAxes) (k : ℕ) : ℝ × Slot :=
  let p := entry k
  (R.roots (plaquette a) (plaquette p.1) p.2, ⟨route 0 p.2 1,p.1⟩)

lemma assign_here (R : Bed) (a : PlaqAxes) (k : ℕ) :
    let x := assign R a k
    x.2.plaq = (entry k).1 ∧ x.2.offset = (entry k).2 ∧
      x.2.length = size (entry k).2 + 4 := by
  intro x
  refine ⟨rfl,route_end ..,?_⟩
  have he (x y : Cover) : (route x y 1).length = size (y-x) := by
    have ha : allAxes 1 = [0,1,2,3] := by decide
    simp [route, axisRoute, ha, size, Fin.sum_univ_succ, straight, Axis]
  change (route 0 _ 1).length+4 = _
  rw [he,sub_zero]

lemma layout (R : Bed) (a b : PlaqAxes) (x : Cover) : HasSum (fun i : ℕ =>
    if (assign R a i).2.plaq = b ∧ (assign R a i).2.offset = x
    then (assign R a i).1 else 0) (R.roots (plaquette a) (plaquette b) x) := by
  let f (i : ℕ) := if (assign R a i).2.plaq = b ∧ (assign R a i).2.offset = x
    then (assign R a i).1 else 0
  let j := entry.symm (b,x)
  have he (i) : (assign R a i).2.plaq = b ∧ (assign R a i).2.offset = x ↔ i=j := by
    rw [(assign_here R a i).1,(assign_here R a i).2.1, ← entry.apply_eq_iff_eq_symm_apply]
    simp only [Prod.ext_iff]
  have hi : f j = R.roots (plaquette a) (plaquette b) x := by
    unfold f; rw [if_pos ((he _).2 rfl)]; simp only [j,assign,Equiv.apply_symm_apply]
  change HasSum f _
  rw [← hi]; exact hasSum_single j (fun i hh => if_neg (mt (he _).1 hh))

/-- Uniform invoice before L. -/
def bill (σ V : ℝ) := Fintype.card PlaqAxes * (Real.exp (σ*4)*V)

lemma row (R : Bed) {σ V : ℝ} (h : R.roots.strip σ V) (a : PlaqAxes) :
    SumBudget (fun i => |(assign R a i).1| * Real.exp (σ*(assign R a i).2.length)) (bill σ V) := by
  let f (b : PlaqAxes × Cover) := Real.exp (σ*4) *
    (Real.exp (σ*size b.2)*‖R.roots (plaquette a) (plaquette b.1) b.2‖)
  have hh : 0 ≤ f := fun ⟨b,x⟩ => by change 0 ≤ f _; unfold f; positivity
  have he (b : PlaqAxes) : Summable fun x : Cover => f (b,x) :=
    (h (plaquette a) (plaquette b)).2.1.mul_left _
  have hs : Summable f := (summable_prod_of_nonneg hh).mpr ⟨he,Summable.of_finite⟩
  rw [show (fun i => |(assign R a i).1| * Real.exp (σ*(assign R a i).2.length)) = fun i => f (entry i) from ?_]
  · refine ⟨fun i => hh _, entry.summable_iff.mpr hs, ?_⟩
    rw [Equiv.tsum_eq entry, hs.tsum_prod, tsum_fintype]
    calc
      _ ≤ ∑ _b : PlaqAxes, Real.exp (σ*4)*V := by
        refine Finset.sum_le_sum fun b _ => ?_
        unfold f
        rw [tsum_mul_left]
        exact mul_le_mul_of_nonneg_left (h (plaquette a) (plaquette b)).2.2 (Real.exp_pos _).le
      _ = _ := by rw [Finset.sum_const,Finset.card_univ, nsmul_eq_mul]; rfl
  funext i
  rw [(assign_here R a i).2.2]
  simp only [f, assign, Real.norm_eq_abs, Nat.cast_add,Nat.cast_ofNat,mul_add,Real.exp_add]
  ring

/-- Keep the caller's atom arrays (which may *depend* on `assign`), only
choose actual ell-row. No assertion station matching or physical-activity
representation with this path. -/
def use (M : Bed) (P : PathData G) : PathData G := { P with row := assign M }

/-- Remaining explicit analytic invoice for the path-only side. Loop moment
conditions are unmasked on the same row, not Gaussian. -/
structure Invoices (P : PathData G) (σ C Λ : ℝ) : Prop where
  cubic : SumBudget (fun i => (P.cubic i).budget σ) C
  quartic : SumBudget (fun i => (P.quartic i).budget σ) C
  loop : SumBudget (fun i => (P.loop i).budget σ) Λ
  invariant i : (P.loop i).Invariant ∧ (P.cubic i).Invariant ∧ (P.quartic i).Invariant
  terms i x : Summable (P.loop_coeff i x) ∧ ∀ l : Axis,
    Summable (fun k => P.loop_coeff i x k *
      ((((P.loop k).leg 1).offset l - ((P.loop k).leg 0).offset l : ℤ) : ℝ))
  norm : P.loop_jets

lemma bounds (M : Bed) (P : PathData G) {σ C V Λ a A : ℝ} {p : Clip}
    (hσ : 0 < σ) (hg : M.roots.strip σ V) (hx : bill σ V ≤ C)
    (hm : Floor M p (1 : Side) a A) (hP : Invoices P σ C Λ) :
    (use M P).Bounds p σ C Λ ∧ Attached M (use M P) := by
  have he a : SumBudget (fun i => |((use M P).row a i).1| * Real.exp (σ*((use M P).row a i).2.length)) C :=
    ⟨(row M hg a).1,(row M hg a).2.1,(row M hg a).2.2.trans hx⟩
  have hh : Attached M (use M P) := ⟨layout M⟩
  have hf := base_symbols hh hσ hm he
  exact ⟨⟨hσ,he,hP.loop,hP.cubic,hP.quartic,hP.invariant,hf.1,hf.2,hP.terms,hP.norm⟩,hh⟩

/-- Sufficient linear part of the pre-L cost (any additional width margins for
copies etc. must fit the Quote too). `issue` chosen K before this. -/
def Rated (q : Quote) (K : MapPrices) : Prop := ∀ j, q.widths.width j ≤ K.α j ∧
    bill (q.widths.width j) (K.Ω j) ≤ q.classicalCost.cap j

/-- Prices that suffice on this interface exist; can choose other Strips
loads/forecasts and Finish after bumping. Not a proof that lowering width
or changing other prices is neutral for paying those (nonlinear!) asks. -/
theorem book (K : MapPrices) : ∃ q : Quote, Rated q K := by
  obtain ⟨q⟩ := quote_ne
  let w : Strips := { q.widths with launch := K.α, top_rate := K.alpha_pos }
  let p : Figures := { q.classicalCost with
    beginCost := fun i => max (q.classicalCost.beginCost i) (bill (w.width i) (K.Ω i))
    pos := fun i => le_max_of_le_left (q.classicalCost.pos i) }
  exact ⟨⟨w,p,q.finish⟩,fun i => ⟨w.le_top _,
    (le_max_right ..).trans (p.le_top _)⟩⟩

lemma launch {a : Levels G} {H : Horizon a} {K : MapPrices} (hh : H.Suffices K)
    {s : Survey G} {q : Quote} (hq : Rated q K) (hs : a.clock.stage = s.melt q)
    (N m : ℕ) (hi : m ≤ N) (P : PathData G)
    (hp : Invoices P (a.params m).width (a.params m).paths (a.clock.loopCap m)) :
    Funded H N m (use (H.H N m) P) := by
  let t := a.params m
  have he : t = s.melt q (a.clock.J m) := congr_fun hs _
  obtain ⟨hα,hΩ⟩ := hq (a.clock.J m)
  have hg : t.width ≤ K.α (a.clock.J m) := he ▸ hα
  have hL : bill t.width (K.Ω (a.clock.J m)) ≤ t.paths := he ▸ hΩ
  have hf := bounds _ P t.width_pos
    (fun i j => (((hh.rows N m hi).2.2.2.1) i j).mono hg le_rfl) hL (hh.all _ _ hi (1:Side)) hp
  exact ⟨hf.1,hf.2⟩

private def blank : Slot := ⟨[],⟨(0,1),by decide⟩⟩
private def noneYet (k : ℕ) : Atom G k := ⟨fun _ => blank,0⟩
private def noNews (G : Gauge) : PathData G :=
  ⟨fun _ _ => (0,blank),fun _ => noneYet 2,fun _ => noneYet 3,fun _ => noneYet 4⟩

/-- Uncorrected, same unmasked canonical rows. Always owes higher-order
kinetic and transfer tests, do NOT use as a constructed RLoops path. -/
def base (G : Gauge) (M : Bed) := use M (noNews G)




end Ell


end YM.Progress.StationaryScenes
