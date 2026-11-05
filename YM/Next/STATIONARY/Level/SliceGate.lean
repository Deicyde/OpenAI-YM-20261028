import YM.Ac.Tree
import YM.Integrated
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.B04
import YM.Work.B06
import YM.Work.F05

set_option autoImplicit false
/-!
# The RScene gate at the periods actually read

This is conditional on PathData funding; no pre-L uniformity is being
claimed for the gap constant (it is chosen *before the wait*, but after L).
The period entrance requirement for this piece can be paid by `shells`
regardless of the rest of the spatial budget.
-/

noncomputable section
namespace YM.Stationary
open Function Lattice RG Wilson Precision Tree Supply Matrix Pressure Filter Exterior
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge}

/-- This ask can even be determined by the two shape indices, before L. -/
def GateVolume (j : ℕ) := 100 * (j+3+4)

section level
variable {s : Sheet G} {L : Rolls s} {M : Protection L} {W : Delays M} {b : Bar W} {v : Wait b}
    {a : Levels G}

theorem larger (h : Paid v a) (hv : ∀ j, GateVolume j ≤ W.shells j) (m p : ℕ) :
    Bid.Larger (a.clock.op m p) (G:=G) := by
  let X := a.S.block m
  let j := a.clock.J (m+1)
  have he := h.volume m p
  have hs : GateVolume j ≤ (a.S.side m p).val := (hv j).trans ((Nat.le_mul_of_pos_right _ (by positivity)).trans he)
  refine ⟨(a.blocks m p).branches,?_,?_⟩
  · rw [show (a.S.side (m+1) p).val = _ from (a.S.oneStep m p).exact_size]
    change 100 * ((j+3)*X.val+4*X.val) ≤ (a.S.side m p).val * X.val
    rw [← add_mul, ← mul_assoc]
    exact Nat.mul_le_mul_right _ hs
  exact lt_of_lt_of_le (by unfold GateVolume; omega) hs

/-- Enough input for both `Planned.gap` and the graph-wise next transfer,
including a gap uniform among all Steps at this choice of K and post L. -/
structure BudgetGap (s : Sheet G) (L : Rolls s) (Y : MapPrices) (η : ℕ → ℝ) : Prop where
  pos j : 0 < η j
  ask (j : ℕ) {c f : Side} (S : StepData c f)
      (hk : S.kernel=s.kernel) (hl : S.patch.L=L.L j) (hj : S.patch.J=j)
      (u : Bid.Larger S (G:=G)) (H : Forest S.ratio) (B C : Bed)
      (p q : Clip) (R : PathData G) (σ A Λ e δ υ : ℝ) (T : Towers S.patch.L) :
      T.Diagonal S B C → Floor B p f (Y.η j) e → R.Bounds p σ A Λ →
      Attached B R → Bid.Sworn B f G → Floor C q c δ υ →
      PriceGap H p R (η j) ∧ ∃ ρ, Critical H p R ρ ∧
        Guessed H (Bloch.installed S.ratio T.A0) ρ ∧ Bid.HeatG H p R ρ C

theorem scene_gate (L : Rolls s) (Y : MapPrices) : ∃ η, BudgetGap s L Y η := by
  choose η hη hu using fun j =>
    (Integrated.stationary_scene (G:=G) (L.L j) j s.kernel (Y.η j) (Y.eta_pos j)).χ
  exact ⟨η, hη, fun j _ _ => hu j _ _⟩

variable {H : Horizon a} {Y : MapPrices} {η : ℕ → ℝ}


end level

section forest
variable {c f : Side} {S : StepData c f}
    {H T : Forest S.ratio} {p : Clip} {R R' : PathData G} {A : ChartRatio G}
    {ρ : Bid.Dir G c → AxisChart G H} {ρ' : Bid.Dir G c → AxisChart G T}
    {η σ K Λ : ℝ}

/-- The real germ assertion in `retains`, independently of the unknown
momentum bound. -/
lemma born (hw : R.Bounds p σ K Λ) (h : Critical H p R ρ) (hg : PriceGap H p R η)
    (hη : 0 < η) (hA : LocalRatio A) (t : S.Choices) : ContDiffAt ℝ ω (thermal H t p R ρ A) 0 := by
  have hi : ContDiffAt ℝ ω (fun x : Bid.Dir G c => (x,ρ x)) 0 := contDiffAt_id.prodMk h.2.1
  let F := tested H t p R
  have hh : ContDiffAt ℝ ω (fun z : Bid.Dir G c × AxisChart G H => fderiv ℝ (fderiv ℝ (F z.1)) z.2) (0,ρ 0) := by
    rw [h.1]; exact Work.F05.curve_partial (F:=fun x => fderiv ℝ (F x)) (Work.F05.curve_partial (h.2.2 t).1)
  have hu : ContDiffAt ℝ ω (fun x => (hessian H t p R x (ρ x)).det) 0 := by
    -- no choice of norm on matrix-valued functions enters
    simp_rw [Matrix.det_apply]
    refine ContDiffAt.sum fun i _ => ?_
    simp only [Units.smul_def, zsmul_eq_mul]
    refine ContDiffAt.mul contDiffAt_const (contDiffAt_prod (by intro a _; dsimp only [hessian,Matrix.of_apply]; simp_rw [iteratedFDeriv_two_apply]; exact ((hh.comp (f:=fun x => (x,ρ x)) 0 hi).clm_apply contDiffAt_const).clm_apply contDiffAt_const))
  have hd := (Work.F05.hessian_pos hη hg h t).self_of_nhds
  have hm (e : H.Free) : ContDiffAt ℝ ω (fun x => A.J (ρ x e)) 0 := by
    have hj := hA.germ 0 (Metric.mem_ball_self hA.patch)
    exact (show ContDiffAt ℝ ω A.J (ρ 0 e) by rwa [h.1]).comp (f:=fun x => ρ x e) 0 ((contDiffAt_apply ℝ G.Color e _).comp 0 h.2.1)
  unfold thermal
  refine ContDiffAt.sub (ContDiffAt.add ?_ (ContDiffAt.mul contDiffAt_const (hu.log hd.ne')))
    ((contDiffAt_prod (fun e _ => hm e)).log (by rw [h.1]; simp [hA.anchored]))
  unfold loop Patch.average
  refine ContDiffAt.mul contDiffAt_const (ContDiffAt.sum fun s _ => ?_)
  refine Work.F02.uncut_contDiffAt (A:=fun x : Bid.Dir G c => pull s 0 (lifting H (represent x) (ρ x))) hw.width hw.two (fun i => ?_)
  have Hm (e : Edge (Site f)) : ContDiffAt ℝ ω (fun x => G.mat (lifting H (represent x) (ρ x) e)) 0 :=
    (show ContDiffAt ℝ ω (fun u : Work.F03.ChartVars H G => G.mat (Work.F03.live H u e)) (0,ρ 0) by
      rw [h.1]; exact Work.F03.live_smooth H _).comp (f:=fun x => (x,ρ x)) 0 hi
  unfold pull Step.read; split
  · exact (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ (Hm _)
  exact Hm _

theorem transfer_bound {q : Clip} {α D ν M : ℝ} (hx : Bid.Larger (G:=G) S)
    (hw : R.Bounds p σ K Λ) (hA : LocalRatio A) (hη : 0 < η)
    (h : Critical H p R ρ) (ht : Critical T p R ρ')
    (hv : PriceGap H p R η) (hu : PriceGap T p R η)
    (hq : FiniteBound T R R' p q α A ρ' D ν M) : FiniteBound H R R' p q α A ρ D ν M := by
  refine ⟨Work.F05.hessian_pos hη hv h,born hw h hv hη hA, hq.classicalResult,?_⟩
  intro t i j v w hi hj
  have hh := Work.F05.same_thermal hx.1 hw h ht hη hu hA t
  exact (hh.iteratedFDeriv ℝ 2).eq_of_nhds.symm ▸ hq.wave_price t i j v w hi hj
end forest
end YM.Stationary
end

/-!
# Costed path realization of the base

The `.full` read of an arbitrary Bed need not use paths in the interface. Here we
arrange the paths, including in the repeated-plateau case, before choosing the
atom fields. Work on the cover and price true lengths, not wrapped/geodesic
lengths. Metric at zero read from Floor on the one-site torus (available by
Suffices.all, not the actual testing periods).
-/
noncomputable section

namespace YM.Stationary
open Filter Function Lattice RG Wilson Precision Tree Supply Matrix Pressure Exterior Bloch Laurent Finset
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius InnerProductSpace

variable {G : Gauge}

lemma route_length (x y : Cover) (o : Lattice.Order) : (route x y o).length = size (y-x) := by
  have he (l : List Axis) (h : l.Nodup) : (axisRoute x y l).length = ∑ i ∈ l.toFinset, ((y-x) i).natAbs := by
    induction l with
    | nil => simp [axisRoute]
    | cons i l ih =>
      obtain ⟨h₁,h₂⟩ := List.nodup_cons.mp h
      rw [List.toFinset_cons, show axisRoute x y (i::l) = straight i ((y-x) i) ++ axisRoute x y l from rfl,
        sum_insert (by simpa using h₁), List.length_append, ih h₂, straight, List.length_replicate]
  have hm (i : Axis) : i ∈ (allAxes o).toFinset := List.mem_toFinset.mpr (List.mem_map.mpr
    ⟨o.symm i,List.mem_finRange _,o.apply_symm_apply _⟩)
  rw [route, he (allAxes o) ((List.nodup_finRange _).map o.injective), eq_univ_of_forall hm]; rfl

def walkSlot (b : PlaqAxes) (y : Cover) : Slot := ⟨route 0 y (Equiv.refl Axis),b⟩

@[simp] lemma walkSlot_end (b : PlaqAxes) (y : Cover) : (walkSlot b y).offset=y := route_end _ _ _
lemma walkSlot_cost (b : PlaqAxes) (y : Cover) : (walkSlot b y).length = size y+4 := by
  unfold walkSlot Slot.length; rw [route_length,sub_zero]

lemma budget_copy {ι ζ : Type*} (e : ι ≃ ζ) {f : ζ → ℝ} {c : ℝ} (h : SumBudget f c) : SumBudget (f ∘ e) c := by
  exact ⟨fun i => h.1 _,e.summable_iff.mpr h.2.1,(e.tsum_eq f).trans_le h.2.2⟩

lemma budget_prod_finite {ι ζ : Type*} [Fintype ι] {f : ι×ζ → ℝ} {A : ι → ℝ} (h : ∀ i, SumBudget (fun x => f (i,x)) (A i)) : SumBudget f (∑ i, A i) := by
  have hs (i : ι × ζ) : 0 ≤ f i := (h i.1).1 _
  have hh := (summable_prod_of_nonneg (f:=f) hs).2 ⟨fun i => (h i).2.1,(hasSum_fintype _).summable⟩
  refine ⟨hs,hh,?_⟩
  rw [hh.tsum_prod, tsum_fintype]
  exact sum_le_sum fun i _ => (h i).2.2

def enumerate (α : Type) [Countable α] [Infinite α] : ℕ ≃ α := (@Denumerable.eqv α (Classical.choice (nonempty_denumerable α))).symm

abbrev addresses : ℕ ≃ PlaqAxes × Cover := by
  haveI : Nonempty PlaqAxes := ⟨⟨(0,1),by decide⟩⟩
  exact enumerate _

def rowPath (B : Bed) (b : PlaqAxes) (n : ℕ) :=
  let i := addresses n
  (B.roots (plaquette b) (plaquette i.1) i.2,walkSlot i.1 i.2)

def emitBase (G : Gauge) (B : Bed) (A : ℕ → Atom G 2) (X : ℕ → Atom G 3) (Y : ℕ → Atom G 4) : PathData G :=
  ⟨rowPath B,A,X,Y⟩

def rowPrice (σ C : ℝ) := (Fintype.card PlaqAxes:ℝ) * (C*Real.exp (σ*4))

lemma price_paths {B : Bed} {σ C : ℝ} (h : B.roots.strip σ C) (b : PlaqAxes) :
    SumBudget (fun k => |(rowPath B b k).1| * Real.exp (σ * (rowPath B b k).2.length)) (rowPrice σ C) := by
  let f : PlaqAxes × Cover → ℝ := fun x => |B.roots (plaquette b) (plaquette x.1) x.2| * Real.exp (σ * (walkSlot x.1 x.2).length)
  refine budget_copy addresses (?_ : SumBudget f _)
  have he : rowPrice σ C = ∑ _ : PlaqAxes, C * Real.exp (σ*4) := by simp [rowPrice]
  rw [he]; refine budget_prod_finite (A:=fun _ => _) (fun i => ?_)
  let g (x : Cover) := Real.exp (σ*size x) * ‖B.roots (plaquette b) (plaquette i) x‖
  let d := Real.exp (σ*4)
  have ht : SumBudget g C := h (plaquette b) (plaquette i)
  rw [show (fun x => f (i,x)) = (fun x => g x*d) by
    funext x; unfold f g d; rw [walkSlot_cost]; push_cast; rw [mul_add,Real.exp_add,mul_comm _ ‖_‖]; simp only [Real.norm_eq_abs]; ring]
  refine ⟨fun i => mul_nonneg (ht.1 _) (Real.exp_pos _).le,ht.2.1.mul_right d,?_⟩
  rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right ht.2.2 (Real.exp_pos _).le

section matching
variable {R : PathData G} {B : Bed} (hR : R.row=rowPath B)
include hR

lemma rows_layout : Attached B R := by
  constructor
  intro i j x
  rw [hR]
  let g := fun y : PlaqAxes × Cover => if (j,x)=y then B.roots (plaquette i) (plaquette j) x else 0
  have ht : (fun k => if (rowPath B i k).2.plaq=j ∧ (rowPath B i k).2.offset=x then (rowPath B i k).1 else 0) = g ∘ addresses := by
    ext k; unfold g; by_cases h : addresses k = (j,x)
    · simp only [rowPath,h, walkSlot_end,Function.comp_apply, ↓reduceIte]
      simp [walkSlot]
    rw [Function.comp_apply,if_neg (Ne.symm h)]; apply if_neg
    rintro ⟨ha,hb⟩; simp only [rowPath,walkSlot_end] at hb; exact h (Prod.ext ha hb)
  rw [ht]; exact addresses.hasSum_iff.mpr (hasSum_ite_eq' _ _)
end matching

variable {B : Bed} {p : Clip} {η M : ℝ}

/-- Row read on the one-site torus identifies the harmonic. Does not already
assume the other `Bounds` clauses. -/
theorem symbol_match {R : PathData G} (h0 : Attached B R) (hw : ∀ i, Summable fun k => ‖(R.row i k).1‖)
    (h : Floor B p 1 η M) : R.metric_zero p := by
  have hz (x : Site 1) : x=0 := by haveI : Subsingleton (Site 1) := inferInstanceAs (Subsingleton (Four (ZMod 1))); exact Subsingleton.elim ..
  -- fiber the summable signed row by the offset of its path.
  have hr (b q : PlaqAxes) : R.symbol0 b q = B.roots.acts 1 (0,plaquette b) (0,plaquette q) := by
    let r (k : ℕ) := if (R.row b k).2.plaq=q then (R.row b k).1 else 0
    have hs : Summable r := by
      refine (hw b).of_norm.indicator {k | (R.row b k).2.plaq=q} |>.congr (fun k => ?_)
      simp [Set.indicator,r]
    let t (k : ℕ) := (R.row b k).2.offset
    have H := (hs.hasSum.tsum_fiberwise t).tsum_eq.symm
    change (∑' k,r k)=_
    apply H.trans
    rw [Row.acts,of_apply]
    apply tsum_congr; intro x
    rw [if_pos (hz _ |>.symm), ← (h0.layout b q x).tsum_eq, _root_.tsum_subtype _ r]
    apply tsum_congr; intro i
    classical
    by_cases hi : t i=x
    · rw [Set.indicator_of_mem (show i∈t ⁻¹' {x} from hi)]
      unfold r
      simp only [show (R.row b i).2.offset=x from hi,and_true]
    rw [Set.indicator_of_notMem (show i∉t ⁻¹' {x} from hi), if_neg (fun v => hi v.2)]
  intro i j
  have he (x y : TypeFace 2) : B.metric.acts 1 (0,x) (0,y) = if x=y then 1 else 0 := by
    have hh := congr_fun (congr_fun h.starts x) y
    rw [Row.read,of_apply,Laurent.read] at hh
    simp only [mode_constant,one_smul,← Complex.ofReal_tsum,Matrix.one_apply] at hh
    rw [Row.acts,of_apply]
    have hs (z : Cover) : (0 : Site 1)=0+wrap 1 z := (hz _).symm
    change (∑' z : Cover, if (0 : Site 1)=0+wrap 1 z then B.metric x y z else 0)=_
    trans ∑' z : Cover, B.metric x y z
    · exact tsum_congr fun a => if_pos (hs a)
    split_ifs at hh ⊢ with H <;> exact_mod_cast hh
  have H := congr_fun (congr_fun h.roots (0,plaquette i)) (0,plaquette j)
  simp_rw [mul_apply,Fintype.sum_prod_type,he,Fintype.sum_sum_type] at H
  rw [Finset.sum_eq_single 0] at H
  · simp only [transpose_apply,Bed.full, of_apply, Sum.elim_inl,Sum.elim_inr, one_apply,Prod.mk.injEq,true_and,
      mul_ite,mul_one,mul_zero,ite_mul] at H
    rw [← Equiv.sum_comp plaqEquiv (fun x => _)] at H
    simp [plaq_iff,← sq, Real.sq_sqrt p.quadratic_pos.le] at H
    rw [← Equiv.sum_comp plaqEquiv (fun x => _)] at H
    simpa [hr,eq_comm] using H
  · exact fun x hx hn => False.elim (hn (hz x))
  simp

lemma build_cap {A : ℕ → Atom G 2} {X Y} (B : Bed) {σ K Λ Ω : ℝ}
    (hσ : 0 < σ) (hr : B.roots.strip σ Ω) (hf : Floor B p 1 η M)
    (hv : rowPrice σ Ω ≤ K) (hA : SumBudget (fun i => (A i).budget σ) Λ)
    (hX : SumBudget (fun i => (X i).budget σ) K) (hY : SumBudget (fun i => (Y i).budget σ) K)
    (hu : ∀ i, (A i).Invariant ∧ (X i).Invariant ∧ (Y i).Invariant)
    (hm : ∀ (i : Fin 2 → PlaqAxes) (x : Fin 2 → G.ColorIndex),
      let W := emitBase G B A X Y
      HasSum (W.loop_coeff i x) 0 ∧ ∀ l : Axis, HasSum (fun k => W.loop_coeff i x k *
        (((((A k).leg 1).offset l - ((A k).leg 0).offset l : ℤ) : ℝ))) 0) :
    (emitBase G B A X Y).Bounds p σ K Λ := by
  let R := emitBase G B A X Y
  have hk (i) : Summable fun k => ‖(R.row i k).1‖ := by
    refine (price_paths hr i).2.1.of_nonneg_of_le (fun i => norm_nonneg _) fun n => ?_
    rw [Real.norm_eq_abs]
    exact le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (mul_nonneg hσ.le (by positivity)))
  refine ⟨hσ,fun i => ⟨(price_paths hr i).1,(price_paths hr i).2.1,(price_paths hr i).2.2.trans hv⟩,
    hA,hX,hY,hu,?_,symbol_match (rows_layout (R:=R) rfl) hk hf,
    fun i x => ⟨(hm i x).1.summable,fun l => ((hm i x).2 l).summable⟩,
    fun i x => ⟨(hm i x).1.tsum_eq,fun l => ((hm i x).2 l).tsum_eq⟩⟩
  intro i q
  refine (hk i).of_norm.indicator {k | (R.row i k).2.plaq=q} |>.congr (fun k => ?_)
  simp [Set.indicator,R]

private def vacantAtom (G : Gauge) (n : ℕ) : Atom G n := ⟨fun _ => walkSlot ⟨(0,1),by decide⟩ 0,0⟩

def blank (B : Bed) (G : Gauge) : PathData G := emitBase G B (fun _ => vacantAtom G _) (fun _ => vacantAtom G _) (fun _ => vacantAtom G _)

@[simp] lemma blank_row : (blank B G).row=rowPath B := rfl
@[simp] lemma blank_loop (b : ℕ) : ((blank B G).loop b).coeff=0 := rfl

private lemma vacant_funded (n : ℕ) {σ C : ℝ} (h : 0 ≤ C) :
    SumBudget (fun _ : ℕ => (vacantAtom G n).budget σ) C := by
  have he : (vacantAtom G n).budget σ=0 := by simp [Atom.budget,Atom.magnitude,vacantAtom]
  simp_rw [he]
  exact ⟨fun _ => le_rfl,summable_zero,(tsum_zero.trans_le h)⟩

/-- Pay before installing any curvature n-arities. Hessian does not
charge again when adding those of the right ranks. -/
theorem blank_cap {σ K Λ Ω : ℝ} (hσ : 0 < σ) (hr : B.roots.strip σ Ω)
    (hf : Floor B p 1 η M) (hv : rowPrice σ Ω ≤ K) (hb : 0 ≤ Λ) :
    (blank B G).Bounds p σ K Λ := by
  have hh := price_paths hr (⟨(0,1),by decide⟩:PlaqAxes)
  have he : 0 ≤ K := (tsum_nonneg hh.1).trans (hh.2.2.trans hv)
  have hs (n : ℕ) : (vacantAtom G n).Invariant := by simp [vacantAtom,Atom.Invariant,Atom.poly]
  refine build_cap B hσ hr hf hv (vacant_funded _ hb) (vacant_funded _ he)
    (vacant_funded _ he) (fun _ => ⟨hs 2,hs 3,hs 4⟩) fun i x => ?_
  have H (k) : (blank B G).loop_coeff i x k=0 := by unfold PathData.loop_coeff; split <;> rfl
  change HasSum ((blank B G).loop_coeff i x) _ ∧ ∀ l : Axis, HasSum (fun k => (blank B G).loop_coeff i x k * _) 0
  rw [show (blank B G).loop_coeff i x = 0 from funext H]
  constructor; · exact hasSum_zero
  simp [hasSum_zero]
end YM.Stationary
end
