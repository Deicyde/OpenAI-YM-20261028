import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Trades
import YM.Progress.JOINT_CALENDAR.Branches
import YM.Push.RELAY_DIFFERENCE.Attaching


/-! # Outright some low-branch corrected suppliers (any trajectory)

D<4. No resetting required for that Crew/Offer clock! We produce
an alternative .Offer directly on the actual path, including terminal
whole-marker value bill & θ/s numerics, no l-side flow or Weak
expansion, any N≥m (and after *all* periods). Can remove inputs here.
Also general endpoint accounting lemma appropriate if .Wire **needn't**
restart; demonstrates commitments on 1 common β. -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Tin
open Function Set Matrix MeasureTheory Filter RG Wilson Lattice Precision Pressure Supply Bid Craft Tree Bloch
    Labels Source Org Input Marker Overlay Next.Extract Extraction Cells Push.Common
    Push.Corrected Endpoint
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge}
section bands
variable {V : Type*} [Fintype V] [DecidableEq V]
  {W : Census V} {n : Side} {R : Rep G n}

abbrev freeBand (f : V→Site n) (v : V) : Bands W R where
  origins := f
  units := 0
  support _ := Finset.univ
  rays _ := W.fire v
  H := 0
  marks _ _ := W.fire v
  entries := 0

omit [Fintype V] in
lemma vacant (v : V) (f : V→Site n) (w : V → ℝ) (hw : ∀ i, 0 < w i) :
    Endpoint.Value (freeBand (W:=W) (R:=R) f v) w 0 0 0 := by
  refine ⟨hw,fun _=> Finset.singleton_nonempty _,fun _ _ _=> Finset.mem_univ _,fun _=>measurable_const,fun _ _ _ _=> rfl,fun _ _ _=> rfl,fun _ _ => Finset.singleton_nonempty _, fun _ _ h=> (h rfl).elim,fun _ _ _ _ _ _=>rfl,
    fun _ _ _ h => (h rfl).elim,fun _ _=>measurable_const,fun _ _ _ _=> rfl, ?_,⟨0,?_,?_⟩,⟨0,?_,?_⟩⟩
  all_goals simp [SumBudget]

lemma none (v : V) (f : V→Site n) (U : Config G n) {k δ : ℝ} (he : R.activities.Valid R.p δ k) :
    (freeBand (W:=W) (R:=R) f v).density U=Marker.Poly.send W.quiet (R.eval U:ℂ) := by
  let b : Bands W R := freeBand f v
  have hm (Y : Support n) : masked R.p.threshold Y (0:Config G n → ℂ) U=0 := by
    by_cases h : Healthy R.p.threshold Y U; simp [masked_eq _ _ _ _ h]; simp [masked_ne _ _ _ _ h]
  have hb : ∀ i, b.each i U= Marker.Poly.bead W (R.activities.K i U:ℂ) := by
    intro i; simp only [b,Bands.each,Bands.tagged,Pi.zero_apply,Poly.send_zero,tsum_zero,add_zero]
    rfl
  have ht (l : Finset ℕ) : b.packet l U= Poly.bead W (R.activities.gasOccurrence R.p l U:ℂ) := by
    -- instances might classical mismatch
    change (if R.activities.admissible R.p U l then _ else _)=Poly.bead W (R.activities.gasOccurrence R.p _ _:ℂ)
    simp_rw [hb]; rw [← map_prod,← Complex.ofReal_prod]; unfold Activities.gasOccurrence
    split <;> simp
  have hx : b.cluster U=(Poly.bead W) (R.activities.gas R.p U:ℂ) := by
    unfold Bands.cluster Activities.gas; simp_rw [ht]; rw [Complex.ofReal_tsum]
    have hL := Activities.gasSeries he |>.summable U
    let B : ℂ →L[ℂ] Poly W := {
      toFun := Poly.send W.quiet, cont := Bands.sends W.quiet
      map_add' x y := (Poly.bead W).map_add x y
      map_smul' x y := by ext i; simp }
    exact (ContinuousLinearMap.map_tsum B (Complex.ofRealCLM.summable hL)).symm -- direction
  unfold Bands.density; change _ • (Poly.pass (b.extra U) * (b.cluster U)) = _
  have hg : Poly.pass (0: Marker.Poly W) = 1 := by
    unfold Poly.pass; rw [Finset.sum_eq_single 0]; simp
    · intro i _ hi; simp [zero_pow hi]
    simp
  rw [hx, show b.extra U=0 by simp only [b,Bands.extra,Bands.ray,Pi.zero_apply,Poly.send_zero,hm,Finset.sum_const_zero,tsum_zero,add_zero],hg,one_mul]
  ext i; simp only [Poly.bead,RingHom.coe_mk,MonoidHom.coe_mk,OneHom.coe_mk,Poly.part_smul,Poly.part_send,Rep.eval, Complex.ofReal_mul]; split <;> simp
end bands

variable {C : Family G} {S : Table C.book} {d k N p : ℕ} {X : Columns C S d} (Y : Tests X) (hG : G.Simple)

include hG




omit hG in
lemma front1 {L : Register G} {T : Table L} (h : T.Basic) (x : Points 1) (d : ℕ) :
    T.useAt T (n:=1) x (Fin.cons ⟨d,T.unit d⟩ Fin.elim0) = 1 := by
  rw [T.at_unit h (show x∈conf (0+1) from fun (u v : Fin 1) _ => Subsingleton.elim u v)]
  have he : (Fin.elim0 : Fin 0 → T.Tag)=T.classTokens ∘ (Fin.elim0 : Fin 0 → L.Token) := funext (fun i=>Fin.elim0 i)
  rw [he,T.at_project _ h.toSymmetric (fun _=>le_rfl) (show x.tail ∈ conf 0 from fun i=> Fin.elim0 i), h.trivial]

omit hG in
lemma front2 {L : Register G} {T : Table L} (h : T.Basic) (x : Points 2) (he : x∈conf 2) (d : ℕ) :
    T.useAt T x (Fin.cons (α:=fun _=>T.Tag) ⟨d,T.unit d⟩ (Fin.cons ⟨d,T.unit d⟩ Fin.elim0))=1 :=
  (T.at_unit h he (Fin.cons ⟨d,T.unit d⟩ Fin.elim0) d).trans (front1 h x.tail d)

include Y








-- No need to change Wire r & k to use original lens all m
omit hG Y
variable (C)
abbrev minimum (o : ℕ) := (C.path.levels.clock.hatBeta o /2)
abbrev threshold (o : ℕ) := (C.path.levels.budget o).threshold
abbrev linearP (o : ℕ) := minimum C o * (C.path.levels.params o).clip.linear * (threshold C o)^2 /4

lemma β_min (o : ℕ) : 0 < minimum C o := half_pos (zero_lt_one.trans (C.path.levels.fits.delayed o))
lemma κ_pos (o : ℕ) : 0 < linearP C o := by
  unfold linearP; have h := β_min C o; have hg := (C.path.levels.params o).clip.tail_pos; have hT : 0<threshold C o := (C.path.levels.budget o).threshold_pos
  positivity



abbrev advance (o : ℕ) :=
    let b := C.path.levels.budget o
    let p := C.path.levels.params o
    let L := C.path.levels.clock
    let t := 2*L.hatBeta o
    let l := linearP C o
    2*(L.allowance o+PathData.loopsPrice b t p.paths (L.loopCap o))+t*(baseBudget p.clip p.paths (threshold C o))+Fintype.card PlaqAxes*(4*l)+L.forcedAllowance o+3*Real.log (multiplier G l)



variable {C}
lemma lens {n : Side} {V : Type*} [Fintype V] [DecidableEq V] (T : Tiling n) (U : Config G n) (v : Finset (T.Cell×V)) (hv : v.Nonempty) :
    Marks.part (Marks.replicate T (fun _ => 1) U) v=0 := by
  rw [Marks.divides]; obtain ⟨⟨i,j⟩,hi⟩ := hv
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  have he : j ∈ Marks.fibre v i := by simp [Marks.fibre,hi]
  have hm : (Marks.mode (Marks.fibre v i)) ≠ (Marks.all V).quiet := fun H => by rw [show Marks.fibre v i=∅ from congr_arg Subtype.val H] at he; simp at he
  unfold Tiling.copy Marks.part; simp [Poly.one_part,hm]


-- schedule-free Price for constant low branch. Q unbounded through k; W can be picked even larger
-- arbitrarily at no H cost (since full pattern=1). No analogous claim THROUGH d=4!
def prices (Z : Series C) : Push.Corrected.Prices where
  since k := threshold C (Z.side k)
  rate k := linearP C (Z.side k)
  Q k := advance C (Z.side k)
  W k := Real.exp (|advance C (Z.side k)|+k)
  tiny k := (C.path.levels.budget _).threshold_pos
  little k := (C.path.levels.budget _).threshold_le
  weight k := Real.one_le_exp (add_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
  margin k := κ_pos ..
  runs := by
    have hT : Tendsto (fun k : ℕ => Real.exp (- (k:ℝ))) atTop (𝓝 0) := by
      simp_rw [Real.exp_neg]; exact tendsto_inv_atTop_zero.comp (Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop)
    apply squeeze_zero (fun t => div_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) _ hT
    intro k
    rw [div_le_iff₀ (Real.exp_pos _),← Real.exp_add]
    refine Real.exp_monotone ?_; linarith only [le_abs_self (advance C (Z.side k))]

include Y hG




/- Weaker pack. Compiler.Scope only d≥4 requests now. -/
open Joint
omit Y hG
variable {Y' : Joint.Comparator C} {V : Type*} {U : Supply.Sheet G} {s : Supply.Rolls U} (L : Timing.Increments s)
structure Capsule (L : Timing.Increments s) (Y' : Joint.Comparator C) (f : Extraction.Order) where
  γ : ℝ
  couples : L.e < γ
  extent : ℕ → ℝ
  offer d : 4 ≤ d → Recruit.Makes (Joint.phantom C) Y'.a.kernels.spin (Bel.viaAll Y'.a.kernels.positive (0:Axis)) d f L.α γ (extent d)

variable (C)


variable {C}

end YM.Further.PhysicalPeriodLimitF933.Tin
