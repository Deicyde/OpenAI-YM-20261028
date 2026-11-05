import YM.Euclid.Differential
import YM.Heat.Extend
import YM.OS.Dynamics
import YM.Ward.Ket



/-!
# Exact singleton ket over any germ of a point. Connect Table.Tag derivatives.

Interior strict only. Plants/mirrors use exact tensor adjoint convention.
Projection kernel identities needed for linking. Banach 1D smooth without
helper representation assumed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Ward
open Function Set Filter Complex Analysis OS Word
open scoped Topology NNReal ENNReal InnerProductSpace ContDiff BigOperators
variable {G : Gauge} {L : Register G} {S : Table L} {a b : Axis}

def expose (t : S.Tag) : L.Token := ⟨t.1,S.representative _ t.2⟩
@[simp] theorem sends_back (t : S.Tag) : S.classTokens (expose t)=t := by change ⟨t.1,S.project _ (S.representative _ t.2)⟩=t; rw [S.rep]

lemma resolve {p : L.Plant} {v : L.Word} (S : Table L) : S.expect (p::v) =
    S.read (Points.cons p.1 (positions v)) (Fin.cons p.2 (tokens v)) := by
  have hv : realize (Fin.cons p.2 (tokens v)) (Points.cons p.1 (positions v))=p::v := by
    unfold realize; rw [List.ofFn_succ]
    simp only [Points.cons,points_apply,Fin.cons_zero,Prod.mk.eta]
    congr 1
    simp only [Fin.cons_succ]
    exact rebuilt v
  conv_lhs => rw [← hv]
  exact S.readAt _ _

lemma exact_table {p : L.Plant} {v : L.Word} (h : distinct (p::v)) (ht : S.Hierarchy) : S.expect (p::v) = S.useAt S
    (Points.cons p.1 (positions v)) (Fin.cons (S.classTokens p.2) fun i => S.classTokens (tokens v i)) := by
  rw [resolve,← S.at_project S ht.laws.toSymmetric (fun _ => le_rfl) ?_]
  · apply congr_arg; funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [← Word.realized (v := Fin.cons p.2 (tokens v))]
  suffices he : realize (Fin.cons p.2 (tokens v)) (Points.cons p.1 (positions v))=p::v from he ▸ h
  unfold realize; rw [List.ofFn_succ]; simp only [Points.cons,points_apply,Fin.cons_zero,Prod.mk.eta]
  congr 1; simp only [Fin.cons_succ]; exact rebuilt v

lemma disjoint_table {p : L.Plant} {v : L.Word} (ht : distinct (p::v)) : Points.cons p.1 (positions v) ∈ conf _ := by
  have hw : positions (p::v)=Points.cons p.1 (positions v) := by
    apply PiLp.ext; intro i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [Points.cons, positions]
  rw [← hw]; exact ht

def plant (t : S.Tag) (x : E4) (a : Axis) (h : 0<x a) : Future L a :=
  ⟨[(x,expose t)],⟨locations.mpr (by simp),fun p hp => by simpa only [List.mem_singleton.mp hp] using h⟩⟩

def spot (V : Chamber S a) (t : S.Tag) (x : E4) := if h : 0<x a then V.GNS.plant (plant t x a h) else 0

@[simp] lemma warm (V : Chamber S a) (t : S.Tag) {x : E4} (h : 0<x a) : spot V t x=V.GNS.plant (plant t x a h) := dif_pos h

lemma beside (v : Future L a) {x : E4} (h : 0<x a) (t : S.Tag) : distinct ((x,expose t)::reflect v.val a) := by
  have ht : distinct (reflect v.val a ++ [(x,expose t)]) := twoSides v.property (plant t x a h).property
  exact locations.mpr
    (((List.perm_append_comm : List.Perm (_++_) (_++_)).map Prod.fst).nodup (locations.mp ht))

lemma link (V : Chamber S a) (t : S.Tag) (q : Future L a) (x : E4) (h : S.Hierarchy) (he : 0<x a) :
    inner ℂ (V.GNS.plant q) (spot V t x) =
      S.useAt S (Points.cons x (positions (reflect q.val a))) (Fin.cons t fun i => S.classTokens (tokens (reflect q.val a) i)) := by
  rw [warm V t he,V.GNS.measure]
  change S.expect (reflect q.val a ++ _) = _
  rw [Veq q he]
  rw [exact_table (beside q he t) h]; simp
where
 Veq (q : Future L a) (he : 0<x a) : S.expect (reflect q.val a ++ (plant t x a he).val) = S.expect ((x,expose t)::reflect q.val a) :=
   S.order h.laws.toSymmetric (beside q he t) (@List.perm_append_comm _ [(x,expose t)] _)

abbrev inc (j : Axis) (x : E4) (t : ℝ) : E4 := x+t • basis j
lemma step {x : E4} (hp : 0<x a) (p : ℝ) (hh : b≠a) : 0< inc b x p a := by simp [inc, Ne.symm hh, hp]

lemma forwards {n : ℕ} (j : Axis) (x : E4) (r : Points n) (t : ℝ) :
    HasDerivAt (fun y : ℝ => Points.cons (inc j x y) r) (Points.direction 0 j) t := by
  rw [show (fun y => Points.cons (inc j x y) r) = fun y => Points.cons x r+y • Points.direction 0 j from ?eq]
  · have he := (ContinuousLinearMap.toSpanSingleton ℝ (Points.direction (n := n+1) 0 j)).hasDerivAt (x := t)
    simpa using he.const_add (Points.cons x r)
  case eq =>
    funext y; apply PiLp.ext; intro i; refine Fin.cases ?_ (fun k => ?_) i <;> simp [Points.cons,Points.direction,inc]

variable (V : Chamber S a) (W : DiffPlan S)
lemma slides (s : ℝ≥0) (t : S.Tag) (x : E4) (hx : 0<x a) : spot V t (inc a x s)=V.flow.E s (spot V t x) := by
  rw [warm V _ hx,← V.atBirth, warm V _ (by simp [inc]; positivity)]
  rfl
lemma rests (s : Cross a) (t : S.Tag) (x : E4) (hx : 0<x a) : spot V t (x+s.val)=V.flow.U s (spot V t x) := by
  rw [warm V _ hx,← V.across, warm V _ (by simp [hx, show s.val a=0 from s.property])]
  rfl

lemma light {x : E4} (t : S.Tag) (j : b≠a) (hp : 0<x a) :
    Continuous fun w : ℝ => spot V t (inc b x w) := by
  let f (i : ℝ) : Cross a := ⟨i • basis b,show _ from by change (i • basis b) a=0; simp [Ne.symm j]⟩
  have he : Continuous f := (continuous_id.smul (continuous_const (y := basis b))).subtype_mk _
  rw [show (fun w : ℝ => spot V t (inc b x w))=fun w => V.flow.U (f w) (spot V t x) from funext fun i => rests V (f i) t x hp]
  exact (V.flow.continuousU (spot V t x)).comp he

def rise (b : Axis) (p : S.Tag) : S.Tag := ⟨p.fst+1,W.deriv p.fst b p.2⟩
lemma responds (h : S.Hierarchy) (g : W.Derivatives S) {x : E4} (p : S.Tag) (j : b≠a) (hp : 0<x a) (t : ℝ) :
    HasDerivAt (fun z => spot V p (inc b x z)) (spot V (rise W b p) (inc b x t)) t := by
  apply represents V.GNS (fun z => spot V p (inc b x z)) (fun z => spot V (rise W b p) (inc b x z))
    (light V _ j hp)
  intro u y
  simp_rw [link V p u _ h (step hp _ j)]
  rw [link V (rise W b p) u _ h (step hp y j)]
  let R := positions (reflect u.val a)
  let Y := Points.cons (inc b x y) R
  have hy : Y ∈ conf _ := disjoint_table (beside u (step hp y j) p)
  unfold rise
  rw [g.kernels p.1 b p.2 hy _]
  exact ((hF h (Fin.cons p fun i => S.classTokens (tokens (reflect u.val a) i)) _ hy).hasFDerivAt.comp_hasDerivAt y
    (forwards b x R y))
where
 hF (h : S.Hierarchy) {n : ℕ} (q : Fin n → S.Tag) (x : Points n) (hx : x∈conf _) : DifferentiableAt ℝ (fun y => S.useAt S y q) x :=
    ((S.class_smooth S h.smooth q _ hx).contDiffAt ((conf_open _).mem_nhds hx)).differentiableAt (by simp)

lemma blooms (h : S.Hierarchy) (g : W.Derivatives S) {x : E4} (p : S.Tag) (j : b≠a) (hp : 0<x a) :
    ContDiff ℝ ∞ fun z => spot V p (inc b x z) := by
  apply contDiff_infty.mpr
  intro n
  induction n generalizing p with
  | zero => exact contDiff_zero.mpr (light V p j hp)
  | succ n ih =>
    push_cast
    apply contDiff_succ_iff_deriv.mpr
    have he := (responds V W h g p j hp)
    refine ⟨fun x => (he x).differentiableAt,fun hz => ?_,?_⟩
    · simp at hz
    rw [funext (fun i => (he i).deriv)]
    exact ih _

/-!
 Analytic time via arbitrary start earlier, minimal raw heat. -/
lemma advancing (p : S.Tag) (x : E4) (u : ℝ) (hx : 0 < inc a x u a) :
    AnalyticAt ℝ (fun t => spot V p (inc a x t)) u := by
  let t := u-inc a x u a/2
  have ht : t<u := by unfold t; linarith
  let y := inc a x t
  have hy : 0 < y a := by dsimp only [y,t]; simp only [inc,PiLp.add_apply,PiLp.smul_apply,basis_eq,if_true,smul_eq_mul,mul_one] at *;linarith
  let r := spot V p y
  let k (i : ℝ) := ((i-t:ℝ):ℂ)
  let F (s : ℝ) := V.flow.F (k s) r
  have he := V.flow.localHeat (k u) (show _ from sub_pos.mpr ht)
  have hp : ContDiffAt ℝ ω (fun z : ℂ => V.flow.F z) (k u) := he.contDiffAt.restrict_scalars ℝ
  have hh : AnalyticAt ℝ F u :=
    ( (ContinuousLinearMap.apply ℂ V.GNS.H.space r).restrictScalars ℝ |>.analyticAt _ ).comp
      (hp.analyticAt.comp ((ofRealCLM.analyticAt _).comp (analyticAt_id.sub analyticAt_const)))
  apply hh.congr
  filter_upwards [lt_mem_nhds ht] with i hi
  let z : ℝ≥0 := ⟨i-t,(sub_pos.mpr hi).le⟩
  change V.flow.F (OS.Semigroup.duration z) r = _
  rw [V.flow.roots_heat (t := z) (show (0:ℝ) < z from sub_pos.mpr hi),← slides V z p y hy]
  congr 1
  change x + t • _ + (i-t) • _ = _
  rw [add_assoc, ← add_smul, add_sub_cancel]
end YM.Ward
