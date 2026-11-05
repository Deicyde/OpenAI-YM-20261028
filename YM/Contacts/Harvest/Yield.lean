import YM.Contacts.Harvest.Route
import YM.Contacts.Score.Wings
/-!
# Scores of the Wilson family & grading

o(w,x) placement plus offsets; only use at the actual ambient stages which contain the full
active normal blocks. The projection onto an engineering-grade follows the field registration
with its own displayed horizon, independent of choices of angle-subpartition or subsequent branch
and tests. Even choose vectors varying with external parameters without recomputing costs. This
is a multilinearized system with assigned grade upper limits. Use with actual grade basis or
linear extension at those grades; not an identity at a contact if changing the assignments.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Contacts.Harvest
open Function Filter Set Metric MeasureTheory Table OPE Normal
open scoped Topology ContDiff Classical BigOperators
variable {G : Gauge} {L : Register G}{S : Table L}{M' : DiffPlan S}
variable {E W I : Type} {k : ℕ}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
abbrev Letter (M' : DiffPlan S) := E4 × Mode M'
local notation "GN" => Normal.Group k
/-- Field display lists with fixed physical engineering grades. No compactness/finite horizon in the definition of the prescription. -/
abbrev Cells (S : Table L) (d : Fin k→ℕ) := (i:Fin k) → S.Field (d i)
def basisCells (M : Devices M') (d : Fin k→ℕ) (c : Cells S d) := ∀ i,c i∈ M.splitting.stratum (d i)
/-- number of projected grades at point of Taylor operation. -/
def levels (d : Fin k→ℕ) (i : Normal.Group k) := (i.sum d)+1-System.relative i
abbrev Way (d : Fin k→ℕ) (i : Normal.Group k) := Option (Fin (levels d i))
def wind (M : Devices M')(d : Fin k→ℕ) (i : Normal.Group k) (v : Way d i)(x:E4) : Expression M'→ₗ[ℂ] Expression M':= v.elim (LinearMap.id - ∑ j:Fin (levels d i), M.insertRow x j) (fun j=> M.insertRow x j)
def testPlan (P : E→ₗᵢ[ℝ] Points k) (d : Fin k→ℕ) (i : Normal.Group k)(v : Way d i)(s:ℝ) := v.elim (1:Optical E) (fun w=> deviation (normalOn P i) s ((levels d i)-1-w.val))
/-- reading against residues (vote.projected=false) only operates in original test support. -/
abbrev outward {d : Fin k→ℕ} {i : Normal.Group k} (v : Way d i) : Bool := v.isSome
lemma turned {d : Fin k→ℕ}(M : Devices M')(i : Normal.Group k)(x : E4) {w : ℕ} (h : levels d i=w+1) : wind M d i none x= M.residue x w:= by
    apply LinearMap.ext; intro e; change e-(∑ j:Fin (levels d i), M.insertRow x j) e=e-M.replaceAt x w e; rw [h,LinearMap.sum_apply,M.replace_sum] -- rewriting motives?
lemma straight (M : Devices M') (d : Fin k→ℕ)(i : Normal.Group k)(h : levels d i=0)(x:E4) : wind M d i none x= LinearMap.id:= by change LinearMap.id - _ = _; rw [show (∑ j:Fin (levels d i), M.insertRow x j)=0 from ?_,sub_zero]; rw [h]; simp

variable (M : Devices M') {P : E→ₗᵢ[ℝ] Points k}
/-- Components of the score at actual placements; not test distribution data. -/
def waySystem (P : E→ₗᵢ[ℝ] Points k) (M : Devices M') (o : Points k) (d : Fin k→ℕ) (c : Cells S d) : System E (Expression M') k :=
   ⟨d, fun i w x=> M.insertRow (centroid i (P x+o)) w, fun i x=> insertField M.basis ((P x+o) i) (d i) (c i)⟩
namespace Route
variable {g : Normal.Group k} {Q : Pieces g} (r : Route P Q I W) {d : Fin k→ℕ}(c : W → Cells S d) (w : W) (i : Normal.Group k)(x:E)
/-- physical center (fixed in Taylor & projection). -/
def oculus := centroid i (r.actualAt w x)
def components := waySystem P M (r.offset w) d (c w)
lemma core_field (j : Fin k) : (r.components M c w).field j x= insertField M.basis (r.actualAt w x j) (d j) (c w j):= rfl
lemma core_reader (j : ℕ) : (r.components M c w).reader i j x= M.insertRow (r.oculus w i x) j:=rfl
lemma core_wind (v : Way d i) : (r.components M c w).treatment i v x= wind M d i v (r.oculus w i x):= by
   cases v
   · change LinearMap.id-(∑ j:Fin ((r.components M c w).depth i),(r.components M c w).reader i j) x=_; rw [Finset.sum_apply]; rfl
   rfl
lemma core_mask (v : Way d i) : (r.components M c w).maskAt P (r.length w) i v=testPlan P d i v (r.length w):= by cases v <;> rfl
lemma oculus_still {q : Normal.Group k} (y:E)(hx : x-y∈ normalOn P q) (he : q=i ∨ Disjoint q i): r.oculus w i x=r.oculus w i y:= by
   simp_rw [oculus,actualAt,map_add,add_left_inj]; apply sub_eq_zero.mp; rw [← map_sub,← map_sub]; have hm : P (x-y) ∈ plane q:= hx
   rcases he with h|he; subst q; exact hm|>.1
   rw [centroid_formula]; rw [Finset.sum_eq_zero (fun x hh=> (plane_iff.mp hm).2 x (fun h=>Finset.disjoint_left.mp he h hh)),smul_zero]
lemma actual_continuous : Continuous (r.actualAt w) := P.continuous.add continuous_const
lemma oculus_continuous : Continuous (r.oculus w i) := (centroid i).continuous.comp (r.actual_continuous w)
lemma offset_still (j : Q.parts) (i : Nails j.val) : centroid i.val (r.offset w)=centroid j.val (r.offset w) := centroid_same i.property.2 _ _ (fun k hk=>r.aligned w j.val j.property k (i.property.1 hk))
lemma oculus_values (j : Q.parts)(i : Nails j.val): r.oculus w i.val x= centroid i.val (P x)+ centroid j.val (r.offset w):=by rw [oculus,actualAt,map_add,r.offset_still w j i]
lemma oculus_diff (j : Q.parts)(i : Nails j.val) (l : Nails j.val): r.oculus w i.val x-r.oculus w l.val x= centroid i.val (P x)-centroid l.val (P x):=by rw [r.oculus_values w x j i,r.oculus_values w x j l]; abel
lemma oculus_extent (i : Q.parts)(l : Nails i.val) : ‖r.oculus w l.val x-r.oculus w i.val x‖ ≤ ‖(normalOn P i.val).starProjection x‖:= by
   rw [show r.oculus w l.val x-r.oculus w i.val x=_ from r.oculus_diff w x i l ⟨i.val,by rfl,Q.nonempty_of_mem_parts i.property⟩]; exact cohort_bounds (r.displaysNormals i.val i.property) x l.property.1 l.property.2
end Route
end YM.Contacts.Harvest
