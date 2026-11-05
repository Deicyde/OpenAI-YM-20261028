import YM.Extension.UV.Station.Cluster
import YM.Push.PRICE_COMPILER.PathBudget
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Extension.UV.StationaryData
open Function Set Filter Lattice RG Laurent Bloch Precision Wilson Push.PriceCompiler
open scoped Topology BigOperators Classical
local instance : Infinite Slot:=many_slots
abbrev roster:ℕ ≃ Slot:=Stationary.enumerate _
variable {G:Gauge}
def payload (x:BookKey G → ℝ) (k:Fin 3) : ℕ→Atom G (k.val+2):= by
  haveI : NeZero (k.val+2) := ⟨by omega⟩
  exact fun i=>⟨slots _ i,fun b=> x (.inr ⟨k,b,slots _ i⟩)⟩

def book_path (f:BookKey G →ℝ): PathData G where
   row :=fun b i=> (f (.inl (b,roster i)),roster i)
   loop:=payload f 0
   cubic:=payload f 1
   quartic:=payload f 2

-- all proofs below only claim pointwise sums or germs when path budgets exist, not identity of label dictionaries
variable (R : PathData G) {p:Clip} {t A L:ℝ} (h : R.Bounds p t A L)
abbrev compactify := book_path (book_get R)

section basic
include h
lemma compact_mass : PathMass (compactify R) t A L A A:= ⟨h.width, fun i=>Stationary.budget_copy roster (row_budget R h i), reatom_wall R.loop h.two, reatom_wall R.cubic h.three, reatom_wall R.quartic h.four⟩
lemma ell_eq {n:Side} (U:Config G n)(b:Face (Per n)): (compactify R).ell U b=R.ell U b:= by
   let a:= fun i : ℕ=> (R.row b.2 i).2
   have he: ∀ i:ℕ,(compactify R).ellTerms b i U=∑' j:{j//a j=roster i}, R.ellTerms b j U:=by
     intro i
     change (∑' j : a ⁻¹' {roster i}, (R.row b.2 j).1) • ((roster i).atSite U b.1)=_
     have ha : Summable fun i=> (R.row b.2 i).1:= by refine Summable.of_norm ((h.rows b.2).2.1.of_nonneg_of_le (fun i=>norm_nonneg _) (fun j=>?_)); exact le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (mul_nonneg h.width.le (Nat.cast_nonneg _)))
     rw [← ((show Summable (fun j:a⁻¹' {roster i}=>(R.row b.2 j).1) from by exact ha.subtype _)).tsum_smul_const]
     exact tsum_congr (fun j=> by change _= (R.row b.2 j).1 • (a j).atSite U b.1; rw [j.2])
   simp_rw [PathData.ell,he]
   exact (roster.tsum_eq (fiber a (fun j=>R.ellTerms b j U))).trans ((fiber_tsum a ((R.ell_dominated h b).summable U)).tsum_eq)

lemma intended_eq {n:Side}(U:Config G n): mainTerm p (compactify R) U= mainTerm p R U:= by
   suffices hh : ∀ V:Config G n, quadratic p (compactify R) V=quadratic p R V from by
     unfold mainTerm; simp_rw [hh]
     apply congr_arg
     funext s
     rw [show uncut ((compactify R).cubic) _=uncut _ _ from reatom_uncut R.cubic h.width.le h.three _,show uncut ((compactify R).quartic) _=uncut _ _ from reatom_uncut R.quartic h.width.le h.four _]
   simp [quadratic,ell_eq R h]

lemma second_eq {n:Side}(U:Config G n): secondTerm p (compactify R) U=secondTerm p R U:=by simp [secondTerm,quadratic,ell_eq R h]
lemma loop_eq {n:Side}(U:Config G n): loop (compactify R) U=loop R U := by unfold loop; exact congr_arg Patch.average (funext (fun x => reatom_uncut R.loop h.width.le h.two (pull x 0 U)))
end basic

lemma pattern_moments {k:ℕ} {y: Fin k → PlaqAxes} (b : Atom G k) (s:Pattern k) (hs:b.leg=s) : (fun i=>(b.leg i).plaq)=y ↔ (fun i=>(s i).plaq)=y:= by rw [hs]
include h in
lemma symbol_eq b q: (compactify R).symbol0 b q=R.symbol0 b q:= by
   let f k:= if (R.row b k).2.plaq=q then (R.row b k).1 else 0
   let z k:= (R.row b k).2
   have hx:= (fiber_tsum z (show Summable f from h.symTerms b q)).tsum_eq
   refine Eq.trans ?_ ((roster.tsum_eq (fiber z f)).trans hx)
   apply tsum_congr; intro i
   change (if (roster i).plaq = q then book_row R b (roster i) else 0) = _
   split_ifs with hh
   · apply tsum_congr; intro j; replace hh:= (j.2 |> congr_arg Slot.plaq).trans hh; exact (if_pos hh).symm
   unfold fiber; trans ∑' _ : z⁻¹' {roster i}, (0:ℝ)
   · simp only [tsum_zero]
   exact tsum_congr (fun j=>(if_neg (by change (z j).plaq ≠ _; rw [j.2]; exact hh)).symm)

open PathData
include h in
lemma loop_normal : (compactify R).loop_jets:= by
   let s i:=(R.loop i).leg; let u : ℕ ≃ Pattern 2:=slots _
   have hv i b y: loop_coeff (compactify R) b y i = fiber s (R.loop_coeff b y) (u i):= by
     unfold loop_coeff; change (if (fun p:Fin 2=>(u i p).plaq)=b then _ else _)=_
     split_ifs with hh
     · apply tsum_congr; intro j; exact (if_pos ((pattern_moments (s:=u i) (y:=b) (b:=R.loop j) (show s j=u i from j.2)).2 hh)).symm
     unfold fiber; trans ∑' _ : s⁻¹' {u i}, (0:ℝ)
     · simp only [tsum_zero]
     exact tsum_congr (fun j=>(if_neg (hh ∘ (pattern_moments (R.loop j) (u i) j.2).1)).symm)
   intro i y
   let z := R.loop_coeff i y
   have hx := u.tsum_eq (fiber s z)
   simp_rw [hv]
   rw [hx,(fiber_tsum s (h.loopTerms _ _).1).tsum_eq]
   refine ⟨(h.loop_normal ..).1,fun l=>?_⟩
   let v (t:Pattern 2) :=(((t 1).offset l-(t 0).offset l:ℤ):ℝ)
   change (∑' j, fiber s z (u j)*v (u j))=0
   simp_rw [show ∀ j, fiber s z (u j)*v (u j)=fiber s (fun i=> z i * v (s i)) (u j) from fun k=>by rw [fiber,← tsum_mul_right]; exact tsum_congr (fun t=> by change z t.val * _=z t.val * _; exact congr_arg (z t.val * v ·) t.2.symm)]
   rw [u.tsum_eq,(fiber_tsum s (h.loopTerms i y|>.2 l)).tsum_eq]; exact (h.loop_normal i y).2 l
include h in
lemma compact_bounds : (compactify R).Bounds p t A L:= by
   apply PathMass.bounds (compact_mass R h) ⟨_,_,loop_normal R h⟩ le_rfl le_rfl le_rfl
   · exact fun i=> ⟨reatom_invariant R.loop h.width.le h.two (fun i=>(h.invariant i).1) i,reatom_invariant R.cubic h.width.le h.three (fun i=>(h.invariant i).2.1) i,reatom_invariant R.quartic h.width.le h.four (fun i=>(h.invariant i).2.2) i⟩
   unfold metric_zero; simp_rw [symbol_eq _ h]; apply h.metric
end YM.Extension.UV.StationaryData
