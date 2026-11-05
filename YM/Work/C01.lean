import YM.Analysis.Polydisc
import YM.Bid.Corners

/-!
# Centered insertions on the common Union via all-spectator matrix elements
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.C01
open Function OS Word Boundary Bid
open scoped NNReal InnerProductSpace

variable {G : Gauge} {L : Register G} {S T : Table L}
variable {V : Chamber T timeAxis}

lemma op_ext {M N : V.H.Op}
    (h : ∀ x y, inner ℂ (V.GNS.plant x) (M (V.GNS.plant y)) = inner ℂ (V.GNS.plant x) (N (V.GNS.plant y))) :
    M = N := by
  apply V.GNS.by_bud
  intro y
  apply V.GNS.whole.eq_of_inner_right ℂ
  intro x
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add,inner_add_left,hf,hg]
  | single i c => simp only [Kernel.Gram.stems,Finsupp.linearCombination_single,inner_smul_left,h]

def center (p : ℝ≥0) (v : L.Token) : L.Plant := (position 0 p,v)

theorem centerTime (p : ℝ≥0) (v : L.Token) : (center p v).1 timeAxis = (p:ℝ) := time_position _ _

lemma centeredSlab (p : ℝ≥0) (v : L.Token) (h : 0 < p) : Slab timeAxis (p+p) [center p v] := by
  have hv : 0 < (p:ℝ) := h
  refine ⟨add_pos h h,⟨locations.mpr (by simp),?_⟩,?_⟩ <;>
    simpa only [List.mem_singleton,forall_eq,centerTime,NNReal.coe_add,lt_add_iff_pos_right] using hv

lemma centeredBuffer (p : ℝ≥0) (v : L.Token) : OS.buffer timeAxis p (p+p) [center p v] := by
  refine ⟨?_,?_⟩
  · intro i j h
    exact (h (Subsingleton.elim (α := Fin 1) i j)).elim
  simp [centerTime]

def spectators (p : ℝ≥0) (x y : Future L timeAxis) : L.Word := reflect x.val timeAxis ++ raised timeAxis (p+p) y.val

lemma cleared {p : ℝ≥0} (v : L.Token) (hp : 0 < p) (x y : Future L timeAxis) :
    distinct (center p v :: spectators p x y) := by
  have he : distinct (reflect x.val timeAxis ++ center p v :: raised timeAxis (p+p) y.val) :=
    twoSides x.property (entering (centeredSlab p v hp) y).property
  exact locations.mpr ((List.perm_middle.map Prod.fst).nodup (locations.mp he))

lemma inner_raw (A : Spread V) (ht : T.Symmetric) {p : ℝ≥0} (hp : 0<p) (q : L.Token) (x y : Future L timeAxis) :
    inner ℂ (V.GNS.plant x) (A.place (p+p) [center p q] (V.GNS.plant y)) =
      T.read (Points.cons (position 0 p) (positions (spectators p x y))) (Fin.cons q (tokens (spectators p x y))) := by
  rw [A.reads (centeredSlab p q hp), V.GNS.measure]
  change T.expect (reflect x.val timeAxis ++ center p q :: raised timeAxis (p+p) y.val) = _
  rw [T.order ht (cleared q hp x y) List.perm_middle.symm]
  exact Ward.resolve T

lemma inner_quotient (A : Spread V) (ht : T.Symmetric) (hr : T.respects S) {p : ℝ≥0} (hp : 0<p) (v : S.Tag)
    (x y : Future L timeAxis) : inner ℂ (V.GNS.plant x) (A.place (p+p) [center p (Ward.expose v)] (V.GNS.plant y)) =
      S.useAt T (Points.cons (position 0 p) (positions (spectators p x y)))
        (Fin.cons v (S.classTokens ∘ tokens (spectators p x y))) := by
  have he : Points.cons (position 0 p) (positions (spectators p x y)) ∈ conf _ :=
    Ward.disjoint_table (cleared (Ward.expose v) hp x y)
  rw [inner_raw A ht hp, ← S.at_project T ht hr he]
  apply congr_arg
  funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- Each finite level gives an algebraically linear map, by placing the variable plant in the
second (linear) side of the Gram elements. -/
def single (A : Spread V) (ht : T.Symmetric) {p : ℝ≥0} (hp : 0<p) (d : ℕ) : S.Field d →ₗ[ℂ] V.H.Op where
  toFun v := A.place (p+p) [center p (Ward.expose ⟨d,v⟩)]
  map_add' v w := by
    apply op_ext; intro x y
    rw [add_apply, inner_add_right]
    simp only [inner_raw A ht hp, Ward.expose, ← Table.head_read, map_add]
  map_smul' c v := by
    apply op_ext; intro x y
    simp only [RingHom.id_apply, smul_apply, inner_smul_right,inner_raw A ht hp, Ward.expose,
      map_smul, ← Table.head_read, smul_eq_mul]

lemma singles_agree (P : DiffPlan S) (A : Spread V) (ht : T.Symmetric) (hr : T.respects S) (HI : P.Inclusions T)
    {p : ℝ≥0} (hp : 0<p) : P.compatible (single A ht hp) := by
  intro d e h v
  apply op_ext; intro x y
  change inner ℂ _ (A.place _ [center p (Ward.expose (⟨e,_⟩ : S.Tag))] _) =
    inner ℂ _ (A.place _ [center p (Ward.expose (⟨d,_⟩ : S.Tag))] _)
  rw [inner_quotient A ht hr hp, inner_quotient A ht hr hp]
  exact HI.kernels h v (Ward.disjoint_table (cleared (Ward.expose (⟨d,v⟩ : S.Tag)) hp x y)) _

lemma at_width (P : DiffPlan S) (A : Spread V) (H : Pantry S T V P A) (p : ℝ≥0) :
    ∃ f : S.Union →ₗ[ℂ] V.H.Op, ∀ d v, 0<p → f (S.pin d v) = A.place (p+p) [center p (Ward.expose (⟨d,v⟩ : S.Tag))] := by
  by_cases h : 0<p
  · obtain ⟨f,hf⟩ := (P.uniqueLift H.head.laws.toSymmetric H.rises (single A H.adopted.laws.toSymmetric h)
      (singles_agree P A H.adopted.laws.toSymmetric H.present H.habits h)).exists
    exact ⟨f,fun d v _ => hf d v⟩
  exact ⟨0,fun _ _ hp => (h hp).elim⟩

theorem answer : YM.Bid.C01 := by
  intro G L S T V P A H
  choose f hf using at_width P A H
  let B : Small S V := ⟨f⟩
  refine ⟨B,fun d v p hp => hf p d v hp,?_⟩
  intro v
  obtain ⟨d,w,rfl⟩ := P.covered H.head.laws.toSymmetric H.rises v
  let t : L.Token := Ward.expose (⟨d,w⟩ : S.Tag)
  obtain ⟨C,K,hC,hCK⟩ := H.counter.cap d ‖t.2‖
  refine ⟨C,K,hC,?_⟩
  intro p hp
  change ‖f p _‖ ≤ _; rw [hf p d w hp.1]
  have hc : constrained d ‖t.2‖ [center p t] := by
    intro i hi
    obtain rfl := List.mem_singleton.mp hi
    exact ⟨le_rfl,le_rfl⟩
  have he := hCK _ _ hc (centeredSlab p t hp.1) p (show 0 < (p:ℝ) from hp.1) (show (p:ℝ) ≤ 1 from hp.2.le)
    (centeredBuffer p t)
  simpa only [Spread.radius,List.length_cons,List.length_nil,Nat.zero_add,Nat.cast_one,pow_one,mul_one,one_div] using he

end YM.Work.C01
