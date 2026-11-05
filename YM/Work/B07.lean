import YM.Bid.Phase

set_option autoImplicit false
noncomputable section
namespace YM.Work.B07
open Bid Set Filter Function MeasureTheory OS OS.Ground Org Org.Phase Spec Table Word Analysis Extraction
open scoped Topology NNReal InnerProductSpace BigOperators ContDiff ENNReal
variable {G : Gauge} {C : Family G} {S : Table C.book} {V : Chamber S timeAxis} {A : Spread V}
variable (P : Spread.Resolution A) (h : Theme V A) (i : P.X) {n : ℕ}

/-- Evaluate the whole compressed word in one character, with zero off Conf. -/
def state : Table C.book where
  value {n} p x := (P.character i).toAlgHom.toLinearMap.compMultilinearMap (h.array n p x).choose

lemma state_value (p : Caps n) (v : C.book.Vector p) (x : Points n) :
    (state P h i).value p x v = P.character i (depot V A x p v) :=
  congr_arg _ ((h.array n p x).choose_spec v)

lemma state_read (v : Fin n → C.book.Token) {x : Points n} (hx : x ∈ conf n) :
    (state P h i).read x v = P.character i (M A (realize v x) ((realized ..).2 hx)) := by
  rw [Table.read,state_value,depot,dif_pos hx]

lemma state_expect (w : C.book.Word) (hw : distinct w) :
    (state P h i).expect w = P.character i (M A w hw) := by
  rw [expect,state_read P h i _ hw]; congr 1; simp

lemma state_receives (u : Steady V) : P.receives (state P h i) i := by
  intro w hw s d hs
  rw [state_expect P h i _ hw, overline A u w hw s hs]

lemma state_basic : (state P h i).Basic where
  same {n} r {x} hx v := by
    rw [state_read P h i _ (Points.rearrange_in _ hx),state_read P h i _ hx]
    congr 1
    apply h.changes
    let f := fun j => (x j,v j)
    have hf : Injective f := fun _ _ e => (show Injective x.ofLp from hx) (congr_arg Prod.fst e)
    change List.Perm (List.ofFn (f ∘ r)) (List.ofFn f)
    refine (List.perm_ext_iff_of_nodup (List.nodup_ofFn.mpr (hf.comp r.injective))
      (List.nodup_ofFn.mpr hf)).mpr (fun a => ?_)
    simp only [List.mem_ofFn,Function.comp_apply]
    exact ⟨fun ⟨j,e⟩ => ⟨r j,e⟩,fun ⟨j,e⟩ => ⟨r.symm j,by rw [Equiv.apply_symm_apply]; exact e⟩⟩
  trivial f x := by
    rw [state_read P h i f (by change Injective x.ofLp; exact Function.injective_of_subsingleton _)]
    have he (hx : distinct (realize f x)) : M A (realize f x) hx = 1 := (show M A (realize f x) hx = M A [] _ by congr 1).trans h.vacant
    rw [he,map_one]
  unital hx d v := by
    rw [state_read P h i _ hx,state_read P h i _ (Points.tail_in hx), h.unital _ _ _ hx]

lemma state_translation : (state P h i).Homogeneous := by
  intro n x hx s v
  rw [state_read P h i _ (Points.across_in s hx),state_read P h i _ hx, h.offsets s (realize v x)]
  congr 2
  simp only [carry,realize,List.map_ofFn]; rfl

lemma state_rel : (state P h i).respects S := by
  intro d v hv
  rw [(state P h i).criterion]
  intro n B x hx
  rw [front_eq,state_value]
  let t := vals B (0 : C.book.Ref d)
  have he : depot V A x _ (vals B v) = depot V A x _ t := h.pins _ _ _ _ _ (fun j => by
    refine Fin.cases ?_ (fun _ => rfl) j
    change S.project d v = S.project d 0
    rw [map_zero]; exact (Submodule.Quotient.mk_eq_zero _).mpr hv)
  rw [he,← state_value P h i]
  exact MultilinearMap.map_coord_zero _ 0 rfl

variable (X : Spec.Algebra S) (H : S.Hierarchy) (u : Locals X H.spin)

lemma state_turns (hr : ∀ K w (e : distinct w) e', M A w e = M A (Ground.rotate w X.turns K) e') :
    X.turns.Oriented (state P h i) := by
  intro n v x hx K
  change (state P h i).read _ (Ward.expose ∘ X.turns.label K ∘ v) = (state P h i).read x (Ward.expose ∘ v)
  let w := realize (Ward.expose ∘ v) x
  have he : Ground.rotate w X.turns K = realize (Ward.expose ∘ X.turns.label K ∘ v) (Points.move K x) := by
    simp [Ground.rotate,w,realize,List.map_ofFn,Function.comp_def,Points.move]
  have hh : distinct (Ground.rotate w X.turns K) := he.symm ▸ ((realized ..).2 (Points.move_in K hx))
  rw [state_read P h i _ hx,state_read P h i _ (Points.move_in _ hx),hr K _ _ hh]
  congr 2
  exact he.symm

include u in
lemma state_spin (hr : X.turns.Oriented (state P h i)) (hf : Org.Phase.reflects (C:=C) V A) :
    (state P h i).RealSpin where
  mirror {n} s {x} hx v := by
    have ht : X.turns.label s.ortho ∘ S.classTokens ∘ v = S.classTokens ∘ C.book.move s ∘ v := by
      ext1 j
      dsimp only [Rotation.label,comp_apply,classTokens]; congr 1
      exact u.spots.signed ..
    have hy := hr _ (S.classTokens ∘ v) _ hx s.ortho
    rw [ht,at_project S (state P h i) (state_basic P h i).toSymmetric (state_rel P h i) (Points.move_in s.ortho hx),
      at_project S (state P h i) (state_basic P h i).toSymmetric (state_rel P h i) hx] at hy
    exact hy
  real {n} {x} hx v := by
    let w := realize v x
    have hw : distinct w := (realized ..).2 hx
    let w' := realize (C.book.conjugate ∘ v) x
    have hw' : distinct w' := (realized ..).2 hx
    have hh := Grid.apart hw'
    have he : List.Perm (Grid.anti w') (Word.reflect w timeAxis) := by
      rw [Word.reflect,Word.conjugate,List.map_reverse,Word.act,List.map_reverse]
      have hy : w' = w.map (fun p => (p.1,C.book.conjugate p.2)) := by
        simp only [w',w,realize,List.map_ofFn]; rfl
      rw [hy]; exact (List.reverse_perm _).symm
    rw [state_read P h i _ hx,state_read P h i _ hx,← map_star,h.opposite w hw (Word.reflects _ hw),hf w' hw',h.changes he hh (Word.reflects _ hw)]

lemma state_smooth (hP : P.Out) : (state P h i).Smooth := by
  let W : Submodule ℂ V.VacuumOp := A.algebra.toSubalgebra.toSubmodule
  let c : W →L[ℂ] ℂ := { (P.character i).toAlgHom.toLinearMap with cont := hP.values i }
  obtain ⟨g,hg,-⟩ := exists_extension_norm_eq (𝕜 := ℂ) (E := V.D →L[ℂ] V.D) W c
  constructor
  intro n d v
  let y (x : Points n) := depot V A x d v
  have hy : ContDiffOn ℝ ∞ (fun x => (y x).val) (conf n) := h.steep _ (fun j => ⟨d j,v j⟩)
  refine ((g.restrictScalars ℝ).contDiff.comp_contDiffOn hy).congr (fun x _ => ?_)
  exact (state_value ..).trans (hg (y x)).symm

theorem answer : YM.Bid.B07 := by
  intro b G C S V A P X H u h hv hf hP
  have ht i := state_turns P h i X (b V A X.turns X.derivatives H u.motion u.spots h hv hf)
  exact ⟨state P h,⟨fun i => state_receives P h i hv, state_basic P h,
    fun i => state_spin P h i X H u (ht i) hf, state_translation P h,state_rel P h,ht,
    fun i => state_smooth P h i hP⟩⟩
end YM.Work.B07
