import YM.Extra.SOURCE_HISTORIES.ColumnStep
import YM.Extra.SOURCE_HISTORIES.Rebase


/-!
# ONE shared linear column family step

Coarse reference coordinate isn't obtained by fitting an expectation.
Rebase using injectivity of the **previous** readout, spend the atoms on
the *complete* column, then choose once and linearly combine the entire
paid column, incl forced parts. Necessary for a cone step: bounds are in
terms of *current* primary size (and remainders), not the sum of unsubtracted
uses of possibly huge original coefficients at earlier bases. Reserve K,
roomCost and Bank for true swollen costs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Histories
open Lattice Wilson RG Source Function Filter Set MeasureTheory Bid Labels Motion
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {d : ℕ} {F : Labels.Frame G d}
variable (B : SectionData F) (H : History G) (N p : ℕ) (A : Hol G)


structure Voice (F : Labels.Frame G d) (H : History G) (p m : ℕ) where
  plays : F.Coeff → Coefficient F (H.S.side m p)
  charge : F.Coeff → ℝ
  index : F.Coeff ≃ₗ[ℂ] F.Coeff

/-- All line/read claims are for the SAME history witness. -/
structure Heard (m : ℕ) (V : Voice F H p m) : Prop where
  book : Ledger F _ V.plays
  earns v : (V.plays v).Format 0 A (H.rep N p m) ∧ (V.plays v).remBound 0 (H.rep N p m)
    (Real.sqrt (H.levels.clock.forcedAllowance m)) (V.charge v)
  currents v : (V.plays v).x = V.index v
  cone v : V.charge v ≤ (H.levels.params m).columns * F.coeffSize (F.core (V.index v))
  summed i j : V.charge (i+j)≤V.charge i+V.charge j
  moves v y : Motion.patch F y (V.index v)=V.index (Motion.patch F y v)
  unit : V.index (unitVec F H N) = unitVec F H m
  values : IsLinearMap ℂ (fun v => (V.plays v).density 0 B (H.rep N p m))
  travels v y : dance y ((V.plays v).density 0 B (H.rep N p m))=
    (V.plays (Motion.patch F y v)).density 0 B (H.rep N p m)

variable (W : Worth)

structure Buys (H : History G) (F : Labels.Frame G d) (W : Worth) (m : ℕ) (C η : ℝ) : Prop where
  cost : 1 ≤ C
  epsilon : 0 ≤ η
  tiny : η*(1+(H.levels.params (m+1)).columns)*orbitCost F ≤ barunit (H.S.block m)
  funds : (C+η*(H.levels.params (m+1)).columns)*orbitCost F ≤ W.K (H.levels.clock.J (m+1))

structure Responds (m : ℕ) (V : Voice F H p (m+1)) (Q : Voice F H p m) : Prop where
  values v : (Q.plays v).density 0 B (H.rep N p m) = blast H N p m d ((V.plays v).density 0 B (H.rep N p (m+1)))
  tally v : direction H W m F ((Q.plays v).x) ((V.plays v).x) (Q.charge v) (V.charge v)

omit A in
private theorem blast_linear (m : ℕ) {f : F.Coeff → Config G (H.S.side (m+1) p) → ℂ} (h : IsLinearMap ℂ f)
    (hF : ∀ v, Integrable (f v) (prior G _)) : IsLinearMap ℂ fun x => blast H N p m d (f x) := by
  constructor
  · intro x y
    simp only [blast,h.map_add,StepData.push_add (H.levels.transition_mass ..) _ _ (hF _) (hF _),smul_add]
  intro c y
  simp only [blast,h.map_smul,StepData.push_smul _ _ _ _ (hF _), smul_comm c]

lemma budgets_orbit (F : Labels.Frame G d) (L : Side) (T : Heading F) (X : F.Index → F.Coeff) (v : F.Coeff) (e : ℝ)
    (he : 0 ≤ e)
    (ht : ∀ (i : Tally F), F.coeffSize (Motion.patch F i.1 (X i.2) - Motion.patch F i.1 (T.leads L (Size.axis F i.2))) ≤
      e * F.coeffSize (F.core (Size.axis F i.2))) :
    F.coeffSize (repaint F X v - T.leads L v) ≤ e * orbitCost F * F.coeffSize (F.core v) := by
  rw [← repaint_same F (T.leads L) (fun x m => (T.coheres L m x).symm) v]
  unfold repaint
  rw [← Finset.sum_sub_distrib]
  simp_rw [← smul_sub]
  refine le_trans (Size.finite F _ _) ?_
  calc
    _ ≤ ∑ i : Tally F, ‖chips F v i‖ * (e * F.coeffSize (F.core (Size.axis F i.2))) :=
      Finset.sum_le_sum fun i _ => by rw [Size.smul]; exact mul_le_mul_of_nonneg_left (ht i) (norm_nonneg _)
    _ = e * ∑ i : Tally F, ‖chips F v i‖ * F.coeffSize (F.core (Size.axis F i.2)) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left (core_tab F v) he).trans_eq (by ring)

lemma residual_bill (F : Labels.Frame G d) (L : Side) (c : ℝ) (hc : 0 ≤ c) (v : F.Coeff) :
    (∑ i : Tally F, ‖chips F v i‖ * (c * F.coeffSize (vowel F L (F.core (Size.axis F i.2))))) ≤
       c * orbitCost F * F.coeffSize (vowel F L (F.core v)) := by
  rw [show (∑ i : Tally F, ‖chips F v i‖ * (c * F.coeffSize (vowel F L (F.core (Size.axis F i.2))))) =
    c * (∑ i : Tally F, ‖chips F v i‖ * F.coeffSize (vowel F L (F.core (Size.axis F i.2)))) from by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring]
  exact (mul_le_mul_of_nonneg_left (vowel_tab F L v) hc).trans_eq (by ring)

/-- One descending PAPER step. No dependence on nonexistent coherent
multi-step decomposition. The inverse needed for *next* rebasing is proven
again on the just selected output. -/
theorem reprise (m : ℕ) (V : Voice F H p (m+1)) {η C : ℝ}
    (h : H.Selected) (hm : m<N) (hq : Heard B H N p A (m+1) V) (hw : roomCost H.levels W)
    (hb : Bank W H.levels) (T : Heading F) (ht : AtomStep B H N p m A T C η) (he : Buys H F W m C η) :
    ∃ Q : Voice F H p m, Heard B H N p A m Q ∧ Responds B H N p W m V Q := by
  classical
  let f (v) := (V.plays v).density 0 B (H.rep N p (m+1))
  have hf (v) : Integrable (f v) (prior G _) :=
    play_integrable H N h hm (hq.earns v).1 (hq.earns v).2
  let P := fun x => blast H N p m d (f x)
  have hP : IsLinearMap ℂ P := blast_linear H N p m hq.values hf
  have hM (v) (y) : dance y (P v) = P (Motion.patch F y v) := by
    rw [← show blast H N p m d (dance y (f v))= dance y (P v) from blast_dance H N p m d y (f v) (hf v)]
    rw [show dance y (f v) = f (Motion.patch F y v) from hq.travels ..]

  let s := (H.levels.params (m+1)).columns
  let L := H.S.block m
  let R := H.rep N p m
  let D (z) := F.coeffSize (vowel F L (F.core z))
  let c := C + η*s
  let ε := η*(1+s)
  have hS : 1 ≤ s := (H.levels.params (m+1)).columns_ge
  have hη := he.epsilon
  have hc' := he.cost
  have hs : 0 ≤ s := by linarith
  have hcc : C ≤ c := le_add_of_nonneg_right (by positivity)
  have hc : 0 ≤ c := by linarith
  have hε : 0≤ε := by unfold ε; positivity
  let J := Size.axis F
  have hd (i : F.Index) : PaidAtom B H N p m A (f (V.index.symm (J i))) (T.leads L (J i))
      (ε * F.coeffSize (F.core (J i))) (c*D (J i)) := by
    let v := V.index.symm (J i)
    have hh : V.index v = J i := V.index.apply_symm_apply _
    have h := InputColumn.main B H N p m A (V.plays v) i h hm ht hη ((hq.currents v).trans hh)
      (hq.earns v).1 (hq.earns v).2
    have hu : V.charge v ≤ s * F.coeffSize (F.core (J i)) := hh ▸ hq.cone v
    refine atom_mono h ?_ ?_
    · exact (mul_le_mul_of_nonneg_left (add_le_add_right hu _) hη).trans_eq (by unfold ε J; ring)
    have hz : F.coeffSize (F.core (J i)) ≤ D (J i) := (Work.G08.size_vowel F L _).1
    exact (add_le_add_right (mul_le_mul_of_nonneg_left (le_trans hu (mul_le_mul_of_nonneg_left hz hs)) hη) _).trans_eq
      (by unfold c D L J; ring)
  unfold PaidAtom at hd; simp only at hd; choose X hx using hd
  choose hX Q hQ hF hT hU using show ∀ i y, _ from fun i y => hx i y

  let O : Tally F → Coefficient F _ := fun j => Q j.2 j.1
  let Y : F.Coeff →ₗ[ℂ] Tally F → ℂ := (chips F).comp V.index.toLinearMap
  let Z : F.Coeff → Coefficient F _ := pencil (code (Tally F)) O Y
  let a v := c * orbitCost F * D (V.index v)
  let y := Real.sqrt (H.levels.clock.forcedAllowance m)
  have hy : 0<y := Real.sqrt_pos.2 (forcedPos ..)
  have hy' := (h.represents N p m hm.le).good
  have hb' (v) : (Z v).Format 0 A R ∧ (Z v).remBound 0 R y (a v) := by
    let t (j : Tally F) := c*D (J j.2)
    have h := pencil_cost (code _) O Y (X:=t) hy (fun j => ⟨hF j.2 j.1,hT j.2 j.1⟩) v
    exact ⟨h.1,rem_mono h.2 (residual_bill F L c hc (V.index v))⟩
  have hZ (v) : (Z v).x = repaint F X (V.index v) := by
    unfold Z
    rw [pencil_x]
    exact Finset.sum_congr rfl fun i _ => congr_arg (chips F (V.index v) i • ·) (hQ ..)
  have hp (v) : (Z v).density 0 B R=P v := by
    let K := (IsLinearMap.mk' P hP).comp V.index.symm.toLinearMap
    have hh (v) (y) : dance y (K v)=K (Motion.patch F y v) := by
      change dance y (P _)=P _
      rw [hM]; apply congr_arg
      apply V.index.injective; rw [← hq.moves]; simp
    funext x
    have hi := field_same F K hh (V.index v) x
    unfold Z
    rw [pencil_density (code _) O Y hy' hy (X:=fun j => c*D (J j.2)) (fun j => hT j.2 j.1)]
    refine (Finset.sum_congr rfl (g:=fun i : Tally F => chips F (V.index v) i *
        dance i.1 (K (J i.2)) x) fun i _ => ?_).trans (hi.trans ?_)
    · exact congr_arg ((Y v i) * ·) (congr_fun (hU i.2 i.1) x)
    change P (V.index.symm (V.index v)) x= P v x; rw [LinearEquiv.symm_apply_apply]

  have hI (v) : F.coeffSize ((Z v).x - T.leads L (V.index v)) ≤
      barunit L * F.coeffSize (F.core (V.index v)) := calc
    _ ≤ ε*orbitCost F*F.coeffSize (F.core (V.index v)) := by
      rw [hZ]; exact budgets_orbit F L T X (V.index v) ε hε (fun i => hX i.2 i.1)
    _ ≤ _ := mul_le_mul_of_nonneg_right he.tiny (Work.G08.size_nonneg ..)
  have ht' (v) : direction H W m F (Z v).x (V.plays v).x (a v) (V.charge v) := by
    rw [hq.currents]
    have ho : 0 ≤ V.charge v := rem_nonneg (hq.earns v).2
    have hg : 0 ≤ barunit L := by
      have hl : (0 : ℝ) ≤ L.val := by positivity
      unfold barunit puffs; positivity
    refine ⟨rem_nonneg (hb' v).2,ho,T.map,fun x => ?_, (hI v).trans ?_,?_⟩
    · have hb : C ≤ W.K (H.levels.clock.J (m+1)) :=
        le_trans (hcc.trans (le_mul_of_one_le_right hc (orbitCost_one_le F))) he.funds
      have hz := mul_le_mul_of_nonneg_right hb (Work.G08.size_nonneg F x)
      exact ⟨((ht.map_norm x).1).trans hz,((ht.map_norm x).2).trans hz,(T.core_comm x).symm⟩
    · exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right ho) hg
    change c * orbitCost F * D (V.index v) ≤ _
    refine le_trans (mul_le_mul_of_nonneg_right he.funds (Work.G08.size_nonneg F _)) ?_
    change _*D _ ≤ _*F.coeffSize (F.core (vowel F L _))+_
    rw [Work.G08.core_vowel]
    exact le_add_of_nonneg_right (mul_nonneg hg ho)

  have hback (v) := Work.G08.cone_step W H hw hb m F _ _ _ _ (ht' v) (show V.charge v ≤
    s * F.coeffSize (F.core (V.plays v).x) from (hq.currents v).symm ▸ hq.cone v)
  have hBook : Ledger F _ Z := pencil_ledger ..
  let Ψ := IsLinearMap.mk' _ hBook.x
  have hΨ : Injective Ψ := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have ha := (hback v).2.1
    rw [show (Z v).x=0 from hv, hq.currents] at ha
    apply V.index.injective
    rw [map_zero]
    exact Work.G08.size_separates F _ (by simpa [Frame.coeffSize] using ha)
  let out : Voice F H p m := ⟨Z,a,LinearEquiv.ofBijective Ψ ⟨hΨ, LinearMap.injective_iff_surjective.mp hΨ⟩⟩
  refine ⟨out, ⟨hBook,hb',fun _ => rfl,fun v => (hback v).1,?_,fun v x => ?_,?_, ?_, ?_⟩,hp,ht'⟩
  · intro i j
    change a (i+j) ≤ a i + a j
    unfold a D
    rw [map_add,map_add,← mul_add,show vowel F L (F.core (V.index i) + F.core (V.index j)) =
      vowel F L (F.core (V.index i))+vowel F L (F.core (V.index j)) from by ext; simp [vowel,mul_add]]
    exact mul_le_mul_of_nonneg_left (Size.add F _ _) (mul_nonneg hc (zero_le_one.trans (orbitCost_one_le _)))
  · change Motion.patch F x (Z v).x=(Z _).x
    rw [hZ,hZ,repainted_eq,hq.moves]
  · change (Z (unitVec F H N)).x = _
    have hc := hI (unitVec F H N)
    rw [hq.unit,show F.core (unitVec F H (m+1))=0 by simp [unitVec,Size.unit_core]] at hc
    rw [show (Z (unitVec F H N)).x = T.leads L (unitVec F H (m+1)) from sub_eq_zero.mp (Work.G08.size_separates _ _ (by simpa [Frame.coeffSize] using hc))]
    change T.map (vowel F L _) = _
    rw [show vowel F L (unitVec F H (m+1)) = unitVec F H m from unit_vowel ..]; simp [unitVec,T.unit]
  · change IsLinearMap ℂ (fun v => (Z v).density 0 B R)
    simpa only [hp] using hP
  intro v x
  change dance x ((Z v).density 0 B R)=(Z _).density 0 B R
  rw [hp,hp,hM]
end YM.Extra.Histories
