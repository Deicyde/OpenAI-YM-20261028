import YM.Next.MULTISOURCE.Initialize
import YM.Next.MULTISOURCE.Kernel
import YM.Next.MULTISOURCE.Surjection

/-!
# Inductive rank-cost choice (NOT uniform Mix funds)
-/

set_option autoImplicit false
noncomputable section
namespace YM.Multi.Step
open RG Wilson Lattice MeasureTheory Marker Filter Finset Work.G07
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff

variable {G : Gauge} {V : Type} [Fintype V] [DecidableEq V] {R : Census V}

abbrev polyse (R : Census V) (i : V) := Hot.one (parts R) (Hot.one R i)
abbrev inflation {n : Side} (i : Hot (parts R)) (o : V→Site n) := (unionOfHot i).sites.image o
omit [Fintype V] in
lemma polyse_inj (i j) : polyse R i=polyse R j ↔ i=j := by simp [polyse]

def rsv (i : Hot (parts R)) : ℝ := if ∃ j,polyse R j=i then 0 else 2
omit [Fintype V] in
lemma rsv_polyse (i) : rsv (polyse R i)=0 := by unfold rsv; exact if_pos ⟨_,rfl⟩

section
variable {p N j : ℕ}
structure Passage (H : History G) (j p N : ℕ) (o : V → Site (H.S.side j p))
    (D : Hot R→ Pulse G (H.S.side (j+1) p)) (L : V → Pulse G (H.S.side j p))
    (Z : Hot (parts R) → Pulse G (H.S.side j p)) (i : Hot (parts R)) (θ b : ℝ)
    (Y : Pulse G (H.S.side j p)) : Prop where
  records x : polyse R x=i → Y=L x
  budgeted : Credit (H.rep N p j).p (rsv i) (money H.levels j) (inflation i o) Y b
  derivative : ∃ f,SimpleBound (H.rep N p j).p θ b f ∧ recept (H.rep N p j).p Y.1 f
  exactF : tangent (H.rep N p j) Y=defect (H.levels.clock.op j p) (H.rep N p j) (H.rep N p (j+1)) Z D i

structure Specified (H : History G) (j p N : ℕ) (o : V → Site (H.S.side j p)) (D : Hot R→ Pulse G (H.S.side (j+1) p))
    (L : V → Pulse G (H.S.side j p)) (ℓ : ℝ) : Prop where
  issued : ∃ X : Hot R → Support (H.S.side (j+1) p), ∀ i, Credit (H.rep N p (j+1)).p 0
    (money H.levels (j+1)) (X i) (D i) 1
  paid i : Credit (H.rep N p j).p 0 (money H.levels j) {o i} (L i) ℓ
  meters i : tangent (H.rep N p j) (L i)= (H.levels.clock.op j p).push (H.β N p (j+1)) (tangent (H.rep N p (j+1))
    (D (Hot.one R i)))
end

omit [Fintype V] in
lemma power_set (R : Census V) (i : Hot (parts R)) (n : ℕ) (he : i.sites.card ≤ n+1)
    (t : Hot (parts R)) (hf : t.sites ⊂ i.sites) : t.sites.card≤ n := Nat.le_of_lt_succ ((card_lt_card hf).trans_le he)

lemma pass_ceiling (H : History G) (j p N : ℕ) (h : H.Selected) (he : j<N) {θ b : ℝ} (hθ : 0 ≤ θ)
    (ht : ∀ (d : Directions G (H.S.side j p)) i,(H.rep N p j).p.dirBound i d → ‖d‖≤θ) (ℓ : ℝ) (y : Hot (parts R))
    (hb : 0≤b) : ∃ a : ℝ,
      ∀ o : V→Site (H.S.side j p), ∀ (D : Hot R → Pulse G (H.S.side (j+1) p)) (L : V→ Pulse G (H.S.side j p)),
        Specified H j p N o D L ℓ → ∀ Z : Hot (parts R) → Pulse G (H.S.side j p),
        (∀ i : Hot (parts R), i.sites ⊂ y.sites → Passage H j p N o D L Z i θ b (Z i)) →
        ∃ A, Passage H j p N o D L Z y θ a A := by
  let P := H.rep N p j
  let Q := H.rep N p (j+1)
  let S := H.levels.clock.op j p
  have hP : P.Lawful _ _ _ _ _ := (h.represents N p j he.le).good
  have hQ : Q.Lawful _ _ _ _ _ := (h.represents N p (j+1) he).good
  let k := money H.levels j; let k' := money H.levels (j+1)
  obtain ⟨C,hC⟩ := jet_bounded (parts R) 1 k' Q hQ (exponent_gauge H h N p (j+1) he) y.val
  obtain ⟨r,t,hT⟩ := kernelized H j p N he h hθ C
  by_cases hy : ∃ j, polyse R j=y
  · obtain ⟨i,hi⟩ := hy
    refine ⟨max r ℓ,fun o D L hS Z hh => ⟨L i,fun s hs => ?_,?_,?_,?_⟩⟩
    · exact congrArg L ((polyse_inj ..).mp (hi.trans hs.symm))
    · obtain rfl := hi; rw [rsv_polyse]; simp only [polyse, inflation, unionOfHot_one,Hot.sites_one,image_singleton]
      exact (hS.paid i).expand (le_max_right ..)
    · obtain rfl := hi
      let Y := tangent Q (D (Hot.one R i))
      obtain ⟨X,hX⟩ := hS.issued
      have hp : FitsPurse C Y := by rw [show Y=_ from (first_jet Q hQ.labels D (parts R) (Hot.one R i)).symm]; exact hC D X hX
      refine ⟨clean P (S.push Q.beta Y), ((hT Y hp).2).expand (le_max_left ..),?_⟩
      intro U hU; apply mul_left_cancel₀ (show (↑(P.eval U):ℂ)≠0 by exact_mod_cast (AxisShift.chosen_positive h he.le U).ne')
      rw [cleaned P _ U (AxisShift.chosen_positive h he.le U), ← show tangent P (L i)=_ from hS.meters i,
        ← first_jet P hP.labels L R i,simple_all _ _ _ _ hU]; simp [Census.fire,P]
    obtain rfl := hi
    unfold defect; simp only [polyse,ProperSum,Hot.one, singleton_shards,erase_singleton,sum_empty, sub_zero]
    rw [first_jet Q hQ.labels]; exact hS.meters i
  obtain ⟨B,m,hU⟩:= at_step θ hθ P hP (exponent_gauge H h N p j he.le) b k y
  let A := r + 2^P.p.order * ‖(-1:ℂ)‖ * B
  obtain ⟨w,hW⟩ := right_paid P hP (exponent_gauge H h N p j he.le) (t+m) A ht (money_accepted H.levels j).1
  refine ⟨max w A,fun o D L hS Z hh => ?_⟩
  let g := jet Q (parts R) D y.val
  let T := S.push Q.beta g
  let E i := if i.sites ⊂ y.sites then Z i else 0
  have hf i (he : i.sites ⊂ y.sites) : Z i=E i := (if_pos he).symm
  have hs := proper_inputs P Z E y hf
  obtain ⟨hY,F,hF,hK⟩:=hU (fun i => inflation i o) E fun i => by
    unfold E; split <;> rename_i he
    · exact ⟨(hh i he).budgeted.soft,(hh i he).derivative⟩
    refine ⟨(Credit.zero P.p le_rfl (money_accepted H.levels _).1 ((unionOfHot i).property.image o)).expand hb,fun _ => 0,
      (SimpleBound.const ..).expand (norm_zero.le.trans hb),fun _ _ => rfl⟩
  rw [← hs] at hY hK
  obtain ⟨X,hX⟩:=hS.issued
  obtain ⟨hJ,hj⟩ := hT g (hC D X hX)
  let f := fun U => clean P T U - F U
  let q := defect S P Q Z D y
  have ha : SimpleBound P.p θ A f := hj.sub hF
  have hq : FitsPurse (t+m) q := hJ.sub hY
  have Hv : recept P.p q (fun U => (P.eval U:ℂ)*f U) := by
    intro U hQ; have hu := hK U hQ
    change T U-ProperSum P Z y U=(P.eval U:ℂ)*(_- _)
    rw [hu,mul_sub,cleaned P T U (AxisShift.chosen_positive h he.le U)]
  obtain ⟨HU,HW⟩ := right_valid P q f Hv
  refine ⟨right P q f,⟨fun x h => False.elim (hy ⟨_,h⟩),?_,⟨f,ha.expand (le_max_right ..),HU⟩,HW⟩⟩
  rw [show rsv y=2 from if_neg hy]; exact (hW q f ha hq _ ((unionOfHot y).property.image o)).expand (le_max_left ..)
end YM.Multi.Step
