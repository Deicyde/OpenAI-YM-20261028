import YM.Next.FREE_KERNELS.Lifts
import YM.Next.UV_STRESS.Foundation
import YM.Next.UV_STRESS.Union
import YM.Push.COMMON_WITNESSES.Fields
import YM.Push.CUTOFF_PROJECTORS.Bank
import YM.UVNext.FREE_STRESS_CERTIFICATE.Consumer
import YM.UVNext.FREE_STRESS_CERTIFICATE.ShellChange
import YM.UVNext.FREE_STRESS_CERTIFICATE.ShellForce
import YM.Work.A10


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Choosing a MaxwellData built with the canonical stress

Relax the stress ante if Maxwell builder can prove only the literal current
`Org.MaxwellData` at first. Arbitrary nonempty MaxwellData -> MaxwellData with
the stress of our certificate, retaining H,W,K,omega etc. At this cut don't
ask for the *numerical* value of the rescaled κ – like in Lighthouse.Goes we
record and keep the same exact fluxes with a common nonzero factor (normalization
compiler). This does not give a proof of `lit.delta` from just Wick/hierarchy,
or of  computing the candidate κ=-τ, and is not a license to change T
in any already-started ActLaw or producer chain. We can't necessarily infer
FreeDiv itself at the *input* T with no ante (in fact if there is any T at all,
there are ones for which this implication fails). Use at YU architecture
**before** weak comparison & κ-dependent requests, or use `from_data` for the
fixed canonical T.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.FreeStress
open Maxwell Labels Table Climb Work.A01 Work.A15 Next.UVStress Function Set MeasureTheory Filter Analysis Org
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} (hG : G.Simple) {C : Family G} (T : MaxwellData C)

local notation "F" => C.book.grid
local notation "S" => Bel C.book

include hG in
lemma every_light (J : KernelSpace T.hT.spin) (h : currentDiv T.T.W T.hT.spin T.lit.hers J=0) :
    ∃ c : ℝ, J.val = torch F c := by
  have hh := line_dim F T.hT.spin hG T.T.W T.lit.pales T.lit.hers
  let j : LinearMap.ker (currentDiv T.T.W T.hT.spin T.lit.hers) :=
    ⟨generator _ _, radiating F T.hT.spin hG T.T.W T.lit.pales T.lit.hers⟩
  have he : j≠0 := fun h => generator_nonzero F T.hT.spin hG (congr_arg Subtype.val h)
  obtain ⟨c,hc⟩ := (finrank_eq_one_iff_of_nonzero' j he).1 hh ⟨J,h⟩
  have he : c • (generator F T.hT.spin).val=J.val := congr_arg
    (fun x : LinearMap.ker (currentDiv T.T.W T.hT.spin T.lit.hers) => x.val.val) hc
  exact ⟨c,(lighting F T.hT.spin ▸ he).symm⟩

section auxiliary
variable {L : Register G} {X : Table L} (H : X.Hierarchy)
variable {R : X.Rotation} {W : DiffPlan X} (h : R.Laws W H.spin) (hv : R.Oriented X)

include H hv in
private lemma rotate_center (K : Ortho) (x : X.Field 4) :
    expectation X 4 (R.act 4 K x) = expectation X 4 x := by
  simp_rw [expectation,front_eval]
  let v := Fin.cons (α:=fun _ : Fin 1 => X.Tag) ⟨4,x⟩ (blank X)
  have he := hv 1 v (0:Points 1) conf1 K
  rw [show Points.move K (0:Points 1) = 0 from PiLp.ext fun i => map_zero (Ortho.motion K),
    show R.label K ∘ v = Fin.cons (α:=fun _ : Fin 1 => X.Tag) ⟨4,R.act 4 K x⟩ (blank X) from
      funext fun i => by rw [@Subsingleton.elim (Fin 1) _ i 0]; rfl] at he
  exact he

include h hv in
lemma stays_tensor {U : X.Stress} (he : Tensorial R U) : Tensorial R (reCenter X U) := by
  intro K a b
  change R.act _ K (centering X 4 _) = ∑ i : Axis, ∑ j : Axis, _ • centering X 4 _
  rw [show R.act _ K (centering X 4 (U a b)) = centering X 4 (R.act _ K (U a b)) from ?_, he]
  · simp only [map_sum,map_smul]
  rw [value_center,value_center,map_sub,map_smul,h.identity,rotate_center H hv]
end auxiliary

include hG in
/-- Compiler output. κ not retuned afterwards. K and W, erases etc need
not be rebuilt for a special stress. -/
theorem ignite (t : ℝ) (ht : t≠0) : ∃ V : Lighthouse C.book,
    V.W=T.T.W ∧ V.K=T.T.K ∧ V.J=torch F t ∧ V.Goes C.book T.hT.spin ∧ Tensorial V.K V.J := by
  let X : (Bel C.book).Stress := (((T.T.κ⁻¹ : ℝ):ℂ)) • T.T.J
  have hx : StressLaws S X T.T.W.deriv T.T.K.lie := by
    have hh := scale_stress T.hT T.lit.delta T.T.κ⁻¹
    simpa only [inv_smul_smul₀ T.T.hκ] using hh
  let U := averageStress T.T.K X
  have hU : StressLaws S U T.T.W.deriv T.T.K.lie := stressLaws_average X Work.A10.answer T.hT T.lit.turns T.lit.preserves hx
  have htU : Tensorial T.T.K U := tensorial_average T.lit.turns X
  let A := white T.hT U
  have haT : Tensorial T.T.K A := plainTensor T.hT _ _ T.lit.turns _ htU
  have haH : RawTensor T.hT.spin A := by
    intro k a b
    rw [← T.lit.turns.signed]
    exact haT k.ortho a b
  have ha : StressLaws S A T.T.W.deriv T.T.K.lie := averaged_white T.hT hU _ _ T.lit.turns T.lit.hers ⟨rfl,rfl⟩
  have hA : Conserved T.T.W T.hT.spin A :=
    ⟨symmetry T.hT T.T.W T.lit.pales A ha, white_real T.hT U, drain_div T.hT T.T.W T.lit.pales A ha⟩
  let j₀ : KernelSpace T.hT.spin := ⟨reCenter S A, enters T.hT _ (sym_mem.mpr ⟨hA.symmetric,hA.real,haH⟩)⟩
  have hJ : currentDiv T.T.W T.hT.spin T.lit.hers j₀=0 := by
    apply (linear_cons ..).mpr
    refine ⟨(sym_mem.mp (kernel_mem.mp j₀.property).1).1,(sym_mem.mp (kernel_mem.mp j₀.property).1).2.1,?_⟩
    intro b
    change ∑ a, T.T.W.deriv 4 a (centering S 4 _)=0
    have hd := T.T.W.unit_drop T.hT.laws T.lit.pales T.hT.smooth 4
    simp only [value_center, map_sub,map_smul,hd,smul_zero,sub_zero,hA.divergence]
  let down (i j) := -expectation S 4 (A i j)
  have he : j₀.val = A+fossil down := by
    funext i j
    change centering S 4 (A i j) = A i j + down i j • (Bel C.book).unit 4
    rw [value_center]; simp [down,sub_eq_add_neg]
  have hm : StressLaws S j₀.val T.T.W.deriv T.T.K.lie := he.symm ▸ add_unit T.hT ha down (fun i j => by dsimp [down]; rw [hA.symmetric i j])
  have hn : j₀.val ≠ 0 := by
    intro ht; apply T.lit.born
    funext b
    apply ContinuousLinearMap.ext; intro i
    apply Table.field_ext S T.hT.laws.toSymmetric; intro n q x hx
    obtain ⟨χ,hχ⟩ := exists_window x hx
    change (Bel C.book).useAt S x (Fin.cons ⟨5,T.T.W.deriv 4 b i⟩ q) =
      (Bel C.book).useAt S x (Fin.cons ⟨5,0⟩ q)
    rw [← hm.translation hx q hχ, ← translationFlux_apply hx hχ T.hT.smooth q,ht,map_zero, ← front_eval q x _ 0,map_zero]
  obtain ⟨c,hc⟩ := every_light hG T j₀ hJ
  have hxC : c ≠ 0 := by rintro rfl; exact hn (hc.trans (zero_smul _ _))
  let V : Lighthouse C.book := { T.T with
    J := torch F t
    κ := t * c⁻¹
    hκ := mul_ne_zero ht (inv_ne_zero hxC) }
  have ht' : V.J = (((t*c⁻¹:ℝ):ℂ)) • j₀.val := by
    rw [hc,torch, Complex.coe_smul, smul_smul, mul_assoc,inv_mul_cancel₀ hxC,mul_one]; rfl
  have hV : StressLaws S V.J (V.κ • V.W.deriv) (V.κ • V.K.lie) := by rw [ht']; exact scale_stress T.hT hm _
  refine ⟨V,rfl,rfl,rfl,
    ⟨T.lit.edges,T.lit.pales,T.lit.hers,T.lit.turns,T.lit.preserves,hV,T.lit.born,T.lit.cuts⟩,?_⟩
  have he : Tensorial V.K j₀.val := stays_tensor T.hT T.lit.turns T.lit.preserves haT
  intro K a b
  rw [ht']; simp only [Pi.smul_apply,map_smul,he K a b, Finset.smul_sum]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => smul_comm ..


include T hG in
/-- Keep exactly the incoming hierarchy, spin, rotation, diffusion, rolls,
frames; same book. The stress and common *proved* nonzero flux factor
are chosen by this cut (κ now for t times the displayed polynomial, known
through common window identities on this K); use only when allowed to choose
these *now* (never to switch already chosen costs/incoming p/Y/rank
estimates). If builder hasn't supplied actual Wick flux identities at all
this is not callable. -/
theorem fire (t : ℝ) (ht : t≠0) : ∃ Q : MaxwellData C,
    Q.T.J = torch F t ∧ Q.T.W = T.T.W ∧ Q.T.K = T.T.K ∧ Q.vacuum = T.vacuum ∧
      Q.hT = T.hT ∧ Tensorial T.T.K Q.T.J ∧ FreeDiv Q.T Q.hT Q.lit.hers := by
  obtain ⟨V,hV,hv,hD,hQ,hr⟩ := ignite hG T t ht
  let Q : MaxwellData C := ⟨V,T.hT,hQ,T.vacuum,hv ▸ T.rolls,hv ▸ T.optic,hv ▸ T.marks,hV ▸ T.frames⟩
  exact ⟨Q,hD,hV,hv,rfl,rfl,hv ▸ hr,from_data hG Q _ ht hD⟩

open Spec Extraction Cells
open scoped Topology

-- Unprepared in J, does not require that the builder succeed with a chosen
-- J before using χ comparison. Stations use only the original H regardless.
include hG in
theorem anew (t : ℝ) (ht : t≠0) {N : Extraction.Order} {Y : Table C.book} {W : DiffPlan Y}
    (h : Seed C N Y) (hw : W.Inclusions Y) (hv : W.Derivatives Y)
    (hu : Stations C N T.hT.spin)
    (budget : ∀ J : KernelSpace h.kernel.spin,J.val ≠ 0 → Conserved W h.kernel.spin J.val → Probed N J.val)
    (grill : Furnace C N) :
    ∃ (Q : MaxwellData C) (I : IR (C:=C) Y) (X : Scaling Y),
      Q.T.K=T.T.K ∧ Q.T.W=T.T.W ∧ Q.vacuum=T.vacuum ∧ Q.T.J=torch F t ∧
      I.J≠0 ∧ I.J∈KernelSpace h.kernel.spin ∧ Probed N I.J ∧
      Approaches (path X) (isoPanel X) ∧ Stable h.kernel.spin Q.hT.spin W T.T.W X ∧
        X.meter I.J Q.T.J ∧ UV C N Y W Q I := by
  obtain ⟨Q,hvQ,hD,hK,hb,-,-,hr⟩ := fire hG T t ht
  obtain ⟨I,X,hI,hX,hx,hA,hj⟩ := foundation Q h hw hv hr hu budget grill
  exact ⟨Q,I,X,hK,hD,hb,hvQ,hI,hX,hx,hA,hD ▸ hj.1,hj.2⟩

-- Important obstruction to trying to squeeze `FreeDiv` directly out of arbitrary

include T in
theorem not_every_builder : ∃ Q : MaxwellData C,Q.T.W=T.T.W ∧ Q.T.K=T.T.K ∧ Q.vacuum=T.vacuum ∧
    Q.T.κ=T.T.κ ∧ ¬ FreeDiv Q.T Q.hT Q.lit.hers := by
  by_cases he : FreeDiv T.T T.hT T.lit.hers
  · let V : Lighthouse C.book := { T.T with J := T.T.J + fossil (fun _ _ => 1) }
    let Q : MaxwellData C := { T with T := V, lit := { T.lit with delta := add_unit T.hT T.lit.delta _ fun _ _ => rfl } }
    refine ⟨Q,rfl,rfl,rfl,rfl,fun hi => ?_⟩
    have hh := (kernel_mem.mp hi.enters).2 0 0
    change expectation S 4 (T.T.J 0 0+(1:ℂ) • (Bel C.book).unit 4)=0 at hh
    rw [one_smul,map_add, mean_unit T.hT.laws,(kernel_mem.mp he.enters).2,zero_add] at hh
    exact one_ne_zero hh
  exact ⟨T,rfl,rfl,rfl,rfl,he⟩

end YM.UVNext.FreeStress
