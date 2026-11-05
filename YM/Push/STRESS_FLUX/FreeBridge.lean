import YM.Push.STRESS_FLUX.Consumer
import YM.Push.STRESS_FLUX.Placement
import YM.Push.STRESS_FLUX.Reverse
import YM.Push.STRESS_FLUX.Sharpen
import YM.Push.STRESS_FLUX.Tune


/-! Strengthen ANY `Org.MaxwellData` to pay the particular free normalization
required at the flux bridge, without swapping field hierarchy or coupling,
K, W, κ. This does **not** construct MaxwellData (or assume Locals).
Separated calculations only, using the two flux laws already demanded on
its actual free Wick fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux.FreeBridge
open Function Set Filter Table Org Work.A01 Work.A15 Climb
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {L : Register G} {C : Family G} {T : Lighthouse L}

def first (c : ℝ) := (![c,0,0,0]:Coeff)
lemma vac_label (t : ℝ) : material (Bel L) (first t) = Tune.vac (Bel L) t := by
  have he : fromPol (Bel L) (Labels.unit G 4) = (Bel L).unit 4 := by
    rw [fromPol_formula,Labels.Frame.coords_unit]; unfold Table.unit Register.scalar
    change _ = (Bel L).project 4 (((1:ℝ):ℂ)^4 • _)
    rw [Complex.ofReal_one,one_pow,one_smul]
  funext a b
  simp only [material,stress_of,Tune.vac]; split <;> simp [first,-fromPol_formula,he]

lemma exists_label (h : G.Simple) {S : Table (Maxwell.standard L.grid)} (hS : S=Bel L) (hs : S.Hierarchy) {W : DiffPlan S} {X : S.Rotation}
    (hx : X.Laws W hs.spin) (J : S.Stress) (hJ : Tensorial X J) (hh : ∀ a b, J a b = J b a) (he : ∀ a b, S.conj hs.spin 4 (J a b) = J a b) :
    ∃ w, J = material S w := by
  subst S
  have hr := (⟨hh,he,fun k a b => ?_⟩ : J ∈ TableTwo hs.spin)
  · obtain ⟨w,hw⟩ := (free_stress_bij (L:=L) h hs.spin).2 ⟨_,hr⟩; exact ⟨w,(congr_arg Subtype.val hw).symm⟩
  change (Bel L).mirror hs.spin 4 k (J a b) = _
  rw [← hx.signed, hJ]
  change (∑ i, ∑ j, (((k.matrix i a * k.matrix j b : ℝ):ℂ)) • J i j) = _
  simp_rw [show ∀ (r : ℝ) (x : (Bel L).Field 4), (r:ℂ) • x = r • x from IsScalarTower.algebraMap_smul ℂ, mul_smul, ← Finset.smul_sum,signed_sum]

set_option maxHeartbeats 1200000 in
lemma remove (h : G.Simple) (hs : (Bel L).Hierarchy) (w : Coeff) {P : Parts (Bel L)} {Z : Ward.SpinRows (Bel L)} (hp : StressLaws (Bel L) (material (Bel L) w) P Z) :
    material (Bel L) w - Tune.vac (Bel L) (w 0) = w 3 • material (Bel L) weyl := by
  let u := w-first (w 0)
  have hu : material (Bel L) u = material (Bel L) w - Tune.vac (Bel L) (w 0) := by rw [← vac_label]; funext a b; simp [material,u,-fromPol_formula]
  have hL := (hu ▸ Tune.vac_laws hs hp (w 0) : StressLaws (Bel L) (material (Bel L) u) P Z)
  have hz : u 0=0 := sub_self _
  let q : Fin 0 → (Bel L).Tag := Fin.elim0
  have hx : (0:Points 1) ∈ conf 1 := fun _ _ _ => @Subsingleton.elim (Fin 1) _ _ _
  have hy z : Points.cons z (0: Points 1) = axisLine z := by ext1 i; fin_cases i <;> rfl
  have H := div_kernel (L:=L) h u hz (fun i j => ?_)
  · rw [← hu]
    conv_lhs => rw [H]
    funext a b
    simp only [material,show u 3 = w 3 from sub_zero _,map_smul,Pi.smul_apply]
  have hp := Reverse.obs_deriv (material (Bel L) u) q 0 hs hL (x:=0) hx (d:=4) (fromPol (Bel L) (pair G i j i j)) (basis 0) ((hy (basis 0)) ▸ axisLine_in base_ne)
  have hh a : signal L u i j i j a 0 = Reverse.obs (material (Bel L) u) (Fin.cons (α:=fun _ => (Bel L).Tag) ⟨4,fromPol (Bel L) (pair G i j i j)⟩ q) a 0 0 := by
    funext z; rw [signal,Reverse.obs,hy,quad]; congr 1
    ext1 k; fin_cases k <;> rfl
  simp_rw [hh]; exact hp

lemma canonical (h : G.Simple) (hs : (Bel L).Hierarchy) (hT : T.Goes L hs.spin) : ∃ τ : ℝ, τ ≠ 0 ∧ StressLaws (Bel L) (τ • material (Bel L) weyl) (T.κ • T.W.deriv) (T.κ • T.K.lie) := by
  have hL := Tune.laws_smul hs.smooth hT.delta T.κ⁻¹
  simp only [inv_smul_smul₀ T.hκ] at hL
  let J := Tune.re hs.spin (averageStress T.K (T.κ⁻¹ • T.J))
  have he : StressLaws _ J T.W.deriv T.K.lie := Tune.re_laws hs hT.hers hT.turns (stressLaws_average _ Work.A10.answer hs hT.turns hT.preserves hL)
  obtain ⟨w,hw⟩ := exists_label h (L:=L) rfl hs hT.turns J (Tune.re_tensor hs hT.turns (tensorial_average hT.turns _)) (Reverse.symmetric J hs he) (Tune.re_conj _ _)
  rw [hw] at he
  have h1 := remove h hs w he ▸ Tune.vac_laws hs he (w 0)
  change StressLaws (Bel L) (w 3 • material (Bel L) weyl) _ _ at h1
  have hn : w 3 ≠ 0 := fun h0 => hT.born (funext fun a => ContinuousLinearMap.ext fun x => (Bel L).field_ext hs.laws.toSymmetric (fun n q z hz => by
    obtain ⟨χ,hχ⟩ := exists_window z hz
    change (Bel L).useAt _ _ (Fin.cons ⟨4+1,T.W.deriv 4 a x⟩ q) = (Bel L).useAt _ _ (Fin.cons ⟨4+1,0⟩ q)
    rw [← h1.translation hz q hχ a 4 x,h0,zero_smul,← translationFlux_apply hz hχ hs.smooth,map_zero, ← front_eval q z (4+1) 0, map_zero]))
  exact ⟨T.κ * w 3,mul_ne_zero T.hκ hn,mul_smul T.κ (w 3) (material (Bel L) weyl) ▸ Tune.laws_smul hs.smooth h1 T.κ⟩

theorem calibrate (h : G.Simple) (M : MaxwellData C) : ∃ P : MaxwellData C, P.T.κ=M.T.κ ∧ P.T.W=M.T.W ∧ P.T.K=M.T.K ∧ P.vacuum=M.vacuum ∧ ∃ τ : ℝ, τ≠0 ∧ P.T.J=τ • material (Bel C.book) weyl := by
  obtain ⟨τ,ht,h⟩ := canonical h M.hT M.lit
  let T := { M.T with J := τ • material (Bel C.book) weyl }
  let P : MaxwellData C := ⟨T,M.hT,⟨M.lit.edges,M.lit.pales,M.lit.hers,M.lit.turns,M.lit.preserves,h,M.lit.born,M.lit.cuts⟩,M.vacuum,M.rolls,M.optic,M.marks,M.frames⟩
  exact ⟨P,rfl,rfl,rfl,rfl,τ,ht,rfl⟩

lemma bridge {S : Table C.book} (hs : S.Hierarchy) (W : DiffPlan S) (h : G.Simple) (M : MaxwellData C) (h0 : Nonstress hs.spin W M.hT.spin M.T.W) : Bridge C hs W := by
  obtain ⟨P,-,hW,-,-,τ,ht,he⟩ := calibrate h M
  exact ⟨P,τ,ht,he,hW ▸ h0⟩
open Extraction Matching Next.BOUNDARY in
theorem through {M : Metals G} {D : RG.Supply.Rolls M.p} {A : Alloy M D} {B : Bolt A} {S₀ S : Table C.book} {P : ℕ → Table C.book} {f : Extraction.Order} {W : DiffPlan S}
    (hg : G.Simple) (hB : Assembly B C) (h : Arrives C f S₀ P) (hc : Cleaner S₀ P S W f)
    (hr : AtRank C f S) (ht : AtGrid C f S) (hq : ∀ g, ∀ s : Spec.Seed C (f.refine g) S, Grill C (f.refine g) →
      ∃ U : MaxwellData C, Nonstress s.kernel.spin W U.hT.spin U.T.W ∧ ∀ w : Coeff, ‖w‖ = 1 → nabla W (material S w)=0 → Centers (material S w) →
        ∀ d≥4, ∀ B : C.label d, (∃ l, Ancestor ((f.refine g).refine l) (StressFlux.token C w) B (d+1) 3) ∧ (∃ l, Ancestor ((f.refine g).refine l) (StressFlux.token C w) B d 4))
    (miles : Bid.Miles) : ∃ g, Nonempty (Spec.Final C (f.refine g) S) := by
  have he := endpoint hg hB h hc hr ht (fun g s he => ?_) miles
  · obtain ⟨g,-,-,F,-⟩ := he; exact ⟨g,⟨F⟩⟩
  obtain ⟨U,hU,hT⟩ := hq g s he
  refine ⟨bridge s.kernel W hg U hU,fun w hn hb hw d B => ?_⟩
  rcases lt_or_ge d 4 with h|h
  · have H (l) := (hB.port hg ((f.refine g).refine l)).book ..
    exact ⟨⟨Extraction.Order.full,quotes_tiny hg hB.stamp (H _) _ _ h (by decide)⟩,⟨Extraction.Order.full,quotes_tiny hg hB.stamp (H _) _ _ h (by decide)⟩⟩
  obtain ⟨⟨l,hl⟩,a,ha⟩ := hT w hn hb hw d h B
  exact ⟨⟨l,quotes_of_ancestor hl⟩,⟨a,quotes_of_ancestor ha⟩⟩
end YM.StressFlux.FreeBridge
