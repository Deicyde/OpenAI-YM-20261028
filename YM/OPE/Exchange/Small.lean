import YM.OPE.Exchange.Regime
/-!
# One-radius bounds through every horizon, subpower version

Consumes a projection chosen *once*, plus exterior clearances for the **geometry**
(not which words or character correlations are to read them later). `c>0` can
be as small as desired but chosen before `eventually`. Deal also with differing
clearances by just taking a minimum over finitely many needs. No need of upper
limits in `y`. Fit `‖x−o‖/r≤M` & `‖x−x'‖/r≥η`, covering any compact in
scaled mutually separated shapes. All η, eps and approach filters are ordinary
pointwise bounds here in the sense of **every point** in a sufficiently
small punctured positive interval, not just a.e. or generic.

Separate subpower estimate, not asserting the log improvement here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Set Filter Lattice RG Next.Extract Bid OS Ground Spec Prescription
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book} (U:Final C F S)
variable {P:Prescription U.sector.derivatives}(hP:P.Coherent) (h: Services C F S)
variable {I J L:Type}[Fintype I][Fintype J] {M η δ c ε : ℝ} (p:I→C.book.Token)(q:J→C.book.Token){n:ℕ}
   (hη:0<η) (hM:0≤ M)(hc:0<c)(he:0<ε)
variable {ℱ:Filter L}{X:L→I→E4}{Y:L→J→E4}{r:L→ℝ}{o:L→ E4} {κ: L→ℝ}
private lemma cross_cli (A:ℝ) (h':Tendsto r ℱ (𝓝[>] 0)) : RateIs ℱ (fun i=> run (r i)) (fun i=> (r i)^A) (-A):=(loglife h' |>.rpow A)|>.swap (by ring)
include U hP h hη hM p he
lemma small_coeff_aux [ℱ.NeBot] (i:Mode U.sector.derivatives)(hr:Tendsto r ℱ (𝓝[>] 0))(hx:∀ᶠ i in ℱ,WithinRoom (r i) M η (X i) (o i)): ∀ᶠ j in ℱ, (∀ u∈ (P.sheet i).support, Injective (beside (away (X j) (o j)) (bearing u))) ∧ ‖P.ope i (X j) p (o j)‖ ≤ (r j)^((i.fst:ℝ) - (sigma p:ℝ)-ε) :=by
    obtain ⟨ht,he'⟩:=room_regime hr hM hη hx; have hT:= run_towards hr; have hw:= available_cost U P p hT h hP ht he' zero_lt_one i -- classical Dec
    refine ((eventually_all_finset (P.sheet i).support).2 (fun i _=> epoch_space hT (he'.away o) ht zero_lt_one i)).and ((cross_cli (((i.fst:ℝ)-(sigma p:ℝ)-ε)) hr).outweigh hw (by linarith only [he]) hT) -- parentheses

include q hc
lemma small_horizon_aux [ℱ.NeBot] (hr:Tendsto r ℱ (𝓝[>]0)) (hx:∀ᶠ i in ℱ,WithinRoom (r i) M η (X i) (o i)) (hy:∀ᶠ i in ℱ, ClearOf (o i) (Y i) c)(n:ℕ): ∀ᶠ j in ℱ, Injective (beside (X j) (Y j)) ∧ Injective (beside (sole (o j)) (Y j)) ∧ Tested U P n (X j) p (o j) (Y j) q ((r j)^((n:ℝ)+1-(sigma p:ℝ)-ε)) :=by
    obtain ⟨ht,he'⟩:=room_regime hr hM hη hx; have hT:= run_towards hr; obtain ⟨hq,hχ⟩:= free_clear hT hc hy; have hR:=arrangement_cost U P n p q hT h hP ht he' zero_lt_one hq hχ le_rfl le_rfl zero_lt_one
    filter_upwards [(he'.chorus (hq.mono zero_le_one) ((Rec_spacing hT hχ ht zero_lt_one).mono zero_le_one)).inject, (Kept.sole ℱ _ _ _|>.chorus hq hχ).inject, (cross_cli ((n:ℝ)+1-(sigma p:ℝ)-ε) hr).outweigh hR (by linarith only [he]) hT] with i hi hi' hT; exact ⟨hi,hi',tested U P n (X i) p (o i) (Y i) q hT hi hi'⟩

omit hc q in
lemma small_coeff (i:Mode U.sector.derivatives) : ∀ᶠ r:ℝ in 𝓝[>]0, ∀ (x:I→ E4)(o:E4), WithinRoom r M η x o → (∀ u∈ (P.sheet i).support, Injective (beside (away x o) (bearing u))) ∧ ‖P.ope i x p o‖ ≤ r^((i.fst:ℝ)-(sigma p:ℝ)-ε):=by
    have he':= refine_geometry (P:=fun (r:ℝ)(g:(I→E4)×E4)=> WithinRoom r M η g.1 g.2) (Q:=fun (r:ℝ)(g:(I→E4)×E4)=> (∀ u∈ (P.sheet i).support, Injective (beside (away g.1 g.2) (bearing u))) ∧ ‖P.ope i g.1 p g.2‖ ≤ r^((i.fst:ℝ)-(sigma p:ℝ)-ε)) (φ:=𝓝[>]0) fun f ψ hN hp h' => (show ∃ χ :Filter ℝ, _ from ⟨ψ,hN,le_rfl,small_coeff_aux (r:=fun s=>s ) (X:=fun t=>(f t).1) (o:=fun t=>(f t).2) U hP h p hη hM he i (tendsto_id.mono_left hp) h'⟩)
    filter_upwards [he'] with r h x y using (h (x,y))
lemma small_horizon (n:ℕ) : ∀ᶠ r:ℝ in 𝓝[>]0, ∀ (x:I→ E4)(o:E4)(y:J→ E4), WithinRoom r M η x o → ClearOf o y c→ Injective (beside x y) ∧ Injective (beside (sole o) y) ∧ Tested U P n x p o y q (r^((n:ℝ)+1-(sigma p:ℝ)-ε)) := by
    have hw:= refine_geometry (P:=fun (r:ℝ)(g:(I→E4)× E4 × (J→E4))=> WithinRoom r M η g.1 g.2.1 ∧ ClearOf g.2.1 g.2.2 c) (Q:=fun (r:ℝ)(g:(I→E4)× E4 × (J→E4))=> Injective (beside g.1 g.2.2) ∧ Injective (beside (sole g.2.1) g.2.2) ∧ Tested U P n g.1 p g.2.1 g.2.2 q (r^((n:ℝ)+1-(sigma p:ℝ)-ε))) (φ:= 𝓝[>]0) fun f ψ hN hp hv=> ⟨ψ,hN,le_rfl,small_horizon_aux U hP h p q hη hM hc he (tendsto_id.mono_left hp) (hv.mono (fun _ hi=> hi.1)) (hv.mono (fun _ hi=> hi.2)) n⟩ -- shape elaboration
    filter_upwards [hw] with r h x o y hx hy using h (x,o,y) ⟨hx,hy⟩
end YM.OPE
