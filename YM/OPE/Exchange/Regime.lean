import YM.OPE.Exchange.Arrangement

/-!
# Rooms and clearances of fixed scaled geometries
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Set Filter Lattice RG Next.Extract Bid OS Ground Spec Prescription
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J L : Type}[Fintype I][Fintype J]{φ:Filter L}{T r:L→ℝ} {a c b d η M : ℝ}
variable {X:L→ I→ E4}{O:L→ E4} {Y:L→J→ E4}

/-- Handy conversion into a uniform asymptotic assertion. Allowed to refine the
filter once more for a finite family of geometries or properties, thus dealing
also with layouts frequently but not yet eventually in good regimes. -/
lemma refine_geometry {V : Type*}[Nonempty V] {P Q : L→ V→Prop}
    (h:∀ f:L→V, ∀ (ψ : Filter L) (_ : ψ.NeBot) (_ : ψ ≤ φ), (∀ᶠ i in ψ,P i (f i)) → ∃ χ : Filter L, χ.NeBot ∧ χ ≤ ψ ∧ ∀ᶠ i in χ,Q i (f i)) : ∀ᶠ i in φ, ∀ x : V,P i x → Q i x:=by
    refine universalize (p:= fun i x=> P i x→ Q i x) (fun f=> ?_)
    by_contra ha; let U:={i | ¬ (P i (f i)→ Q i (f i))}; let ψ:= φ ⊓ 𝓟 U; have hN:ψ.NeBot:= frequently_mem_iff_neBot.mp (show ∃ᶠ i in φ, i∈U from not_eventually.mp ha)
    have he:(∀ᶠ i in ψ,P i (f i) ∧ ¬ Q i (f i)):= ((show ∀ᶠ i in 𝓟 U, i∈ U from eventually_principal.mpr (fun i h=> h)).filter_mono inf_le_right).mono (fun i hi=> (Classical.not_imp.mp hi))
    obtain ⟨χ,hc,hp,hf⟩:= h f ψ hN inf_le_left (he.mono (fun i hi=>hi.1)); obtain ⟨i,hi⟩:= ((he.filter_mono hp).and hf).exists; exact hi.1.2 hi.2

structure WithinRoom (r:ℝ)(M η:ℝ)(x:I→E4)(o:E4): Prop where
    span (i:I) : ‖x i-o‖ ≤ M*r
    spaced (i j:I): i≠j→ η*r ≤ ‖x i-x j‖

structure ClearOf (o:E4)(y:J→E4)(c:ℝ): Prop where
    openSpace (v:J): c ≤ ‖o-y v‖
    spread (i j:J): i≠j→ c ≤ ‖y i-y j‖

/-- Negative log, so r has rate -1. -/
def run (r:ℝ):ℝ:= -(Real.log r)
lemma run_towards (h:Tendsto r φ (𝓝[>] 0)) : Tendsto (fun i=>run (r i)) φ atTop := (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero).comp h
lemma loglife (h:Tendsto r φ (𝓝[>] 0)): RateIs φ (fun i=>run (r i)) r (-1):=by
    have hT:=run_towards h; have hx:∀ᶠ i in φ, 0< r i:= h.eventually (p:=fun (i:ℝ)=>0 < i) self_mem_nhdsWithin
    refine ⟨hx,tendsto_const_nhds.congr' ?_⟩; filter_upwards [hT.eventually_gt_atTop 0] with i hi; apply (eq_div_iff (show run (r i) ≠ 0 from ne_of_gt hi)).mpr; unfold run; ring
lemma room_regime (h:Tendsto r φ (𝓝[>] 0))(hM:0 ≤ M)(hη:0 < η)(hp:∀ᶠ i in φ, WithinRoom (r i) M η (X i) (O i)) : let T:= fun i=>run (r i); enveloped φ T 1 X O ∧ Kept φ T 1 X:=by
    intro T; have hT : Tendsto T φ atTop := run_towards h; have hr:=loglife h; constructor
    · apply (((RateLE.const M hT).mul (hr.pays hT)).mono (zero_add _|>.le)).of_norm_le; filter_upwards [hp,hr.pos] with i hi hh using (pi_norm_le_iff_of_nonneg (mul_nonneg hM hh.le)).mpr hi.span
    have he: RateIs φ T (fun i=>η*r i) (-1):=((RateIs.const hT hη).mul hr)|>.swap (zero_add (-1)); intro c hc
    filter_upwards [hp,he.overtakes (RateLE.exp (-c) hT) hT (by linarith only [hc])] with i hi he using (fun j k hj=> he.trans_le (hi.spaced j k hj))
omit [Fintype J] in
lemma free_clear (hT:Tendsto T φ atTop)(he:0<c)(h:∀ᶠ i in φ,ClearOf (O i) (Y i) c): Kept φ T 0 Y ∧ Intervals φ T 0 (fun i=> sole (O i)) Y:=by
    have hh(a:ℝ)(h:0<a):∀ᶠ i in φ, Real.exp (-a*T i)<c:= (RateIs.const hT he).overtakes (RateLE.exp (-a) hT) hT (neg_lt_zero.mpr h); constructor
    · intro a ha; filter_upwards [hh _ ha,h] with i hx hi using (fun j k hj=> hx.trans_le (hi.spread j k hj))
    intro a ha; filter_upwards [hh _ ha,h] with i hx hi using (fun _ j=>hx.trans_le (hi.openSpace j))
end YM.OPE
