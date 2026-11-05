import YM.TraceExtension.Pith.Campus

/-! Formal coefficient precision on this square. Work in invariant formal powers
 through λ = g²; verify at actual lengths through that grade, not just a presumed
 diagram-to-theory identification. Existence/uniqueness not conditional on
 existence of either a full asymptotic series or a higher-order formal prediction.
 We use a different calculation. Missing orders of these square columns are not
 used under the zero in leading E,d. This is NOT a real O(g⁴) bound, nor a
 claim to estimate a little o at degree in the signed variable g above 2 (parity
 gives the intervening cubic entry of a *formal* parity-compatible relation). -/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pith
open Function Filter Set Extraction Ward Climb Spec Over Pilot Table Analysis Maxwell StressFlux Work Work.A05 MeasureTheory Next.UVStress Spin
open scoped Topology BigOperators InnerProductSpace Classical ContDiff
variable {G:Gauge}{C:Family G}{p:Extraction.Order}{S:Table C.book}(H:(Bel C.book).Hierarchy){n:ℕ}
local notation "F₀" => Bel C.book
variable (F: Spec.Final C p S)(h:G.Simple){𝓛:Ultrafilter (ℕ×ℕ)}

/-- tested square to the orders determining the coefficient. Column test E
 needs grade through 1, others (B,R,Q) only grade 0. -/
structure Easel where
   b : ℂ
   e : Fin 2 → ℂ
   r : ℂ
   q : ℂ

structure Easel.Verified (X:Easel)(P:ℝ→change S 4)(χ:E4→ℝ) (u:ℝ→ℝ):Prop where
   shape : Window sail χ
   field : Tendsto (B P) trail (𝓝 X.b)
   mix : Tendsto (fun s=> (u s ^ (2:ℕ))⁻¹ • (E P s-X.e 0)) trail (𝓝 (X.e 1))
   shell : Tendsto (R P χ) trail (𝓝 X.r)
   residual : Tendsto (Q P χ) trail (𝓝 X.q)
-- use κ only through 0, set d=grades 0 and1; enforce leading conservation solve at 0 and translation at 0.
structure Easel.System (X:Easel)(κ:ℝ)(d:Pilot.Jet):Prop where
   lane : κ • (X.e 0)+ d 0 • X.b =0
   normalized : κ • X.r +d 0 • X.q=X.b
   mixed : ∀ k':ℝ,∀ b':ℂ, κ • (X.e 1)+k' • (X.e 0)+d 1 • X.b+d 0 • b'=0

def limitE (C:Family G)(χ:E4→ℝ):Easel := ⟨datum C, ![0,(-d2 G) • datum C],datum C,prism C χ⟩

lemma limit_sol (χ:E4→ℝ): Easel.System (limitE C χ) 1 (![0,d2 G]:Pilot.Jet):=by
   constructor
   · simp [limitE]
   · simp [limitE]
   intro k b; simp[limitE]
include H h in
lemma normalized_sol (χ:E4→ℝ)(κ:ℝ)(d:Pilot.Jet)(ht:Easel.System (limitE C χ) κ d): κ=1 ∧ d=(![0,d2 G]:Pilot.Jet):=by
   obtain ⟨ha,hp,ht⟩:=ht; specialize ht 0 0
   simp only[limitE,Matrix.cons_val_zero,Matrix.cons_val_one,zero_smul,smul_zero,add_zero,zero_add] at *
   have hn: datum C≠0:= sail_b H h
   have hz:d 0=0:=smul_left_injective ℝ hn (ha.trans (zero_smul ℝ _).symm); rw[hz,zero_smul,add_zero] at hp
   have he:κ=1:=smul_left_injective ℝ hn (hp.trans (one_smul ℝ _).symm)
   have hb:d 1=d2 G:=smul_left_injective ℝ hn (by rw [he,one_smul, neg_smul, neg_add_eq_zero] at ht; exact ht.symm)
   exact ⟨he,funext (Fin.forall_fin_two.mpr ⟨hz,hb⟩)⟩

variable {u d:ℝ→ℝ}{P:ℝ→change S 4}(hg:Coupling G u)(hp:TendC F P d)(hP:PlotX F H 𝓛 h P)(he:∀ m:ℕ,∀ᶠ r in trail, chores r (P r) m)
include hP hp hg H F he
lemma formed : ∃ κ e:ℝ→ℝ, (∀ᶠ r in trail, Measures F r (P r) (κ r) (d r) (e r)) ∧ Tendsto κ trail (𝓝 1)∧ Through u d (![0,d2 G]:Pilot.Jet) ∧ (∀ (χ:E4→ℝ), Window sail χ → LiveP P κ d χ ∧ Easel.Verified (limitE C χ) P χ u):=by
   obtain ⟨κ,e,hk⟩:= promo H F h hg hp hP; obtain ⟨χ,hχ⟩:= has_window sail sail_at
   have hb(χ)(hχ:Window sail χ): LiveP P κ d χ:= lift_ward H F h hg hp hP hk χ hχ
   refine ⟨κ,e,hk,akela H F h hg hp hP hχ (hb χ hχ) he,?_,?_⟩
   · unfold Through; rw[show (![0,d2 G]:Pilot.Jet) 0=0 from rfl]; simp only[sub_zero];rw[force_b G]; exact hp.measures u hg
   intro φ hφ; refine ⟨hb _ hφ,⟨hφ,(station_limits H F h he φ hφ).2.1,?_,(station_limits H F h he φ hφ).1,(station_limits H F h he φ hφ).2.2⟩⟩; change Tendsto (fun t=> (_:ℝ) • (E P t-0)) _ _; simp only[sub_zero];exact eid H F h hg hp hP hφ (hb φ hφ) he
end YM.Trace.Pith
#print axioms YM.Trace.Pith.formed
