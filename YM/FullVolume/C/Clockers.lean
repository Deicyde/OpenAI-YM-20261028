import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Rain.Innings
/-! Ordinal.Clock staging. A `keep` test is not coefficient dependent.
`bouquet` withdrawal formulas (not just tests) are beta only. Important
when applying sectors to trajectories that do not come from a compact input curve.
 *literal* indexing: doesn't use proof uniqueness of a Cash. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Match
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f L₀ : Side} {K : Teller G} {p a W U : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' Q : RG.Rep G f} {H : Cash W p a L₀ X o U T R} {I: Cash W p a L₀ X o U T R'} {χ : Chi} {F : Tree.Forest S.ratio}
variable (P : Match.Alliance H I 1 0) (hz:P.units=Equiv.refl _)
variable (hp:R.path=R'.path) (he:R.activities.reg=R'.activities.reg) (hk:R.activities.forced=R'.activities.forced)
lemma local_units {P A:Match.Alliance H I 1 0} (hh : P.units=A.units) : P=A:=by cases P; cases A; congr
include hp he hk
lemma signage (r) : Beam.marquee H r= Beam.marquee I r:=by
  obtain ⟨u,c,⟨s,v,e1,k1⟩,p,b,t⟩:=R
  obtain ⟨U,C,⟨S,V,e2,k2⟩,P,B,T₁⟩:=R'
  cases hp; cases he; cases hk; rfl
include P hz
def sheet : Magazine H ≃ Magazine I := Equiv.sumCongr P.furrow (Equiv.refl _)
lemma migrate (d : ℕ) (i:Magazine H) : (Meadow.keep H i ↔ Meadow.keep I (sheet P i)) ∧ (i∈ Meadow.bouquet H d ↔ sheet P i ∈ Meadow.bouquet I d):=by
  have hK := Match.same_area (J:=I) (H:=H) hp he hk
  rcases i with z|z
  · let V:= firstBatch hp hK
    have hv (i:Poet H): i ∈ Meadow.calendar H d ↔ V i∈Meadow.calendar I d:= by rw [tunes,tunes]; rfl
    refine ⟨not_congr (holdings P hp hz hK z),?_⟩
    change _↔ Sum.inl (P.furrow z) ∈_
    simp only [Meadow.bouquet,inl_mem_disjSum,Finset.mem_map]
    constructor
    · rintro ⟨i,hi,rfl⟩; exact ⟨V i,(hv i).1 hi,(identifies P hp hz hK i).symm⟩
    rintro ⟨i,hi,hu⟩; obtain ⟨i,rfl⟩:= V.surjective i; exact ⟨i,(hv i).2 hi,P.furrow.injective ((identifies P hp hz hK i).trans hu)⟩
  change (Meadow.keep H (Sum.inr z) ↔ Meadow.keep I (Sum.inr z)) ∧ _
  refine And.intro (show (radiusB p<_) ↔ (radiusB p< arc T.down z) from Iff.rfl) ((Finset.inr_mem_disjSum).trans Finset.inr_mem_disjSum.symm)
lemma flyer (i:ℕ): (pennant I i).2=sheet P (pennant H i).2:=by
  obtain ⟨u,c,⟨s,v,e1,k1⟩,p,b,t⟩:=R
  obtain ⟨U,C,⟨S,V,e2,k2⟩,p,B,T₁⟩:=R'
  cases hp; cases he; cases hk; obtain ⟨_,_,_⟩:=P; cases hz
  have hv (i:Magazine H):sheet (H:=H) (I:=I) (Match.staple rfl rfl rfl) i=(show Magazine I from i):=by rcases i with i|i <;> rfl
  exact (hv (pennant H i).2).symm
omit hz P in
lemma stamped (d i : ℕ):debris H d i ↔ debris I d i:=by
  let V := staple (H:=H) (J:=I) hp he hk
  unfold debris; rw [flyer V rfl hp he hk]; obtain ⟨h,hx⟩:= migrate V rfl hp he hk d (pennant H i).2; exact and_congr (not_congr h) (not_congr hx)
variable (χ) -- order
lemma upward {I': Cash W p a L₀ X o U T R'} (γ:ℝ) : Song.plusone H P χ γ=Song.plusone I' (Match.staple (J:=I) rfl rfl rfl) χ γ:=by
  obtain ⟨u,c,⟨s,v,e1,k1⟩,p,b,t⟩:=R
  obtain ⟨U,C,⟨S,V,e2,k2⟩,p,B,T₁⟩:=R'
  cases hp; cases he; cases hk; obtain ⟨_,_,_⟩:=P; cases hz; rfl
lemma written {I': Cash W p a L₀ X o U T R'} (γ:ℝ) (d:ℕ): Meadow.timbres P (χ:=χ) γ d= Meadow.timbres (Match.staple (H:=I') (J:=I) rfl rfl rfl) (χ:=χ) γ d:=by
  have he₁ := upward (I':=I') χ P hz hp he hk γ
  let V:= Match.staple (H:=H) (J:=I') hp he hk
  have he₂ : (timbres P (χ:=χ) γ d).logRead=(timbres (Match.staple (H:=I') (J:=I) rfl rfl rfl) (χ:=χ) γ d).logRead := by
    ext1 i; rw [compass, he₁, compass]
    rw [(flyer V rfl hp he hk i)]
    exact if_congr (migrate V rfl hp he hk _ _|>.2) rfl rfl
  unfold Meadow.timbres; rw [Collection.Source.mk.injEq]; exact ⟨he₂, congr_arg Collection.Source.hardRead he₁⟩
end YM.PhysicalNext.Repeat.Meadow
