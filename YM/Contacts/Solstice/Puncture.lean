import YM.Contacts.Solstice.Scaling
/-! # Same bounds in any punctured annulus

Definition of the punctured product in the score (the one with the full-root term missing),
already including proper-stratum cumulants. The bounds pay here the actual arity weights in the
rooted integrations; when taking integrals **through** the puncture, use the cutting prescription
and the identities already established. `Loose` means off that total diagonal, not synonymous
with no collisions in the test. Our estimates not require a lower constant >0 for annulus holes.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Solstice
open Function Filter Set Metric MeasureTheory Submodule Table Spec Normal MultipleContact MultipleContact.Script OPE Layers Ordered Harvest Route
open scoped Topology Classical BigOperators ContDiff InnerProductSpace MeasureTheory
variable {E W I J X: Type}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
variable {G: Gauge}{C : Family G}{F : Extraction.Order}{S: Table C.book}{Z : Final C F S}
variable {k : ℕ}{g : Normal.Group k}{P:E→ₗᵢ[ℝ] Points k}
local notation "GN" => Normal.Group k
local notation "K!" => normalOn P g

-- untagged version mask test
omit [FiniteDimensional ℝ E] in
lemma masked_out {f v : Score E (Expression Z.sector.derivatives)} {p : SmoothTests E} (h : f * instructionScore E (Expression Z.sector.derivatives) (mask p)= v * instructionScore E _ (mask p)) (x:E) : action x p f= action x p v:= by
   let t : SmoothTests E := ⟨fun _=>1,(contDiff_const (c:=(1:ℂ)) : ContDiff ℝ ∞ (fun _:E=> (1:ℂ)))⟩; have he:= congrArg (action x t) h; rw [takeRight,takeRight] at he; rw [show mask p t=p from Subtype.ext (funext (fun x=>mul_one _))] at he; exact he

def Loose (P:E→ₗᵢ[ℝ] Points k)(g:GN)(p : SmoothTests E) := ∀ x∈ (normalOn P g)ᗮ,x∉ tsupport p.val
-- whole agrees punct (all projections collapse on punct test). Relative to actual context(s) with punct ambient.
lemma full_loose (Y : System E (Expression Z.sector.derivatives) k) (s:ℝ)(h : 1 < g.card) (f:SmoothTests E) (hh:Loose P g f)(x:E): action x f (Y.full P s g)=action x f (Y.punctured P s g):= by
    apply masked_out _ x; rw [Y.full_formula P s g (Finset.card_pos.mp (by omega)), add_mul, all_off hh (Y.translatesOrigin P s g),add_zero]

variable (r : Route P (root g) Unit W)
lemma looser {p: SmoothTests E} (h : Loose P g p)(w : W): Loose P g (normal_test r w p) := by
     intro x hx; apply notMem_tsupport_iff_eventuallyEq.mpr; have hp:= (notMem_tsupport_iff_eventuallyEq.mp (h x hx));
     have hm: (slide (normalOn P g) (scale r w)⁻¹) x=x:= slip_hide _ _ hx; filter_upwards [( ((slide (normalOn P g) (scale r w)⁻¹).continuous.tendsto x)).eventually (hm.symm ▸ hp)] with y hy; exact (scaled r w p y).trans (smul_eq_zero_of_right _ (show p.val _=0 from hy))
lemma annulus_loose (t : ℝ) (h:0<t) (p : SmoothTests E)(hh: tsupport p.val ⊆ sun (normalOn P g) t): Loose P g p := by
   intro x hx hu; have he:= (show t/2 ≤ ‖(normalOn P g).starProjection x‖ from (hh hu).1); rw [starProjection_apply_eq_zero_iff (normalOn P g)|>.2 hx,norm_zero] at he; linarith

variable (M : Devices Z.sector.derivatives){q:Fin k→ℕ}(T : W→ Cells S q)
variable [NormedAddCommGroup X][NormedSpace ℂ X]

def outsideC (w : W)(p:SmoothTests E)(x:E):=action x p ((r.components M T w).punctured P (r.length w) g)
def outsideCost (D : Reader E W X k Z.sector.derivatives)(w : W)(p:SmoothTests E)(x:E):= D w x (tag g (outsideC r M T w p x))
def festive (k : ℕ) : Menu k:= fun _=> Ballot.whole

variable {r M T}
lemma puncture_eq (D : Reader E W X k Z.sector.derivatives)(h : 1 < g.card)(w : W)(p : SmoothTests E)(hh : Loose P g p) : outsideCost r M T D w p=r.windings M D T (festive k) w p := by
   funext x; let Y:= r.components M T w; have hg:g.Nonempty:= Finset.card_pos.mp (by omega)
   unfold windings scoreAt outsideCost outsideC; rw [tag_alone hg, ← full_loose _ (r.length w) h p hh]; simp_rw [festive,System.all_votes]
-- also local smaller integral choices justified by Loan; puncture branches estimated using projection loans.
variable [MeasureSpace E][BorelSpace E][(volume:Measure E).IsAddHaarMeasure]

def Annulus (r : Route P (root g) Unit W)(M : Devices Z.sector.derivatives)(T : W→ Cells S q)(D : Reader E W X k Z.sector.derivatives)(ε u : ℝ) := ∃ C>(0:ℝ), ∀ w p (m:ℝ),Loose P g p → tsupport p.val ⊆ (barrel r w) ⁻¹' r.stage w → Jet (stairs q (root g)) univ p.val m → Dust (outsideCost r M T D w (normal_test r w p)) (C*m* scale r w ^ (u - arityRate q g- ε))
omit [BorelSpace E] [(volume:Measure E).IsAddHaarMeasure] in
lemma poke {D: Reader E W X k Z.sector.derivatives}{ε u : ℝ}(h : Claim r M T D ε u)(hp : 1 < g.card) : Annulus r M T D ε u := by
   obtain ⟨c,hc,h⟩:=h; refine ⟨c,hc,fun w p m hz hm h'=>?_⟩; rw [puncture_eq D hp w _ (looser r hz w)]; exact h w _ p m (fun i _=>rfl) hm h'

end YM.Contacts.Solstice
