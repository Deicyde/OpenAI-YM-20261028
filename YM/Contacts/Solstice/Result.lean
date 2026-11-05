import YM.Contacts.Solstice.Ledger
import YM.Contacts.Layers.Conclusion
/-!
# Euclidean distributions at multiple collisions
`celestial` constructs the Wilson hierarchy and the subtraction data. For an admissible forest, `Resolution` gives the Taylor pairing, summability and agreement with the proper-subcluster readings. On annuli away from total collapse the result agrees with the punctured correlation. `MultipleLight` and `Thresholds` specify the permitted tests, scales and finite grades, including the dependence on the chosen subtraction.
Reflection positivity of the original hierarchy is a separate statement. This extension does not establish reflection positivity on overlapping supports, contact Ward identities for arbitrary subtractions, or real-time time-ordered products.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Solstice
open Function Filter Set Metric MeasureTheory Submodule Table Spec Normal MultipleContact OPE Layers Harvest Route Transport
open scoped Topology Classical BigOperators ContDiff InnerProductSpace MeasureTheory TensorProduct
variable {G: Gauge} {C: Family G}{F:Extraction.Order}{S:Table C.book}
variable {k : ℕ} {g : Normal.Group k} {E W I J X : Type}
variable [NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
variable [MeasureSpace E][BorelSpace E][(volume:Measure E).IsAddHaarMeasure]
variable [NormedAddCommGroup X][NormedSpace ℂ X][NormedSpace ℝ X][CompleteSpace X]
variable [Fintype I] {d:Fin k→ℕ}
variable (Z:Final C F S)(M:Devices Z.sector.derivatives)

/-- Properties of full contact resolution on any admissible continuation, including at separated patches. -/
structure Resolution (P:E→ₗᵢ[ℝ] Points k) (Q : Pieces g) (r:Route P Q I W) (B:W→ℝ)(T: W→ Cells S d)(D: Reader E W X k Z.sector.derivatives) : Prop where
    estimates (γ:ℝ)(hp : Economy Q γ) : ∃ C>(0:ℝ),Achieves Z M r T B D γ C
    root_formula (f:Menu k)(w:W)(p:SmoothTests E)(hp : tsupport p.val ⊆ r.stage w) (i:Q.parts)(hh:1 < i.val.card)(hf:f i.val=Ballot.whole) :
       (∫ x,r.windings M D T f w p x) = ∑ v:Way d i.val, ∑' n:ℕ, ∫ x,r.beckon M T D i v f w p n x
    interior_calls (f:Menu k) (w:W)(p:SmoothTests E)(hp : tsupport p.val ⊆ r.stage w)(i:Q.parts)(hh:1 < i.val.card)(v:Way d i.val):
        let F:= r.select M T D i v f w (r.net i v w p); let K:= r.beckon M T D i v f w p
        Integrable F ∧ (∀ n,Integrable (K n)) ∧ Summable (fun n=>∫ x,‖K n x‖) ∧ HasSum (fun n=>∫ x,K n x) (∫ x,F x)
    places (f:Menu k) (L:List Q.parts) (h:Route.Centered Q f L) (w:W)(p:SmoothTests E)(hp: tsupport p.val⊆r.stage w) :
       Summable (fun n:Overtures L=> ∫ x,‖r.windings M D T (Route.march f L n) w p x‖) ∧ HasSum (fun n:Overtures L=>∫ x,r.windings M D T (Route.march f L n) w p x) (∫ x,r.windings M D T f w p x)

structure Sunshine (Z:Final C F S)(M:Devices Z.sector.derivatives)(P:E→ₗᵢ[ℝ] Points k)(g : Normal.Group k)(r:Route P (root g) Unit W) (hg:g.Nonempty)
     (T : W→Cells S d){v:J→ℕ}[Fintype J](θ : Backdrop S r v)(α: W→Viewers Z):Prop where
    raw_power ε : 0<ε → Claim r M T (θ.polls M α) ε 0
    output ε : 0<ε → ∀ n,sees M (clasp g hg) n r → Claim r M T (rootCoeff r M n) ε n
    remainder ε : 0<ε → ∀ n,sees M (clasp g hg) n r → Claim r M T (θ.controlled M (clasp g hg) n false α) ε (n+1:ℝ)
    punct (h:1< g.card) :
        (∀ ε:ℝ,0<ε → Annulus r M T (θ.polls M α) ε 0) ∧
          ∀ n,sees M (clasp g hg) n r → (∀ ε:ℝ,0<ε → Annulus r M T (rootCoeff r M n) ε n) ∧ Annulus r M T (θ.controlled M (clasp g hg) n false α) (1/2:ℝ) (n+1:ℝ)

variable (H:Services C F S)
include H
lemma commissions (P:E→ₗᵢ[ℝ] Points k) (Q : Pieces g) (r:Route P Q I W) {B T D} (h : Given (d:=d) T) (he : r.Authority M d) (hv : Loan Z M r B (show Reader E W X k Z.sector.derivatives from D)) : Resolution Z M P Q r B T D:= by
   refine ⟨fun _=> achieved _ _ _ _ H hv he h, fun f w p hp i hh hf=> ownformula i hh f w p hv h he H hp hf, fun f w p hp i hh v=> ?_, fun f L h' w p hW=> ⟨(canopy f L hv h he H hW h').2, cartesian f L hv h he H hW h'⟩⟩; have ht:=emphatic i hh v f w p hv h he H hp; exact ⟨ht.1,ht.2.1,ht.2.2.1,ht.2.2.2.1⟩
lemma collars (P:E→ₗᵢ[ℝ] Points k) (Q : Pieces g)(r:Route P Q I W)(T : W→Cells S d)(h:Given T)(he:r.Authority M d) {v:J→ℕ}[Fintype J](θ : Backdrop S r v){δ:ℝ}(hθ:θ.Eligible δ)(α:W→Viewers Z) : Resolution Z M P Q r 1 T (θ.polls M α):= commissions Z M H _ _ _ h he (Backdrop.hierarchy_cost hθ H)
lemma summers {J:Type}{P:E→ₗᵢ[ℝ] Points k} (r:Route P (root g) Unit W)(hg:g.Nonempty){T:W→ Cells S d}(hs : Run r)(hT : Given T)(hm:r.Authority M d){v:J→ℕ} [Fintype J]{θ : Backdrop S r v}(α : W→ Viewers Z){δ : ℝ}(he : θ.Eligible δ): Sunshine Z M P g r hg T θ α:= by
    have h₁(ε:ℝ)(h:0<ε):=full_power (α:=α) hg hs hT hm H h he; have h₂(ε:ℝ)(h:0<ε) (n:ℕ) (x:sees M (clasp g hg) n r):= coeff_power hg hs hT hm H h x; have h₃(ε:ℝ)(h:0<ε)(n:ℕ) (x:sees M (clasp g hg) n r):= rem_power (α:=α) hg hs hT hm H h x he
    exact ⟨h₁,h₂,h₃,fun h=> ⟨fun ε x=> poke (h₁ _ x) h, fun n hi=> ⟨fun ε hx=> poke (h₂ _ hx _ hi) h, poke (h₃ (1/2:ℝ) (by norm_num) _ hi) h⟩⟩⟩
omit H

structure MultipleLight (Z:Final C F S)(M:Devices Z.sector.derivatives) : Prop where
   services : Services C F S
   sameRotation : M.rotation= Z.sector.turns
   slope :
       ∀ (E W J : Type) [NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
           [MeasureSpace E][BorelSpace E][(volume:Measure E).IsAddHaarMeasure] {k : ℕ}{P:E→ₗᵢ[ℝ] Points k}{g:Normal.Group k}(r:Route P (root g) Unit W) (hg:g.Nonempty) (d : Fin k→ℕ) (T:W→ Cells S d), Run r → Given T → r.Authority M d → ∀ (v:J→ℕ)[Fintype J](θ:Backdrop S r v) (α:W→Viewers Z) (δ:ℝ), θ.Eligible δ → Sunshine Z M P g r hg T θ α
   moment :
       ∀ (E W I J : Type) [NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
           [MeasureSpace E][BorelSpace E][(volume:Measure E).IsAddHaarMeasure] [Fintype I] {k:ℕ}{P:E→ₗᵢ[ℝ] Points k}{g:Normal.Group k}{Q:Pieces g} (r:Route P Q I W) (d:Fin k→ℕ)(T:W→Cells S d), Given T → r.Authority M d → ∀ (v:J→ℕ)[Fintype J] (θ:Backdrop S r v)(α:W→Viewers Z) (δ:ℝ), θ.Eligible δ → Resolution Z M P Q r 1 T (θ.polls M α)
   distribution :
       ∀ (E : Type) [NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
        [MeasureSpace E][BorelSpace E][(volume:Measure E).IsAddHaarMeasure] {k:ℕ}(P:E→ₗᵢ[ℝ] Points k) g o, plane g ≤ LinearMap.range P.toLinearMap → Collapsed g o → ∀ (d:Fin k→ℕ)(t:Cells S d) (α : Viewers Z) (B s:ℝ), B∈ Ioc 0 1 → B ≤ M.clearance (∑ i,d i+0) → 0<s ∧2*s≤B → Charge (majorKernel P g M t α o s) ⊤ (totalTestOrder d g)

lemma provided (h: M.rotation=Z.sector.turns)(H:Services C F S): MultipleLight Z M:= by
   refine ⟨H,h,?_,?_,?_⟩
   · intros; apply summers Z M H <;> assumption
   · intro E W I J _ _ _ _ _ _ _ k P g Q r d T h hm v _ θ α δ hF; exact collars Z M H P Q r T h hm θ hF α
   intro E _ _ _ _ _ _ k P g o h hh d t α B s hW hv hb; exact global_charge h hh t α hW hv hb H

/-- `celestial` gives the calibrated family with all projection choices working in genuine open
forests.

Instantiate all the above resolution properties with its `services`.

The existence conclusion is combined here, no consumer needs a strengthened
existence oracle. -/
theorem celestial (G:Gauge) (h:G.Simple) : ∃ (C:Family G)(F: Extraction.Order)(S:Table C.book)(Z: Spec.Final C F S) (M:Devices Z.sector.derivatives), MultipleLight Z M ∧ Nonempty (Transport.SystemBasis M) ∧ Nonempty (Thresholds M):= by
   obtain ⟨C,F,S,Z,M,e,H,hM⟩:= Layers.signed_placements G h; exact ⟨C,F,S,Z,M,provided Z M e H, real_basis M,⟨ (installs M (f:=fun i=>1) (fun i=>zero_lt_one)).choose⟩⟩
end YM.Contacts.Solstice

#print axioms YM.Contacts.Solstice.celestial
