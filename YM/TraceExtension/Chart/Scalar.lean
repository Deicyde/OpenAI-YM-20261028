import YM.TraceExtension.Chart.Nectar
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Over
open Function Filter Lattice RG Wilson Labels Source Extra.Histories Bid MergeProof.Accent MergeProof
open Extraction Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Climb Analysis Work
open MeasureTheory
open Further.PhysicalPeriodLimitF933 Shunt Weir PhysicalNext.Repeat.Legato.Bandage Push.GridApprox Cells
open Relay Pull Terrace Terrace.Glade Perfect Turret Margin Slate Shelves
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}
variable (P:C.Makes) (h:G.Simple) (θ:PostT C.path.levels)(K:Stock.Tabs C.path.levels)
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p i:ℕ,i<N→GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)}
variable (ht:Scrim C W u ψ φ δ (fly C.path.levels) r D)(hM:Sceptre C W) (hT:supportQ C.path.levels)
variable {F:Extraction.Order}{𝓛:Ultrafilter (ℕ×ℕ)} (hb:(𝓛:Filter (ℕ×ℕ))≤F.fuse)
set_option quotPrecheck false
local notation "A"=> C.path.levels
local notation "V!"=> C.path
local notation "b!"=> (𝓛:Filter (ℕ×ℕ))
local notation "H!"=> C.path.levels.clock.hatBeta
variable {t:Tickets C} (hu:Grant C (𝓛:Filter (ℕ×ℕ)) t)
open Zn
variable {d:ℕ}{Z:Arch C}(hz:steep 𝓛 Z)
open Finset StressFlux
local notation "Fᵣ"=> C.labels.level 4
local notation "Zᵣ"=> C.labels.level 5
variable {X:Axis→ Logs C 5}(hp:∀ i,TravelsC (𝓛:Filter (ℕ×ℕ)) (exhibit t i) (Readout t i) (X i).v (X i).x)
open StressFlux Next.UVStress Margin
variable (Hδ:Moonlit C.path r (PhysicalNext.Repeat.Legato.Bandage.renal C.path.levels) u D)(hr:∀ᶠ i in atTop,2 ≤ r i)(hA:auraQ C.path.levels TileNo)
variable {L:PaceBook C}(hL:Rod t none (𝓛:Filter (ℕ×ℕ)) L)
variable {S:Table C.book}{J:Scaling S}{H:(Cells.standard C).Hierarchy}{V:∀ i,Vane C i}{Y:∀ d i:ℕ,(Cells.standard C).Field d→L[ℂ] C.label d}(hq:Gondola F H J 𝓛 V Y)
variable (H':S.Hierarchy)(HF:F.PointLimits C S) (hq': StarPath F H J H' 𝓛)
variable {S₁:DiffPlan S}{P₁:DiffPlan (Cells.standard C)} (hJ:S₁.Derivatives S)(hP:P₁.Derivatives (Cells.standard C)) (ho:P₁.Orientation H.spin)
variable {s:ℕ→ Bowl (C.labels.level 5) →L[ℝ] (TableOne H.spin)} (hY:Spun Z J V H s)
open Asymptotics
local notation "F!"=> Cells.standard C
local notation "P!"=> Stern V
open Spec TraceExtension Table
local notation "Fo"=> Climb.Bel C.book
-- H invariants weight-four for real scalar == these two magnetic directions.No SO caveat for *scalar d reading*.
def ScalarP(C:Family G): CP→ₗ[ℝ] (Climb.Bel C.book).Field 4:=(LinearMap.proj (0:Fin 2)).smulRight ((Climb.Bel C.book).unit 4)+(LinearMap.proj (1:Fin 2)).smulRight ((4:ℝ) • OScale C.book)
lemma Scalar_inj(h:G.Simple)(a:(Climb.Bel C.book).Hierarchy): Injective (ScalarP C):=by
    have hu : expectation (Climb.Bel C.book) 4 ((4:ℝ) • OScale C.book)=0:=by
        rw[← sum_delta (C:=C),map_sum]; apply Finset.sum_eq_zero; intro i _; rw [expectation_is]; unfold materialB; rw [show oneStress _ _ _ _ _=_ from oneStress_formula (L:=C.book) _ i i 0];norm_num
    have hv : (OScale C.book)≠0:=by
        intro he; change (Climb.Bel C.book).project 4 ((Fᵣ).coords (square4 G))=0 at he
        have hx:= sane4 (C:=C) h; exact square_alive h ((Fᵣ).coords.injective ((hx.1 (he.trans (map_zero _).symm)).trans (map_zero _).symm))
    apply LinearMap.ker_eq_bot.mp; apply LinearMap.ker_eq_bot'.mpr; intro u ht';
    let t:=(expectation (Climb.Bel C.book) 4).restrictScalars ℝ; let y:=OScale C.book; let A' := (Fo).unit 4; change u 0 • A' + u 1 • ((4:ℝ) • y)=0 at ht'; have hx : (u 0)=0:=by
        have ht:=congr_arg t ht'; rw [map_add,map_smul,map_smul, show t A'=1 from mean_unit a.laws, show t ((4:ℝ) • y)=0 from hu,map_zero] at ht; simpa [Complex.real_smul] using ht
    rw[hx,zero_smul,zero_add] at ht'; exact funext (Fin.forall_fin_two.mpr ⟨hx,(smul_eq_zero.mp ht').resolve_right (smul_ne_zero (by norm_num) hv)⟩)
lemma Scalar_onto(h:G.Simple)(t:(Fo).Field 4)(hv:conjQ H.spin t=t) (hy:∀ s:Signed,spinQ H.spin s t=t):∃ x, ScalarP C x=t:=by
    let J(i j:Axis):= if i=j then t else 0
    have hs : J∈ TableTwo H.spin:=by
        refine ⟨fun i j=> by unfold J; by_cases h:i=j <;> simp [eq_comm,h], fun i j=> ?_ , fun s a b=> ?_⟩
        · unfold J;split_ifs <;> first| exact hv|exact map_zero _
        unfold J; simp only [s.perm.injective.eq_iff]; split_ifs with h
        · subst b; rw [hy,←sq,sign_sq,one_smul]
        rw [map_zero,smul_zero]
    obtain ⟨w,hw⟩:= (free_stress_bij (L:=C.book) h H.spin).2 ⟨_,hs⟩
    let F:= Fo; let c:= w 1+4*w 2; let u:= OScale C.book
    have he : (∑ i:Axis, material F w i i)=(4:ℝ) • t:=by
       have hv(i:Axis): material F w i i=t:= (show material F w i i=J i i from congr_fun (congr_fun (congr_arg Subtype.val hw) i) i).trans (by simp[J]); simp_rw[hv];rw[Finset.sum_const,Finset.card_univ,show Fintype.card Axis=4 from Fintype.card_fin _];
       module
    have hg(i:Axis): fromPol F (Labels.unit G 4)= F.unit 4:= UVNext.FreeStress.pin_unit ..
    have hp: (∑ i:Axis, material F w i i)= (4:ℝ) • (w 0 • F.unit 4)+(4*c) • u:=by
        unfold StressFlux.material; simp_rw [stress_of,if_true, map_add,map_smul,hg 0,map_sum,Finset.sum_add_distrib];
        have hv:u=(1/4:ℝ) • ∑ i:Axis,∑ j:Axis,fromPol F (StressFlux.pair G i j i j):=by unfold u OScale square4; rw[map_smul,map_sum]; congr 2; ext1 i; rw [map_sum]
        rw [hv]; simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Finset.smul_sum]; unfold c; module
    refine ⟨![w 0,c/4],?_⟩; rw [hp] at he; change (w 0 : ℝ) • ((Fo).unit 4)+ (c/4:ℝ) • (((4:ℝ) • OScale C.book):(Climb.Bel C.book).Field 4) = t; apply smul_right_injective _ (by norm_num :(4:ℝ)≠0); change (4:ℝ) • _= (4:ℝ) • t; rw [← he]; unfold u F; module
variable {A':Spec.Algebra S} {T₀:Table C.book} (hν:Locals A' H'.spin)(hr_ : T₀.respects S)(H₀:T₀.Hierarchy)
include h H hν hr_ H₀ in
lemma payload (a:ℕ→ℝ) (hc:∀ᶠ i in atTop,Coherent H.spin H'.spin 4 (J.U i 4)) : ∀ᶠ k in atTop,∃ v:CP, ZoomValue J a (TraceExtension.theta T₀ A'.energy) k=ScalarP C v:=by
    filter_upwards[hc] with i hi; let x:= TraceExtension.theta T₀ A'.energy; have hx : S.conj H'.spin 4 x=x:= trace_real hν.conserved hr_ H₀
    have hv (s:Signed):S.mirror H'.spin 4 s x=x:=by rw[← hν.spots.signed];exact trace_turn hν.spin hν.spots s.ortho
    let p:=a i*J.r i^(4:ℕ); let U:= (J.U i 4).symm; let v:=U (p • x); have he:= flips hi
    have hp(s):spinQ H.spin s v=v:=by
         change (Fo).mirror H.spin 4 s (U _)=_; rw[← he.signed,show S.mirror H'.spin 4 s (p • x)= p • S.mirror H'.spin 4 s x from ((S.mirror H'.spin 4 s).restrictScalars ℝ).map_smul p x,hv]
    have hg: conjQ H.spin v=v :=by
         change (Fo).conj H.spin 4 (U _)=_;rw[← he.stars,show S.conj H'.spin 4 (p • x)=p • S.conj H'.spin 4 x from (conjQ H'.spin).map_smul _ _,hx]
    obtain ⟨z,h'⟩:=Scalar_onto (C:=C) (H:=H) h v hg hp; exact ⟨z,h'.symm⟩
end YM.Trace.Over
