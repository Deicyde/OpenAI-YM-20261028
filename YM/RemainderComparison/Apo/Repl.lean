import YM.RemainderComparison.Breeze.Sonar
import YM.RemainderComparison.Herbal.Orbit
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Apo
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι β : Type} {α:Type*}
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (H:Cash W x μ L Q o C T R) {q A B b e u v d L' Gp:ℝ}{j n k s J I:ℕ}(χ:Chi)
open Lyric Mosaic Muse Sleet Serif Typeface
variable (U:Pad H j χ)
local notation "P₀"=> tax G L x
variable {τ κ K Y γ V T0:ℝ}
variable (M:ι→Portrait R α) (x' y:α) (l:ι→ℝ)(Z:Set ι)(δ:ℝ)
variable (h:Roles H χ U k s J I a d e K σ Y γ V T0) (hh:Motto (brand M x') l δ H τ K Y I)
local notation "Lt"=> sits Z l δ
local notation "Vx"=> brand M x'
local notation "Vy" => brand M y
variable [DecidableEq β]{Jm:Marker.Census β}
variable (z:ι→Marker.Poly Jm) {gP:β→ℝ} (hZ : Chorus Jm gP Z z k)
open Mallow Ovens Progress.DirectedRecipe
open WickReps
local notation "Tt"=> Sleet.Staff Vx H
local notation "Σ₁" => Mosaic.etude Vx H χ
local notation "Σ₂" => Mosaic.etude Vy H χ
open Mosaic Serif
open Aux Portal -- Conflict sunny! Qualify.
-- Pieces of a CAR sorted before AUX comparison. Require original Road
-- structure enough to link EACH reply, including all TEST α at once.
-- This layer only processes stamps.
local notation "Zʼ"=> (Set.univ:Set ι)
local notation "A₀" => Creek.theater H χ M x' l Set.univ δ
local notation "Rt" => Flues.candle M x' S
variable (P': BudgetPoint)
open Marker Next.Rank.Glyph Next.Rank.Exponential
lemma scrub (i:Tt) : (A₀).solvent y i= Sleet.charge Vy H χ l i:=by
   have he: ∀ z:Multiset ι,Mosaic.Verse.load Zʼᶜ z=0:=by simp [Mosaic.Verse.load]
   funext x
   unfold Creek.theater; dsimp only; unfold Muse.sits; rw [Verse.excursion,he,pow_zero,one_mul,Verse.emit, Mosaic.pieces]; rfl
lemma strum (s:Finset Tt): Portal.bar Vy H χ l (s:Set Tt)=fun V=> ∑ i∈s,(A₀).solvent y i V:=by
    funext V; let f:Tt→ℝ:=fun i=>Portal.heed Vy H χ l (s:Set Tt) i V;
    change (∑' i,f i)= _; rw [tsum_eq_sum (f:=f) (s:=s) (fun _ h=> if_neg h)]
    refine sum_congr rfl fun i hi=>?_ ; rw [scrub]; exact if_pos (show i∈ (s:Set Tt) from hi)
variable {E0 : Set (Sleet.Staff (Typeface.brand M x') H)}
lemma shieldP (he: Manor.Spinal A₀ E0 Rt P' a u) : Rendition Vy H χ l P' E0 a u:=by
   obtain ⟨w,h,hp,hδ⟩:= Manor.Spinal.grants he; let f i:=if i∈E0 then w i else 0; have hf i:0 ≤ f i:=by unfold f; split; exact h _; exact le_rfl
   refine ⟨f,hf,fun i hi=> if_neg hi, fun i hi=>?_, fun x=>?_⟩
   · rw [← scrub H χ M x' y l δ, show f i=w i from if_pos hi, ← show Manor.halls A₀ i=Base Vy H i from Creek.point H χ M x' l Set.univ δ i]; exact ⟨(hp i hi).1.angle _,(hp i hi).2 _⟩
   refine budget_mono (hδ x) (fun i=>by split; exact mul_nonneg (hf _) (Real.exp_nonneg _); exact le_rfl) fun i=>?_
   rw [show _= Base Vy H i from Creek.point H χ M x' l Set.univ δ i]; split; next=> apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _); unfold f; split; exact le_rfl; exact h _
   next=>rfl

local notation "Pt"=> fun i: Staff Vx H=> Pure Vx H χ Set.univ k i
local notation "At" => Creek.Academy H χ M x' l Set.univ δ k
set_option quotPrecheck false
local notation "So" => {p|p∈At ∧ Pt p ∧ ¬ Halo.dyed Vx H (∅:Set ℕ) p.1 p.2}
variable [Fintype ι] (μ':modes ι)
local notation "Or" => Portal.ringSet Vx H μ'
lemma cap (hk: μ'.val.card ≤ k): Or ⊆ So:=by
    intro i hi; have ht:=Portal.thins Vx H i μ' hi -- implicit args
    let z:= (etude Vx H χ i.1 i.2).letters
    have h : z.Nodup:= (Creek.rounds H χ M x' l Set.univ δ i).2 hi.1
    have hz : Mosaic.Verse.load Set.univ z=z.card:=by simp [Mosaic.Verse.load]; -- edit
    have hh : Verse.load Set.univ z ≤ k:=(hz.trans ((Muse.scores Vx H χ i.1 i.2).trans ht)).trans_le hk
    refine ⟨⟨hh,?_⟩,⟨?_,hh⟩,fun h=> ?_⟩
    · exact @Multiset.Nodup.filter ι (fun x=>x∈ (Set.univ:Set ι)) (fun _=> Classical.propDecidable _) z h
    · change Verse.load _ z=0; simp [Mosaic.Verse.load]
    obtain ⟨a,b,⟨p,hp,_⟩,-⟩:=h; exact hp
lemma rainy : Or = ringSet (brand M y) H μ':= rfl

-- Model presented after analytic m sections. Ledger.Spine at lengths.
-- exact Ψ on Sunny, may be total mark. Might be singular series outside Sunny, not asserted analytic there.
-- keep jet errors tolerance separate.
section
open WickReps Manor
variable (Fa:Manor G c ι α β) (pP:Set β)(u':α)(o':ι→Support c)
omit [Fintype ι] [DecidableEq β]
local notation "X₀" => Fa.solvent

def stump (s:Set β)(a:α):s→ Config G c→ℝ:=fun x=>Fa.solvent a x.val
local notation "F₁"=> stump Fa

def slab (S:Finset β)(a:α)(V:Config G c) := ∑ i∈ S,Fa.solvent a i V

def whole (a:α) := Portal.unite (Fa.solvent a)
lemma sublimed (hf: Fa.Spinal pP o' P' a b)(hx:0≤a): Tally P' ↥pP (F₁ pP u') (Fintype.card (Site c)*b) := by
    obtain ⟨f,h,hp,hP⟩:= hf.templary.grants
    have hg : SumBudget f (Fintype.card (Site c)*b):= by
       convert budget_mono (budget_over univ _ _ fun i (_:i∈_)=> hP i) h ?_ using 1
       · rw [sum_const,nsmul_eq_mul,card_univ]
       intro i; simp only [sum_ite_eq,mem_univ, ↓reduceIte]; exact le_mul_of_one_le_right (h _) (Real.one_le_exp (mul_nonneg hx (by positivity)))
    apply Portal.fuel (K:=Fa.halls ∘ Subtype.val) (Fa.port ∘ Subtype.val) ⟨f ∘ Subtype.val, budget_pull Subtype.val Subtype.val_injective hg,fun ⟨i,hi⟩=>⟨(hp i hi).1.angle _,(hp i hi).2 _⟩⟩
lemma stays (s:Finset β)(hf:Fa.Templary (s:Set β) o' P' a b): P'.Regular univ (slab Fa s u'):=by
    rw [show slab Fa s u'=∑ i∈s,Fa.solvent u' i from funext (fun x=> by rw [Finset.sum_apply]; rfl)]
    refine Meadow.regularA s ?_; exact fun i hi=> AnalyticBridge.CouplingShape.reg_extend ((hf.grants.choose_spec.2.1 i hi).1.angle _) (subset_univ _)
lemma stays_at (s:Finset β)(h: Tally P' ↥((s:Set β)ᶜ) (stump Fa ((s:Set β)ᶜ) u') a)(V:Config G c)(hp:V∈Boulevard.sunny P') : whole Fa u' V= slab Fa s u' V + Portal.unite (stump Fa ((s:Set β)ᶜ) u') V:=by
    have hf:= (Portal.levy h V hp).1
    have hx: Summable (fun i: ↑s=> Fa.solvent u' i.val V):= Summable.of_finite
    unfold slab whole Portal.unite; rw [← Finset.sum_coe_sort, ← tsum_fintype (L:=.unconditional _)]; exact (Summable.tsum_add_tsum_compl (s:=s) (f:=fun i=> Fa.solvent u' i V) hx hf).symm
end
end YM.RemainderComparison.Apo
