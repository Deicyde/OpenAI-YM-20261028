import YM.RemainderComparison.Lacuna.Yarn
import YM.RemainderComparison.Funk.Leader
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Funk
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι δ : Type} {α:Type*}
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
open Aux Mosaic Verse Muse Apo Marker Push.Uniform Lapis Sienna Fare Boulevard Herbal WickReps Lyric Typeface
open Trio Next.Rank.Glyph Next.Rank.Exponential
variable (Q:ConnectedActivityE6.Target G P) (Ω:KernelChoices)
open Lobby Portal
open Pier Slide
variable {β:ℝ}{χ:Chi}{ιa ιb δa δb:Type}(P': BudgetPoint)
open WickReps Manor Flues Serif
-- Work proof data-choices returned. Don't require any layout after masks as hypothesis. Represent crop BEFORE additional reset.
-- Ownership interactions exported per-log & per root. ROI.Count.Val
variable (A:Manor G c ι α ιa)(F:Manor G c ι α ιb)(K:Set ιa)(E:Set ιa)(U:Set ιb)(Z:Set ι)
variable (D:Yard ι α G c)
variable {r' p B z k n I d:ℕ}{B₀ B₁ B₂ v R' v₀ v₁ N θ b b' γ ψ σ₀ g u η η':ℝ}
variable {Y:Stars→Side} (X:∀ i:Stars,(Y i).val=2*(n+i.val))(hf:2*n≤f.val)
variable {P': BudgetPoint}
variable (roots:ι→Support c)
variable (C':∀ i:Stars,Pier (Y i) G W x μ L Q o C β χ α)(S':δ→Pier f G W x μ L Q o C β χ α)
local notation "M₀"=> mural A F K

namespace Cargo
variable (o':ι→Site c) (Wc:Breeze.Careers ι δ c o' r' p) (T:Cargo Q A F K roots C' S' r')
variable (wP:ι→ ℝ)
local notation "St"=> sun o' Wc wP

local notation "Sl"=> wall Q A F K roots C' S' T
variable [Countable δ]

-- Bound.Health Λ OrientationOne
--
local notation "Mʼ"=> (Manor.mansion (ι:=ι) (c:=c) X (surge Q T.aCut T.poses) z)
local notation "Kʼ"=> (Manor.vessel M₀ T.marker hf (songs Q T.bCut) (sun o' Wc wP) k)

-- Result across TEST after Crafts
open GridRenewal.Rain
open Lobby Lacuna

def residual (z k:ℕ): Manor G c ι α (Site c ⊕ δ ⊕ ↑(Slᶜ)):= Lobby.unison (Manor.mansion (ι:=ι) (c:=c) X (surge Q T.aCut T.poses) z) (Lobby.unison (Manor.vessel M₀ T.marker hf (songs Q T.bCut) (sun o' Wc wP) k) (Lobby.peel M₀ (Cargo.wall Q A F K roots C' S' T)ᶜ))
local notation "Re"=> Cargo.residual Q A F K X hf roots C' S' o' Wc T wP z k
local notation "L₁" => (lamps Q A F K X hf roots C' S' o' Wc T wP P' z k)
def pure (a:α):=∑ x:Site c,(mural A F K).sector a T.chosen T.seats x 1
variable {dC : ℝ}
variable (hd:Cargo.Thesaurus Q A F K Z D X hf roots C' S' o' Wc T wP P' z k p σ dC b b' θ N)
variable (hU:Underscore Q A F K Z roots C' S' o' Wc T wP P')
variable (hA : A.Templary K roots P' σ B₁)(hF:F.Templary Set.univ roots P' σ B₂)(hσ:0≤ σ) {dA vF :ℝ}
-- decomposed logging law.Birth can render independently, Land.Wind
include hd
include hA hF hσ
lemma portrait_h (hg: Manor.Templary (mural A F K) (Slᶜ) roots P' σ dA):
    Lacuna.Seeds (Lobby.peel A K) F (Re) P' roots Z L₁ σ B₁ (σ+1) B₂ (dC+(b+dA)) θ N:=by
    have ht {α β : Type}: Set.univ ⊆ Lobby.switch (Set.univ:Set α) (Set.univ:Set β):=by intro i _; cases i<;>simp [Lobby.switch]
    let V':= (Slᶜ)
    have hx := Lobby.templaryPeel M₀ P' V' (p:=V') (K:=Set.univ) hg (fun i _=>i.prop)
    have hw:= (hd.marks.templary).skim (Set.Subset.refl _) (le_refl b) (show σ ≤ σ+1 from le_add_of_nonneg_right zero_le_one)
    refine ⟨Lobby.templaryPeel A P' K hA (fun i _=> i.prop),hF, ((Lobby.sumAnch Mʼ (unison Kʼ (Lobby.peel M₀ V')) P' Set.univ Set.univ ((Lobby.sumAnch Kʼ _ P' Set.univ Set.univ hx hw).skim ht le_rfl le_rfl) hd.initials).skim ht le_rfl le_rfl),hd.price,add_nonneg hσ zero_le_one,hσ⟩
local notation "Ψ"=> pure Q A F K roots C' S' T
include hU
lemma avow (hg: Manor.Templary (mural A F K) (Slᶜ) roots P' σ dA):
    Lacuna.Vision (Lobby.peel A K) F (Cargo.residual Q A F K X hf roots C' S' o' Wc T wP z k) P' Z (L₁) p (pure Q A F K roots C' S' T):=by
    constructor; intro a X' β _ _ B z' pp hZ
    let f:= Lobby.peel A K; have hx:= portrait_h Q A F K Z D X hf roots C' S' o' Wc T wP hd hA hF hσ hg
    rw [Lobby.Univ,Lobby.Univ,Lobby.Univ]
    have hz : Summable (fun i:↑K=> A.paint P' Z z' a X' i.val):= Manor.standing a X' Z z' hA hZ hσ
    have he: Summable (F.paint P' Z z' a X'):= Lobby.standing' P' a Z z' F X' hF hσ hZ
    change A.basin P' K Z z' a X'= _; rw [Lobby.unionAt _ _ P' K a Z z' X' hz he]
    have hp : (walls M₀ T.marker)⊆ (T.chosen:Set (K⊕ιb))ᶜ :=by
       rintro i ⟨x,hx⟩ ht; have h: T.marker.sign x=0:= ((T.marker.meets x i hx).2.2).symm.trans (hU.occupation.vacuum i ht); have h':= hd.situated x; simp [h,Verse.load] at h'
    have hv : Templary M₀ Set.univ roots P' σ (B₁+B₂):= by
       apply Templary.skim (Lobby.sumAnch (Lobby.peel A K) (signed F) P' Set.univ Set.univ (Lobby.templarySign F P' Set.univ hF) (templaryPeel A P' K hA (fun i _=>i.prop))) ?_ le_rfl le_rfl
       intro i _; cases i<;> simp [Lobby.switch]
    have hdκ:= Lobby.standing' P' a Z z' _ X' hd.marks.templary hx.exponent hZ
    obtain ⟨hh,hR⟩:= Vesuvius.plastic P' roots p a Z z' _ (hair c δ) hd.price hx.exponent hZ X'
    have hs:= Lobby.onceP M₀ P' z a Z z' T.chosen T.seats X (surge Q T.aCut T.poses) X' T.marker hf (songs Q T.bCut) (sun o' Wc wP) (hair c δ) hd.price hx.exponent hp hU.occupation.vacuum hZ (Lobby.standing' P' a Z z' M₀ X' hv hσ hZ) hdκ
    let U₁:= (Re).paint P' Z z' a X'; have hA:= Lobby.standing' P' a Z z' Re X' hx.core hσ hZ; have hρ: Summable fun i=> U₁ (.inr i):=hA.comp_injective Sum.inr_injective
    have ht : (∑' i,U₁ i)= (∑' i,(Mʼ).paint P' Z z' a X' i)+ ((∑' i, (Kʼ).paint P' Z z' a X' i)+(M₀).basin P' (Cargo.wall Q A F K roots C' S' T)ᶜ Z z' a X'):=by
        rw [Summable.tsum_sum (f:=U₁) (hA.comp_injective Sum.inl_injective) hρ]
        apply congr_arg; exact Summable.tsum_sum (f:=fun i=>U₁ (.inr i)) hdκ (hρ.comp_injective Sum.inr_injective)
    rw [hs,show (∑' i,(Re).paint P' Z z' a X' i)=_ from ht,← hh.tsum_eq]; simp only [add_assoc]; rfl
omit hA hF hσ hU
lemma reading(hg: Manor.Templary (mural A F K) ((Slᶜ)∩ night M₀ Z) roots P' σ dA)(h:Manor.Spinal M₀ (Slᶜ) roots P' σ vF) :
    Manor.Templary Re (Lobby.night Re Z) roots P' σ (dC+dA)∧ Manor.Spinal Re ((Lobby.night Re Z)ᶜ) roots P' σ (b+vF):=by
    -- Kʼ no silent entries, Mʼ all night
    have hx (i): (Mʼ).marks i=0:= rfl
    have hv (i): i∉ Lobby.night Kʼ Z:= fun h=> Nat.ne_of_gt (hd.situated i) h
    have hh: Manor.Templary Kʼ (∅) roots P' σ 0:= ⟨fun _=>0,fun _=>le_rfl,fun _ h=> (by simp at h),fun i=> by simp only [zero_mul,ite_self]; exact budget_of_sum (fun _=>le_rfl) (fun _=>by simp)
       ⟩
    have he: Manor.Spinal Mʼ ∅ roots P' σ 0:=⟨fun _=>0,fun _=>le_rfl,fun _ h=> (by simp at h),fun i=> by simp only [zero_mul,ite_self]; exact budget_of_sum (fun _=>le_rfl) (fun _=>by simp)⟩
    let U:Set (↑(Slᶜ)):= {i| i.val∈night M₀ Z}
    have hp:= Lobby.sumAnch Mʼ (unison Kʼ (Lobby.peel M₀ (Slᶜ))) P' Set.univ (switch ∅ U) (Lobby.sumAnch Kʼ (Lobby.peel M₀ (Slᶜ)) P' ∅ U (Lobby.templaryPeel M₀ P' (Slᶜ) hg (fun i hi=> ⟨i.prop,hi⟩)) hh) hd.initials
    have hV:= Lobby.sumPays Mʼ (unison Kʼ (Lobby.peel M₀ (Slᶜ))) P' ∅ (switch Set.univ Uᶜ) (Lobby.sumPays Kʼ (Lobby.peel M₀ (Slᶜ)) P' Set.univ Uᶜ (Lobby.peeled M₀ P' (Slᶜ) h (fun i _=>i.prop)) (hd.marks.skim (Set.Subset.refl _) le_rfl (show σ≤σ+1 from le_add_of_nonneg_right zero_le_one))) he
    constructor
    · refine hp.skim ?_ (by simp) le_rfl; rintro (i|i|i) h
      · exact Set.mem_univ i
      · exact (hv i h).elim
      exact (show i ∈ U from h)
    refine hV.skim ?_ (by simp) le_rfl; rintro (i|i|i) hX
    · exact (hX (show i ∈ Lobby.night Mʼ Z from by unfold night; simp [hx,Verse.load])).elim
    · exact Set.mem_univ i
    exact (show i∈ Uᶜ from hX)
end Cargo
end YM.RemainderComparison.Funk
