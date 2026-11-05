import YM.RemainderComparison.Muse.Baton

/-!
# Terse invoice on the exact utterances
Distinct OriginS sets (indexed by Sigma). Send to Assembly *before* CU transformations. All mark & nature terms canonical and non-canonical.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Muse
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type}
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(H:Cash W x μ L Q o C T R) {q A B b e u v d L' Gp:ℝ}{j n k s J:ℕ}(χ:Chi)
open Lyric Mosaic
variable (N:Captain H j q d v u A b r B e n χ)
local notation "sx"=> radiusB x
variable (Z:Set ι)(l:ι→ℝ) (δ:ℝ)
open Mixed
open Cascade Halo Height Opacity
local notation "LT"=> sits Z l δ
open Sleet Next.Foundations

-- Geometric costs from actual P are applied after supply from several Captains, converted to P.order etc once per Pad. Use Sticker industry independent.
local notation "E₀"=> etude M H χ
variable (P':BudgetPoint)
structure Seal (z : Staff M H) (f : Config G c→ℝ) (p:ℝ) : Prop where
   nneg : 0 ≤ p
   bound : P'.Regular (Base M H z) f ∧ ∀ x∈Base M H z,P'.supBounds x (Base M H z) f p
structure Network (V:Set (Staff M H))(Y:Staff M H→ℝ)(a b:ℝ) : Prop where
   mark z : z ∈ V → Seal M H P' z ((E₀ z.fst z.snd).emit l) (Y z)
   costs : Ac.Hit (Base M H) P'.B (fun z=> if z∈V then Y z else 0) a b

-- Convenient lift into previous RU call as needed
lemma seals {V:Set (Staff M H)}(Y:Staff M H→ℝ) (h: Network M H χ l P' V Y a b):Sleet.Rendition M H χ l P' V a b:=by
    refine ⟨fun z=> if z∈V then Y z else 0, fun z=>?_,fun z hz=> if_neg hz,fun z hz=> ?_, h.costs⟩
    · dsimp only; split; exact (h.mark _ ‹_›).nneg; exact le_rfl
    obtain ⟨p,hp⟩:=z; dsimp only; rw [if_pos hz]; have hh: Sleet.charge M H χ l ⟨p,hp⟩=(E₀ p hp).emit l:=by ext V; unfold Sleet.charge Verse.emit; rw [Mosaic.pieces]; rfl
    rw [hh]; exact (h.mark _ hz).bound
lemma advance {V U:Set (Staff M H)}(Y:Staff M H→ℝ) (h: Network M H χ l P' V Y a b)(he:U⊆V){b':ℝ}(hp:b≤ b') : Network M H χ l P' U Y a b':=by
    refine ⟨fun z hz=>h.mark _ (he hz),fun p=>budget_loosen (budget_mono (h.costs p) ?_ ?_) hp⟩
    · intro i; dsimp only; split; next=> apply mul_nonneg ?_ (Real.exp_pos _).le; split; exact (h.mark i (he ‹_›)).nneg; exact le_rfl
      next=>exact le_rfl
    intro i; by_cases hp':i∈U
    · dsimp only; simp only [if_pos hp',if_pos (he hp')]; exact le_rfl
    dsimp only; rw [if_neg hp',zero_mul,ite_self]; exact (h.costs p).1 i
variable (hx:P'.B=radiusB x)(ht:P'.threshold=Pressure.temp x)(hn:P'.order≤j)(hk:P'.power≤J)
include hx ht hn hk
variable (f':H.ThinP→Drums M S→ℝ)(hl:Lyric.Paid M H χ N f')

def toll (j J:ℕ)(z:Staff M H):ℝ:= Lyric.Bill M H f' z.1 l j z.2 J

variable [Fintype ι]
include hl
lemma reunion (V:Set (Staff M H))(p : (z:H.fragrances)→Syllable M H z→Prop){b₁:ℝ}[∀ i j,Decidable (p i j)](he:∀ i, i ∈ V → p i.1 i.2)
    (hp:Ac.Hit (Captain.reachability (H:=H)) sx (fun z=>∑ i:Syllable M H z, if p z i then Lyric.Bill M H f' z l j i J else 0) a b₁)
    (he':∀ i,0 ≤ l i): Network M H χ l P' V (toll M H l f' j J) a b₁:=by
   let f:=toll M H l f' j J
   have hz (z): 0 ≤ f z:= mul_nonneg (prod_nonneg fun i _=>prod_nonneg fun i _=>he' _) (Lyric.dividend_nonneg M H χ hl z.1 z.2)
   let b i:= if i∈V then f i else 0
   refine ⟨fun z hi=> ⟨hz _,?_⟩,fun x₀=>?_⟩
   · obtain ⟨i,w⟩:=z
     let c':=(E₀ i w).stock l; let M':=c' • (ContinuousLinearMap.id ℝ ℝ)
     have he:(E₀ i w).emit l=M' ∘ Lyric.string M H χ i w:=rfl
     obtain ⟨hg,hv⟩:=Lyric.direction M H χ hl i w P' ht hn J hk
     rw [he]; refine ⟨regular_mapped M' hg,fun y hy=>⟨hz _, fun x hx t hpL hh=>?_⟩⟩
     rw [Push.Local.left_linear M' t (f:=Lyric.string M H χ i w) (hg.smooth _ hx) hpL]; change ‖c'*_‖≤ _; unfold c'; rw [pieces M H χ, norm_mul, Real.norm_of_nonneg (show 0 ≤ invests M H i w l from prod_nonneg fun i _=>prod_nonneg fun i _=>he' _)]
     exact mul_le_mul_of_nonneg_left ((hv _ hy).2 _ hx t hpL hh) (prod_nonneg fun i _=>prod_nonneg fun i _=>he' _)
   apply Sleet.budget_sigma; swap
   · intro i; dsimp only; split; next=> apply mul_nonneg ?_ (Real.exp_pos _).le; split; exact hz _; exact le_rfl
     next=>exact le_rfl
   refine budget_mono (hp x₀) (fun i=>?_) (fun i=>?_)
   · apply sum_nonneg; intro k _; dsimp only; split; next=> apply mul_nonneg ?_ (Real.exp_pos _).le; split; exact hz _; exact le_rfl
     next=>exact le_rfl
   by_cases h : x₀∈reachability (H:=H) i
   swap; · dsimp only; rw [if_neg h,sum_eq_zero (fun j _=>if_neg (show ¬x₀∈ Base M H ⟨i,j⟩ from h))]
   dsimp only; rw [if_pos h,hx, Finset.sum_mul]; apply sum_le_sum; intro k _
   rw [if_pos (show x₀∈Base M H ⟨i,k⟩ from h)]; split; next hn=> rw [if_pos (show p i k from he ⟨i,k⟩ hn)]; exact le_rfl
   rw [zero_mul]; split; exact mul_nonneg (hz ⟨i,k⟩) (Real.exp_pos _).le; rw [zero_mul]

omit hx ht hn hk hl

omit [Fintype ι] in
lemma enclosure {U:Set (Staff M H)} (Y:Staff M H→ℝ)(h:Network M H χ l P' U Y a b)(hp:∀ i:Staff M H,i∈U→virgin M H χ Z i.1 i.2):Network M H χ (sits Z l δ) P' U Y a b:=by
   refine ⟨fun z hz=>?_,h.costs⟩
   have he: (E₀ z.fst z.snd).emit LT=(E₀ z.1 z.2).emit l:=by
      funext u; unfold sits; rw [Verse.excursion,show Verse.load Zᶜ (E₀ z.fst z.snd).letters = 0 from hp z hz,pow_zero,one_mul] -- edit
   rw [he]; exact h.mark z hz
end YM.RemainderComparison.Muse
