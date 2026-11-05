import YM.RemainderComparison.Script.Glyphs

/-!
# Natural books of tickets over cuts
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Script
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι α : Type}
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(H:Cash W x μ L Q o C T R) {q A B b e u v d L' Gp:ℝ}{j n k s J:ℕ}(χ:Chi)
open Lyric Mosaic Muse
variable (σ:α ↪ ι)
local notation "M'" => M ∘ σ
local notation "V'"=> drums M σ S
local notation "w'"=> label M H σ

variable (l:ι→ℝ)(p:H.Chainbook)(w:Scene (M ∘ σ) H p) (s:H.fragrances)(i:Syllable (M ∘ σ) H s)
local notation "Z₀"=> board M H σ
local notation "Z₁"=> queue M H σ
local notation "λ₀"=> l ∘ σ
local notation "bQ"=> Muse.toll M H
open Sleet

lemma tip (n:ℕ)(p:Molecule S)(z:Drums M' S): Mosaic.bite M H l n p (V' z)= Mosaic.bite M' H (l ∘ σ) n p z:=by
   unfold Mosaic.bite; rw [travels]
   split; next he=> rw [show (V' z).val=z.val.map σ from rfl,prod_map]; rfl
   next=>rfl
lemma tender : Mosaic.kronor M H l s ((w' s) i)=Mosaic.kronor M' H (l ∘ σ) s i:= by
   unfold kronor; exact congr_arg (‖cadence H s‖*·) (prod_congr rfl fun j _=>tip M H σ l _ _ (i j))
lemma mint (j:H.Chapter)(z: Mosaic.Stone M' H j): Mosaic.pay M H l j (Z₀ j z)=Mosaic.pay M' H (l ∘ σ) j z:=by
   rcases j with j|j
   · exact tip M H σ l _ _ z
   exact tender M H σ l j z
lemma fisc : Mosaic.Bank M H l p (Z₁ p w)= Mosaic.Bank M' H (l ∘ σ) p w:=by
   unfold Bank; split; next h=> exact prod_congr rfl fun i _=> congr_arg (·/_) (prod_congr rfl fun j _=>mint M H σ l _ (w i j))
   next=> rfl

lemma copay : invests M H s ((w' s) i) l=invests M' H s i λ₀:=by
   unfold invests; apply prod_congr rfl; intro j _; rw [show ((w' s) i j).val=(i j).val.map σ from rfl,prod_map]; rfl
variable {h:Pad H j χ}
lemma title {g:H.ThinP→Drums M S→ℝ}{g':H.ThinP→Drums M' S→ℝ} (he: ∀ p i, g p (V' i)=g' p i)(j s':ℕ):
     Muse.toll M H l g j s' ⟨s,w' s i⟩ = Muse.toll M' H (l ∘ σ) g' j s' ⟨s,i⟩:=by
   unfold Muse.toll Lyric.Bill Lyric.dividend Lyric.adjectives; rw [copay]; dsimp only
   refine congr_arg (_ * ·) (congr_arg (_ * ·) (congr_arg (_* ·) (Finset.prod_congr rfl fun j _=> ?_)))
   exact congr_arg (_ * ·) (he _ (i j))
lemma article (N:Brake H j χ)(p:H.ThinP)(i: Drums M' S)(E:Set ℕ)(w:ℕ→ℝ): Muse.song M H χ N E w p (V' i) = Muse.song M' H χ N E w p i:= by unfold Muse.song Halo.melod; rw [travels,wage]
lemma signL (N: Pad H j χ)(p:H.ThinP)(i: Drums M' S): floats M H χ N.S.N p (V' i)= floats M' H χ N.S.N p i:=by unfold Lyric.floats; rw [travels,wage]
variable (Z:Set ι) (k:ℕ)
lemma story : Muse.arity M H χ Z s (w' s i) = Muse.arity M' H χ (σ ⁻¹' Z) s i:= by unfold Muse.arity clinic; rw [resume]; exact sun σ Z _
lemma grip : Muse.virgin M H χ Z s (w' s i) ↔ Muse.virgin M' H χ (σ ⁻¹' Z) s i:= by
   change Muse.arity M H χ Zᶜ s _=0↔ _; rw [story]; rfl
lemma capZ : Muse.Pure M H χ Z k ⟨s,w' s i⟩ ↔ Muse.Pure M' H χ (σ ⁻¹' Z) k ⟨s,i⟩ := by unfold Muse.Pure; simp only [grip,story]
lemma capL : Muse.impure M H χ Z k ⟨s,w' s i⟩ ↔ Muse.impure M' H χ (σ ⁻¹' Z) k ⟨s,i⟩:=by unfold Muse.impure; simp only [grip,story]
lemma capK : Muse.within M H χ Z k ⟨p,Z₁ p w⟩ ↔ Muse.within M' H χ (σ ⁻¹' Z) k ⟨p,w⟩:= by
   unfold Muse.within; rw [Script.parade,Script.write];dsimp only; rw [sun]
lemma wages (δ:ℝ): Muse.pitch M H χ Z l δ ⟨p,Z₁ p w⟩ = Muse.pitch M' H χ (σ ⁻¹' Z) (l ∘ σ) δ ⟨p,w⟩:=by
   unfold Muse.pitch; rw [Script.parade,Script.write,fisc]; dsimp only;rw [sun,Script.earns]
lemma erased (E:Set ℕ) : Halo.dyed M H E s (w' s i)↔ Halo.dyed M' H E s i:=by unfold Halo.dyed; simp_rw [show ∀ t,(w' s i) t=V' (i t) from fun _=>rfl,travels]
lemma attrition (E:Set ℕ)(k:ℕ): Muse.Elder M H E k ⟨s,w' s i⟩ ↔ Muse.Elder M' H E k ⟨s,i⟩:=by
   unfold Muse.Elder; rw [erased]; unfold Halo.gross; dsimp only; simp_rw [show ∀ t,(w' s i) t=V' (i t) from fun _=>rfl,travels]
lemma plant (b:ℕ) : Sleet.muddy R b M (page M H s (w' s i)) ↔ Sleet.muddy R b M' (page M' H s i):=by
   constructor
   · rintro ⟨j,h,hG⟩; obtain ⟨p,hp,hv⟩:= mem_biUnion.mp h
     obtain ⟨j,hj,rfl⟩:= mem_map.mp (show j∈ (i p).val.map σ from hv); exact ⟨j,mem_biUnion.mpr ⟨p,hp,hj⟩,hG⟩
   rintro ⟨k,hk,hG⟩; obtain ⟨p,hp,hv⟩:=mem_biUnion.mp hk; exact ⟨σ k, mem_biUnion.mpr ⟨p,hp,show σ k∈(i p).val.map σ from mem_map_of_mem σ hv⟩,hG⟩
end YM.RemainderComparison.Script
