import YM.RemainderComparison.Serif.Wallet

/-!
# Packed books; coda before reclosure ledger
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Serif
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
variable (M:ι→Lotus.Leaf R)(H:Cash W x μ L Q o C T R) {q A B b e u v d L' Gp:ℝ}{j n k s J I:ℕ}(χ:Chi)
open Lyric Mosaic Muse Sleet
variable (Z:Set ι)(l:ι→ℝ) (δ:ℝ)
open Verse Marker Script
variable {β:Type} [DecidableEq β]{Jm:Census β}
variable (U:Pad H j χ)
local notation "F'"=> U.S.N
local notation "L₁"=> Muse.song M H χ U.V (∅:Set ℕ) 0
local notation "P₀"=> tax G L x
local notation "Lt"=> sits Z l δ
variable {τ κ K Y γ V T0:ℝ}
variable (h:Roles H χ U k s J I a d e K σ Y γ V T0) (hh:Motto M l δ H τ K Y I)
include h hh
variable (z:ι→Poly Jm) {fP:β→ℝ} (hZ : Chorus Jm fP Z z k)
local notation "E'"=> jewel M H χ
include hZ
open Ovens Mallow Progress.DirectedRecipe
variable (Sx : BudgetPoint) (hx:Sx.B=radiusB x)(hv:Sx.threshold=Pressure.temp x)(ht:Sx.order≤j)(hJ:Sx.power≤J)

omit h hZ hh
lemma shrine {A:Set (Staff M H)}{V':Staff M H → ℝ} (hi:Network M H χ l Sx A V' a b)(hv:Sx.threshold=Pressure.temp x)(i:Staff M H) (p:i ∈ A)(U:Config G c): ‖(jewel M H χ i.1 i.2).emit l U‖≤ V' i:=by
    let f:=(E' i.1 i.2); let a:= Sleet.Base M H i
    have hp:= (hi.mark i p).bound
    by_cases he:Healthy (Pressure.temp x) a U
    · rw [emit,show (jewel M H χ i.1 i.2).utter U= string M H χ i.1 i.2 U from masked_eq _ a (Lyric.string M H χ i.1 i.2) U he];
      have hn : a.Nonempty:=Refrain.chapter_ne H (Sum.inr i.1) -- check
      obtain ⟨x,hx⟩:=hn; exact (hp.2 _ hx).2 U (hv.symm ▸ he) [] (Nat.zero_le _) (by simp)
    change ‖f.emit _ _‖ ≤ _; unfold Verse.emit f; rw [show (E' _ _).utter U=0 from masked_ne _ a _ _ he,mul_zero,norm_zero]; exact (hi.mark i p).nneg
lemma educt (X:Staff M H): (Sleet.Base M H X).Nonempty := Refrain.chapter_ne H (Sum.inr X.1)
include h hZ hh
lemma input_pay : Dominated (fun i:Drums M S=> (raw M i).paint Z Lt z) :=by
   have hp:δ≤ 1:= (le_mul_of_one_le_left hh.positive h.allowed).trans hh.emit
   have ht:= Serif.league M H l δ hh; obtain ⟨X,hX,sx,t',hl⟩:= hh.claim
   have he (i) :0 ≤ sits Z l δ i:= mul_nonneg (show 0 ≤ Verse.marked Zᶜ δ i from (by unfold Verse.marked; split; exact hh.positive; exact zero_le_one)) (hl.currency i)
   apply dominion M H Z _ z hZ _ he
   exact ht.of_nonneg_of_le (fun i=> mul_nonneg (he i) (Leaf.profit _) ) fun i=> mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (hl.currency _) (show Verse.marked Zᶜ δ i ≤ 1 from by unfold Verse.marked; split; exact hp; exact le_rfl)) (Leaf.profit _)

open Daisy

-- Visibility from *fixed* Book: test owner willing to pay from envelope === genuine Poly
include hx hv ht hJ
lemma rollbook : ∃ c':Staff M H→ℝ, Summable c' ∧ ∀ i:Staff M H,∀ V:Config G c, Poly.price fP ((E' i.fst i.snd).paint Z Lt z V) ≤ c' i := by
   obtain ⟨_,_,hc,hT⟩:= honored M H χ Z l δ U h hh Sx hx hv ht hJ
   have hq {V':Set (Staff M H)}{b t}(hh:Network M H χ Lt Sx V' t a b): let s (p:Staff M H):= if p∈V' then t p else 0; Summable s ∧ (∀ p,0 ≤ s p)∧ ∀ i∈V',∀ Y, Poly.price fP ((E' i.fst i.snd).paint Z Lt z Y) ≤ s i:=by
      intro s; have ht i: 0≤ s i:=by unfold s; split; exact (hh.mark _ ‹_›).nneg; exact le_rfl
      refine ⟨Daisy.Charity.everyoneN _ _ ht (hx ▸ hh.costs) (fun i _=> educt M H i) h.price.visit.posts,ht, fun i hp V=> (Serif.housing hZ _ _ _).trans ((shrine M H χ _ Sx hh hv i hp V).trans_eq (show t i=s i from (if_pos hp).symm))⟩
   obtain ⟨hu,h'H,hH⟩:=hq hc; obtain ⟨hx,hk,hP⟩:= hq hT
   let b i:= if Muse.Pure M H χ Z k i then Muse.toll M H l (Muse.song M H χ U.V ∅ 0) j J i else 0
   let b' i:= if Muse.impure M H χ Z k i then Muse.toll M H Lt L₁ j J i else 0
   refine ⟨fun i=>b i+b' i,hu.add hx,fun i V=>?_⟩
   by_cases hp:arity M H χ Z i.1 i.2≤ k
   · by_cases he: Muse.Pure M H χ Z k i
     · exact (hH i he V).trans (le_add_of_nonneg_right (hk i))
     exact (hP i (show impure M H χ Z k i from ⟨fun h=>he ⟨h,hp⟩,hp⟩) V).trans (le_add_of_nonneg_left (h'H i))
   rw [paint, hZ.capacity (E' _ _).letters (lt_of_not_ge hp), smul_zero, Poly.zero_price]; exact add_nonneg (h'H _) (hk _)

abbrev KEntry (i:Refrain.Leaf H) := Mosaic.Scene M H i.val
omit hx hv ht hJ
lemma rollK : ∃ c': (Σ i:Refrain.Leaf H,KEntry M H i) → ℝ,Summable c' ∧ ∀ i t Y, Poly.price fP ((Mosaic.parade M H χ i.val t).paint Z Lt z Y)≤ c' ⟨i,t⟩:=by
    let p'(i:Flak M H):= if Muse.within M H χ Z k i then Muse.pitch M H χ Z l δ i else 0
    have hv (i:Flak M H):0≤p' i:=by unfold p'; split; exact (norm_nonneg _).trans (winter M H χ Z l δ U h hh i 1); exact le_rfl
    have hd : ∀ i:Refrain.Leaf H,(H.library i.val).Nonempty:=by
       intro i; obtain ⟨j,hj⟩:=i.prop -- inventory subset
       obtain ⟨x,hx,hm⟩:=mem_biUnion.mp hj; -- x is Thick. chapterFoot.nonempty
       exact Finset.Nonempty.mono (subset_biUnion_of_mem H.bookFoot (mem_toLeft.mp hx)) (Refrain.chapter_ne H _)
    let t: (Σ i:Refrain.Leaf H,KEntry M H i) ↪ Flak M H:= Embedding.sigmaMap (Embedding.subtype _) (fun i=> Embedding.refl (KEntry M H i))
    let u(i):=p' (t i); have hp: Ac.Hit (fun i=> H.library (t i).fst) (radiusB x) u a ((unitK x)^4 * gStep R.beta ^ s) := fun i=> budget_pull t t.injective (Script.forceC M H χ Z l δ U h hh i)
    refine ⟨u,Daisy.Charity.everyoneN _ _ (fun i=>hv _) hp (fun i _=> hd i.1) h.price.visit.posts,fun i z' y=>?_⟩
    let v:=t ⟨i,z'⟩; let V:= Mosaic.parade M H χ v.fst v.snd
    by_cases hh' : Muse.within M H χ Z k v
    · exact (show Poly.price fP (V.paint Z Lt z y)≤ _ from Serif.housing hZ V _ _).trans ( (winter M H χ Z l δ U h hh v y).trans_eq ((if_pos hh').symm))
    change Poly.price fP (V.paint Z Lt z y)≤ p' v; rw [paint, hZ.capacity V.letters (lt_of_not_ge hh'), smul_zero, Poly.zero_price]; exact hv _
end YM.RemainderComparison.Serif
