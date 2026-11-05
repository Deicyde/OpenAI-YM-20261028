import YM.RemainderComparison.Solo.Barque
import YM.RemainderComparison.Sleet.Forest
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Sleet
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling Raw Itinerary Opacity Cascade Lyric Daisy Halo Height
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type} [Fintype ι]
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(H:Cash W x μ L Q o C T R) {q A B b e u v d L' Gp:ℝ}{j n k s J:ℕ}(χ:Chi)
variable (N: Captain H j q d v u A b r B e n χ) (Ξ:Utopia H j v d r q χ)
variable (l:ι→ℝ) {T' S' δ B' b' τ ε:ℝ}
local notation "V'" => Q.costs L μ R.beta x q
local notation "LT" => Mixed.lengths S V' (ConnectedActivityE6.lengths T R)
local notation "Z" => radiusB x




-- Four bookings: seed/w^ powers, heavy gusts and exceptional letters,
-- measured/registered kernels long, rough next-step rails. Prior-to-mask
-- alignment components. Same exact alphabet/log for all those bookings.

def Rode (z:Staff M H)(k s:ℕ)(E:Set ℕ)(Y:ℕ):Prop :=
    ((tumble H z.1 ∨ Flurry H z.1 k s) ∨ muddy R Y M (page M H z.1 z.2)) ∨ Halo.dyed M H (ridge R Y E) z.1 z.2
omit [Fintype ι] in
lemma road (z:Staff M H) {V:Config G c}{E:Set ℕ}{Y:ℕ}(he : Lyric.string M H χ z.1 z.2 V≠0)(hz : ¬Rode M H z k s E Y)(hE: ¬ Halo.dyed M H E z.1 z.2): Nordic M H z.1 z.2 E k s Y:=
   season M H χ z.1 z.2 E he (fun h=> hz (Or.inl (Or.inr h))) (fun h=>hz (Or.inl (Or.inl (Or.inr h)))) (fun h=>hz (Or.inl (Or.inl (Or.inl h)))) (fun h=>hz (Or.inr h)) hE

include H in
private lemma bandH : inBand (betaF G x L) R.beta:=by
    have hh:= H.laws.data.funds.length_eq
    have hX:1 < betaF G x L := hh ▸ H.laws.intake.height
    obtain ⟨ha,hb⟩:=H.laws.intake.window; rw [hh] at ha hb; exact ⟨by linarith only [ha,hX],by linarith only [hb,hX]⟩

-- F' view before mask. Width/pigment consumption needs no actual long proof disguised as formal tails.

-- keep record including plots manager for Photo exports; supplies Spotlight externally
structure Bristling (Q:ConnectedActivityE6.Target G P)(L:Side)(D:Patch)(W μ:ℝ)(o: ConnectedActivityE6.Target.Order G W)
    (χ:Chi)(j J I k:ℕ)(x α ε Δ M' C σE:ℝ)(η:ℕ) : Prop where
   grants (c f:Side)(S:StepData c f) (T':Tube G S) : S.patch=D→Stamp T'→∀ (R:Rep G f) (C':ℝ)(H:Cash W x μ L Q o C' T' R),
      ∃ (q d v t A a r B b:ℝ) (n:ℕ)(N: Captain H j q d v t A a r B b n χ), Heroes H N.conduit A B n ∧ Heavy N.conduit ∧ Premium Q L x α μ ε B j n I k J η M' ∧
         ∀ (V:BudgetPoint), V.B=radiusB x→V.threshold=Pressure.temp x→V.order≤j→V.power≤J→ ∀ (ι P':Type) [Fintype ι][Fintype P'] (M:ι→Leaf R)(X:P'→ Site f)(p:ι→ Finset P')(l:ι→ℝ)(σ:ℝ), Lyric.Scale X p M l η σ M' S → radiusCost Q L σ→
           Sleet.Rendition M H χ l V {z|kept M H I z} α C ∧
           ∀ (E:Set ℕ)(w:ℕ→ℝ) (Y:ℕ), Cost R E Y x Δ σE w→ Lyric.Scale X p M (pigmentY R Y M x Δ l) η σ M' S →
             Sleet.Rendition M H χ l V {z|kept M H I z ∧ Rode M H z I k E Y} α (4* (gStep R.beta)^k)

abbrev demand (k:ℕ) (Q:ConnectedActivityE6.Target G P):Cascade.Lower Q:= fun {_ _ _ _ _ _ _ _ _ _ _} H {_ _ _ _ _ _} Ξ=> Massive (H:=H) k Ξ

set_option maxHeartbeats 800000 in
lemma table (Q:ConnectedActivityE6.Target G P)(hQ:3/8+Q.rate<0) :∃ ℓ:ℕ, ∀ (L:Side), ℓ≤L.val → ∀ (D:Patch), D.Branches P.bind G → ∀ (W μ:ℝ)(o:ConnectedActivityE6.Target.Order G W), 0<W→0<μ→ ∀ (χ:Chi)(j J I k:ℕ)(a ε Δ:ℝ),0≤a→0<ε→a+2*ε≤ Q.exp→0<Δ→∀ (Y:ℝ→ℝ)(n:ℝ→ℕ)(f:ℝ→ℝ)(t:ℝ), Reserve G L Y→ Reserve G L (fun x=>(n x:ℝ))→ Rate G L t f→∃ C, Reserve G L C∧ ∀ᶠ x in atTop,
    Bristling Q L D W μ o χ j J I k x a ε Δ (Y x) (C x) (f x) (n x) :=by
   obtain ⟨ℓ,hℓ⟩:= Utopia.crinkles P Q; obtain ⟨L,hL⟩:= Halo.gallery P Q; obtain ⟨m,hM⟩:= Halo.ramp P Q
   refine ⟨ℓ+L+m, fun f hz D hd W μ o hW hμ χ j J I k a ε Δ ha he haε hΔ Y n F t hY hn hF=>?_⟩
   let b:=region I k
   obtain ⟨A,c',C,d,v,t',r,B,q,l,hC,hB,hP⟩:= triumphedFor P Q (demand b Q) ℓ (fun L hL D hd j=> hℓ L hL D hd b j) f (by omega) D hd j χ W hW μ hμ o
   obtain ⟨V,hV,hG⟩:= hL f (by omega) D hd j ε a ha he (by linarith only [haε]) χ W hW μ hμ o I J Y n hY hn
   obtain ⟨A',a',B',C',d₀,v₀,t₀,r₀,F₀,B₀,T₀,K₀,k₀,hF₀,hT₀,hv₀,h⟩:= hM f (by omega) D hd j ε a ha he (by linarith only [haε]) χ W hW μ hμ o
   obtain ⟨G',S',δ,hδ,hG',hS',hL''⟩:= h I J Y n hY hn
   refine ⟨V,hV,?_⟩
   filter_upwards [hP,hG,hL'',narrowK Q f b, Lyric.epochs Q f hQ ha he (by linarith only [haε]:a+ε+ε≤ _) hμ j l I k J hB hY.rate hn.rate, gustLine Δ hΔ hF k, gustLine Δ hΔ (hF.mul hG'.rate) k,gustLine Δ hΔ hV.rate k] with x hh h hX hx hS hw hP hV
   constructor; intro c f' S T hD hT R C'' H; have hg:=bandH H
   obtain ⟨N,hΞ,hΦ⟩:= hh c f' S T hD hT R C'' H
   obtain ⟨q₁,d₁,v₁,t₁,A₁,a₁,r₁,B₁,e₁,k₁,Q',hB⟩:= h c f' S T hD hT R C'' H
   obtain ⟨J',hy,hΘ,hk⟩:= hX c f' S T hD hT R C'' H
   refine ⟨_,_,_,_,_,_,_,_,_,_,N,hΦ,Sleet.narrow H χ _ hΞ hS.roll,hS,?_⟩
   intro P'' hβ hR hJ hi ι P' _ _ M X p τ σ hv hR0
   have ht z:0 ≤ τ z:= hv.currency z
   obtain ⟨X',hA,hG⟩:= hB _ M
   have hf:= hG P' X p τ σ hv hR0
   constructor
   · exact reunion M H χ Q' τ P'' hβ hR hJ hi X' hA ht _ (fun z i=> Lyric.notes M H z i ≤ I) (fun _ h=>h) hf
   intro E w Y' hS' hm
   let z:=gStep R.beta^k
   have ht' := Lyric.rocketing M H χ N hΦ
   let a (p:Staff M H):Prop := tumble H p.1 ∧ kept M H I p; let b' (p:Staff M H):Prop:=Flurry H p.1 I k∧ kept M H I p; let c₁ (p:Staff M H):Prop:= kept M H I p∧ muddy R Y' M (page M H p.1 p.2)
   let d' (p:Staff M H):Prop:=Halo.dyed M H (ridge R Y' E) p.1 p.2∧ kept M H I p
   have hp₁:= reunion M H χ N τ P'' hβ hR hJ hi _ ht' ht {p|a p} (fun z i=> Sleet.tumble H z ∧ notes M H z i≤ I) (fun _ h=>h) (Sleet.tempest M H χ N τ hv hR0 hS hΞ hΦ)
   have hp₂:= reunion M H χ N τ P'' hβ hR hJ hi _ ht' ht {p|b' p} (fun z i=> Flurry H z I k ∧ notes M H z i≤ I) (fun _ h=>h) (Sleet.snow M H χ N τ hv hR0 hS hx hΦ hΞ)
   have hp₃:= Rendition.weaken M H χ τ _ (reunion M H χ Q' τ P'' hβ hR hJ hi _ hA ht {p|c₁ p} (fun z i=> notes M H z i≤ I ∧ muddy R Y' M (page M H z i)) (fun _ h=>h) (Sleet.color M H χ Q' τ hA hΔ ht (hG P' X p _ σ hm hR0))) ((le_abs_self _).trans (hV.2 R.beta hg)) (Set.Subset.refl _) le_rfl
   let ℓ:=pigment Δ x *F x; let ff:= ridge R Y' E; have ht:ℓ ≤ incomingE G f x:= (le_abs_self _).trans hw.1
   obtain ⟨hA',hP'⟩:= hk ι P' M X p τ σ ff w ℓ hv hR0 (sails E w hS') ht
   have hp₄:= Rendition.weaken M H χ τ _ (reunion M H χ J' τ P'' hβ hR hJ hi _ hA' (fun i=> hv.currency i) {p| d' p} (fun z i=> (Halo.dyed M H ff z i∧ 1+0≤ Halo.gross M H z i) ∧ Lyric.notes M H z i ≤ I) (fun i h=>by
     change (Halo.dyed M H ff i.1 i.2∧ 1+0≤ Halo.gross M H i.1 i.2) ∧ kept M H I i
     change _ ∧ kept M H I i at h; refine ⟨⟨h.1,?_⟩,h.2⟩
     obtain ⟨hh,hp⟩:=h; obtain ⟨j,k,-,h⟩:= hh;  exact (Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨_,h⟩)).trans (Finset.single_le_sum (f:=fun j=>((i.fst.snd j).val\ Tickets.reach (i.snd j)).card) (fun _ _=>Nat.zero_le _) (mem_univ j))) (hP' 0)) (show G' x*S' x ^ 0 * ℓ ≤ z from ?_) (Set.Subset.refl _) le_rfl
   swap; · unfold ℓ; rw [pow_zero,mul_one,mul_comm,mul_assoc]; exact (le_abs_self _).trans (hP.2 R.beta hg)
   apply Rendition.weaken _ _ _ _ _ (Rendition.plus M H χ τ _ (Rendition.plus M H χ τ _ (Rendition.plus M H χ τ _ hp₁ hp₂) hp₃) hp₄) (by apply le_of_eq; unfold z; ring) ?_ le_rfl
   intro z ⟨hz,h⟩; rcases h with ((h|h)|h)|h
   · exact Or.inl (Or.inl (Or.inl ⟨h,hz⟩))
   · exact Or.inl (Or.inl (Or.inr ⟨h,hz⟩))
   · exact Or.inl (Or.inr ⟨hz,h⟩)
   exact Or.inr ⟨h,hz⟩
end YM.RemainderComparison.Sleet
