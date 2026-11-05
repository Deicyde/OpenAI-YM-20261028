import YM.RemainderComparison.Halo.Nexus
import YM.RemainderComparison.Halo.Must
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Halo
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling Raw Itinerary Opacity Graft Cascade Lyric Daisy
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type} [Fintype ι]
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(H:Cash W x μ L Q o C T R) {q A B b e u v d L':ℝ}{j n k s J:ℕ}(χ:Chi)
variable (N: Captain H j q d v u A b r B e n χ) (Ξ:Utopia H j v d r q χ)
variable (l:ι→ℝ) (E:Set ℕ)(w:ℕ→ℝ){T' S' p' δ B' τ ε:ℝ}

-- All marker rough budget p_geo (NOT via (Rate 0)); inherited components may
-- use their actual normalization however. Ward stroke costs still external.
local notation "Z" => radiusB x
local notation "LT" => Mixed.lengths S (Q.costs L μ R.beta x q) (ConnectedActivityE6.lengths T R)
variable (C₁ A₁ X:ℝ)
local notation "rail" => rails H N.conduit (∅:Set ℕ) 0 C₁ A₁
local notation "p₀" => melod M H rail X n
local notation "TOL" => Lyric.mulScale τ⁻¹ l
variable {P':Type} [Fintype P']{X' : P'→ Site f}{Y : ι→ Finset P'}
lemma catkin (h:Quarry H N.conduit A C₁ A₁ X n)(hW:Writ Q L μ x q A₁ C₁ τ δ S' X p' ε m j n)
    (hp:Scale X' Y M l m σ p' S) (ht:radiusCost Q L σ)(hC:0≤C₁)(hA:0≤A₁)(hX:0≤X)(hv:a+ε+ε≤ Q.exp)(ha:0≤a)(hε:0<ε)(J:ℕ) :
     let V:=p₀; Lyric.Paid M H χ N V ∧ Ac.Hit (Captain.reachability (H:=H)) Z (fun z=>∑ i:Syllable M H z, Lyric.Bill M H V z TOL j i J) a
      (collars G ε x j J*(rebate Q X δ j n * (1-1/2)⁻¹)) := by
   intro f; have he := Presents.zeroG R
   have hc (i):0 ≤ rail i:= rails_nonneg H N.conduit ∅ 0 C₁ A₁ he hC hA i
   have hh:= Halo.earns M H χ N rail n X hX hc (fun M p=> h.ready M ∅ 0 _ he zero_le_one p)
   have hp':0<τ:=zero_lt_one.trans_le hW.pace
   have hp:= scaled M l hp (inv_pos.mpr hp').le
   have ht':R.p.B ≤ 2*Z:=by rw [H.laws.intake.sizes,H.laws.data.funds.length_eq]; exact hW.shape
   let p:= gaugeG (S:=S) ∅ τ⁻¹ S'
   have hQ i:1≤p i:= by rw [show p i=S' from if_neg (by rintro ⟨j,hj,_⟩; simp at hj)]; exact hW.income
   have hk: Ready H.supportP Z (tariff (Lyric.combined M (fun i=> p i*rail i) (TOL)) LT 0 Q.ε) (Q.exp+2*Q.ε) δ Q.δ (1/2) :=
      redwood M H N.conduit (TOL) ∅ 0 C₁ A₁ τ⁻¹ S' he (inv_pos.mpr hp').le (zero_le_one.trans hW.income) hC hA hp.currency (show Sales Z Q.relative Q.ε _ (0:ℕ→ℝ) _ (|cost L Q x|) from
        (show Sales Z Q.relative Q.ε _ (0:ℕ→ℝ) (regularExtra R) 0 from ⟨fun _=>le_rfl,fun i=>?_⟩).raise (abs_nonneg _)) (rays M H (TOL) hp ht' ht) hW.beat hW.awake hW.warmth
   swap; · simp [SumBudget,tariff]
   have hv':= boats M H rail p n X TOL hX (prize M _ _ _ hp.currency hc fun i=> zero_le_one.trans (hQ i)) hε hv hk hW.height
   have he' := Lyric.run M H χ f TOL (merit M H p) hh hp.currency (fun p i=>prod_nonneg fun i _=> zero_le_one.trans (hQ i)) ha J hv' (fun _ _=>True) 1 zero_le_one (fun z i _=> by rw [one_mul]; exact one_le_prod fun u _=> show 1 ≤ merit M H p _ _ from one_le_prod fun j _=> hQ j)
   refine ⟨hh,?_⟩; simpa only [↓reduceIte,one_mul] using! he'

lemma charm (h:Quarry H N.conduit A C₁ A₁ X n)(hW:Writ Q L μ x q A₁ C₁ τ δ S' X p' ε m j n)
    (hp:Scale X' Y M l m σ p' S) (ht:radiusCost Q L σ)(hC:0≤C₁)(hA:0≤A₁)(hX:0≤X)(hv:a+ε+ε≤ Q.exp)(ha:0≤a)(hε:0<ε)(J k:ℕ) :
     let V:=p₀; Lyric.Paid M H χ N V ∧ Ac.Hit (Captain.reachability (H:=H)) Z (fun z=>∑ i:Syllable M H z, if Lyric.notes M H z i≤k then Lyric.Bill M H V z l j i J else 0) a
      (τ^k*(collars G ε x j J*(rebate Q X δ j n * (1-1/2)⁻¹))) :=by
   intro P₀; obtain ⟨hz,hR⟩:= catkin M H χ N l C₁ A₁ X h hW hp ht hC hA hX hv ha hε J
   refine ⟨hz,?_⟩; simpa only [true_and] using!
      remits M H χ N l P₀ (fun _ _=>True) (show Ac.Hit _ _ _ a _ from by simpa only [↓reduceIte] using! hR) hp.currency hW.pace hz k

-- Works independent of which E/K decompositions called.
lemma carousel (P:Teller G) (Q:YM.ConnectedActivityE6.Target G P): ∃ l:ℕ,∀ L:Side,l≤L.val → ∀ (D: Patch), D.Branches P.bind G →
    ∀ (j:ℕ) (ε a:ℝ),0≤a→0<ε→a+ε+ε≤ Q.exp→∀ χ (W:ℝ),0<W→∀ μ:ℝ,0<μ→∀ o:ConnectedActivityE6.Target.Order G W,
    ∀ J:ℕ,∀ (Y:ℝ→ℝ)(n:ℝ→ℕ), Reserve G L Y→ Reserve G L (fun x=>(n x:ℝ))→∃ (u τ:ℝ→ℝ), Reserve G L u ∧ Reserve G L τ ∧ ∀ᶠ x in atTop,
      ∀ (c f:Side) (S:StepData c f) (T':Tube G S), S.patch=D→Stamp T'→∀ (R:Rep G f) (C'':ℝ) (H:Cash W x μ L Q o C'' T' R),
        1 ≤ τ x ∧ ∃ (q d v t A a' r B e A₁ B₁ C₁:ℝ)(k:ℕ)(N:Captain H j q d v t A a' r B e k χ), ∀ (ι:Type) [Fintype ι] (M:ι→Leaf R),
         let W':= melod M H (rails H N.conduit (∅:Set ℕ) 0 C₁ A₁) B₁ k; Lyric.Paid M H χ N W' ∧ ∀ (P':Type)[Fintype P'](X':P'→ Site f)(L':ι→Finset P')(l:ι→ℝ)(σ:ℝ), Scale X' L' M l (n x) σ (Y x) S → radiusCost Q L σ→ Ac.Hit (Captain.reachability (H:=H)) (radiusB x) (fun z=>∑ i:Syllable M H z, Lyric.Bill M H W' z (Lyric.mulScale (τ x)⁻¹ l) j i J) a (u x):=by
   obtain ⟨m,hM⟩:= seeds P Q; refine ⟨m,fun L hL D hD j ε a ha hε he χ W hW μ hm o J Y n hY hJ=> ?_⟩
   obtain ⟨A,a',C₀,C',d,v,t,B,r,T,p,w,k,hC,hC',hF,hv,hB,hR,htP,hp,h,hH'⟩:= hM L hL D hD j χ W hW μ hm o
   obtain ⟨V',hV, τ,γ,S',hT,hP,hS,hB⟩:= gear_writ Q (j:=j) (n:=k) (κ:=C') C₀ hY p hp hm ε htP n hJ
   have hb:= Halo.lumens (j:=j) (k:=k) Q ε hp hP; have hK:= Halo.lumens (j:=j) (k:=J) Q ε hp hP
   refine ⟨_,τ,hK.2.mul (hb.1.mul (Reserve.const (1-1/2)⁻¹)),hT,?_⟩
   filter_upwards [hH',hB] with x hh hv c f S T' hS hΛ R C'' H
   obtain ⟨N,-,-,hN⟩:= hh c f S T' hS hΛ R C'' H
   have ha': 0≤ p x:= (h x).2; have he':= Presents.zeroG R
   refine ⟨hv.pace,_,_,_,_,_,_,_,_,_,T x,p x,C',k,N,fun ι _ M=>?_⟩
   exact ⟨ Halo.earns M H χ N _ k (p x) ha' (rails_nonneg H N.conduit ∅ 0 C' (T x) he' hC' (h x).1) (fun M p=>hN.ready M ∅ 0 _ he' zero_le_one p), fun P' _ X' L' l σ hP hI=> (Halo.catkin M H χ N l C' (T x) _ hN hv hP hI hC' (h x).1 (h x).2 he ha hε J).2⟩
-- Works independent of which E/K decompositions called.
lemma gallery (P:Teller G) (Q:YM.ConnectedActivityE6.Target G P): ∃ l:ℕ,∀ L:Side,l≤L.val → ∀ (D: Patch), D.Branches P.bind G →
    ∀ (j:ℕ) (ε a:ℝ),0≤a→0<ε→a+ε+ε≤ Q.exp→∀ χ (W:ℝ),0<W→∀ μ:ℝ,0<μ→∀ o:ConnectedActivityE6.Target.Order G W,
    ∀ I J:ℕ,∀ (Y:ℝ→ℝ)(n:ℝ→ℕ), Reserve G L Y→ Reserve G L (fun x=>(n x:ℝ))→∃ u, Reserve G L u ∧ ∀ᶠ x in atTop,
      ∀ (c f:Side) (S:StepData c f) (T':Tube G S), S.patch=D→Stamp T'→∀ (R:Rep G f) (C'':ℝ) (H:Cash W x μ L Q o C'' T' R),
        ∃ (q d v t A a' r B e:ℝ)(k:ℕ)(N:Captain H j q d v t A a' r B e k χ), ∀ (ι:Type) [Fintype ι] (M:ι→Leaf R),
         ∃ W', Lyric.Paid M H χ N W' ∧ ∀ (P':Type)[Fintype P'](X':P'→ Site f)(L':ι→Finset P')(l:ι→ℝ)(σ:ℝ), Scale X' L' M l (n x) σ (Y x) S → radiusCost Q L σ→ Ac.Hit (Captain.reachability (H:=H)) (radiusB x) (fun z=>∑ i:Syllable M H z, if Lyric.notes M H z i≤I then Lyric.Bill M H W' z l j i J else 0) a (u x):=by
   obtain ⟨m,hM⟩:= seeds P Q; refine ⟨m,fun L hL D hD j ε a ha hε he χ W hW μ hm o I J Y n hY hJ=> ?_⟩
   obtain ⟨A,a',C₀,C',d,v,t,B,r,T,p,w,k,hC,hC',hF,hv,hB,hR,htP,hp,h,hH'⟩:= hM L hL D hD j χ W hW μ hm o
   obtain ⟨V',hV, τ,γ,S',hT,hP,hS,hB⟩:= gear_writ Q (j:=j) (n:=k) (κ:=C') C₀ hY p hp hm ε htP n hJ
   have hb:= Halo.lumens (j:=j) (k:=k) Q ε hp hP; have hK:= Halo.lumens (j:=j) (k:=J) Q ε hp hP
   refine ⟨_,(hT.pow I).mul (hK.2.mul (hb.1.mul (Reserve.const (1-1/2)⁻¹))),?_⟩
   filter_upwards [hH',hB] with x hh hv c f S T' hS hΛ R C'' H
   obtain ⟨N,-,-,hN⟩:= hh c f S T' hS hΛ R C'' H
   have ha': 0≤ p x:= (h x).2; have he':= Presents.zeroG R
   refine ⟨_,_,_,_,_,_,_,_,_,_,N,fun ι _ M=>?_⟩
   exact ⟨_, Halo.earns M H χ N _ k (p x) ha' (rails_nonneg H N.conduit ∅ 0 C' (T x) he' hC' (h x).1) (fun M p=>hN.ready M ∅ 0 _ he' zero_le_one p), fun P' _ X' L' l σ hP hI=> (Halo.charm M H χ N l C' (T x) _ hN hv hP hI hC' (h x).1 (h x).2 he ha hε J I).2⟩
end YM.RemainderComparison.Halo
