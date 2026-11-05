import YM.UVExtension.Dales.Inspire
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Dales
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext PhysicalNext.Repeat
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost
open Progress.DirectedRecipe Time Rain
open Wick Lamppost YM.UVExtension.Concert
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Guild Tabernacle
open Whirl PhysicalNext.Repeat.Graces
variable {G : Gauge} {X:Metals G} {D:Rolls X.p} {A : Alloy X D} (R:Factor A)
   {N m n : ℕ}{ε : ℝ}
local notation "R₁" => A.B.a.budget (m+1)
local notation "B" => A.B.a
local notation "Y" => A.B.a.clock.hatBeta (m+1)
local notation "Pv" => mount R N (m+1) n 0 (A.B.a.clock.hatBeta (m+1)) 0
variable (hG:G.Simple) (t:Crest R ε) (H: Tour R N m n ε) (d:Cham A.B.a (m+1) n)
variable (v:Fin 4→ Valve (m+1) n A.B.a d)
    (hv:∀ i,‖place A.B.a (m+1) n d (v i)‖ ≤1){u:ℝ}(T:Paperwork R.shape ε u A.delay) {C:ℝ}(hc:InsideB (A.B.a.clock.hatBeta (m+1)) C)
local notation "B₀"=> A.B.a.clock.hatBeta m
local notation "N₀"=> A.B.a.clock.J m
local notation "N₁"=> A.B.a.clock.J (m+1)
local notation "T₁"=> betaF G (A.B.a.clock.hatBeta m) (D.L (A.B.a.clock.J (m+1)))
local notation "d₁"=> D.L (A.B.a.clock.J (m+1))
variable {V:Cham A.B.a m n}(he : Tour.Hind R hG t H d V)
open Tour
open Oriel Oriel.Charted

lemma photo (V:Type)[AddCommGroup V][Module ℝ V] (W:Fin 4→ℝ × V)(w:Fin 4→ℝ)(hw:∀ i,|(W i).1|≤1)(h:∀ i,|w i|<radiusU) : tick W w=((Rhue _ w hw h).val none,tick (fun i=> (W i).2) ((Rhue _ w hw h).val∘some)):= by
    unfold Oriel.tick; simp_rw [Fin.sum_univ_four]; apply Prod.ext; · simp [Tabernacle.Rhue, Fin.sum_univ_four]
    rfl

variable (C)
abbrev Flows (T:Levels G)(m n:ℕ)(d:Cham T m n):= ℝ × Valve m n T d
abbrev Flow (T:Levels G)(m n:ℕ)(d:Cham T m n):= ℂ × Hold T m n d
abbrev river (T:Levels G)(m n:ℕ)(d:Cham T m n): Flows T m n d→ₗ[ℝ] Flow T m n d := Tabernacle.joint (place T m n d)
lemma eddies (T:Levels G)(m n:ℕ)(d:Cham T m n)(v:Flows T m n d):‖river T m n d v‖=max |v.1| ‖place T m n d v.2‖ := by
    change max ‖(v.1:ℂ)‖ _=_; rw [Complex.norm_real]; rfl

def flowing (C:ℝ) (v:Flows A.B.a (m+1) n d):ℂ:= ↑(H.claim R d v.2 (art Y C v.1))
def marble (C:ℝ) (v:Flows A.B.a (m+1) n d):= place B m n V (H.choiceV R hG t d he v.2 (art Y C v.1))

variable {C}
include hG t T he hc
lemma skies (W: Fin 4→ Flows A.B.a (m+1) n d) (hm:∀ i,‖river A.B.a (m+1) n d (W i)‖≤1):Nonempty (Reel (flowing R H d C) (Yard.rake Y) W)∧ Nonempty (Reel (marble R hG t H d he C) u W):= by
    let z:=fun i=> (W i).2; have hz(i):‖place B (m+1) n d (z i)‖≤1:=le_trans (le_max_right _ _) ((eddies ..).symm.trans_le (hm i))
    have ht (i):|(W i).1|≤1:= le_trans (le_max_left ..) ((eddies ..).symm.trans_le (hm i))
    obtain ⟨⟨F,hF,hM,hK⟩,X,hX,hx,hJ⟩:= high R hG t H d z hz T hc he
    let q s:= spent R d z hz T hc s -- prop
    constructor
    · apply reed W _ F hF hK hM ht; intro w hg; let s:=Rhue _ w ht hg
      unfold flowing; rw [photo _ W w ht hg]; change (↑(Tour.bonus R H d (q s)):ℂ)= ↑(Tour.claim R H d (songs d z (mapsA s)) (art Y C (s.val none))); unfold claim; rw [dif_pos (q s)]
    apply reed W _ X hX hx hJ ht; intro w hg; let s:=Rhue _ w ht hg
    unfold marble; rw [photo _ W w ht hg]; change _=place A.B.a m n V (Tour.choiceV R hG t H d he (songs d z (mapsA s)) (art Y C (s.val none))); rw [choiceV,dif_pos (q s)]

structure Order {G:Gauge} {T:Levels G} {m n:ℕ} {d:Cham T m n} {K:Type} [NormedAddCommGroup K] [NormedSpace ℂ K]
    (f : Flows T m n d → K)(M:ℝ) (F:Flow T m n d→K) : Prop where
    bounds : Bumps Grip F ∧ (∀ x∈Grip, ‖F x‖≤ M)∧(∀ x∈Grip,∀ y∈Grip, ‖F x-F y‖ ≤ M*‖x-y‖)
    ray (x:Flows T m n d): (river T m n d x)∈ Grip → F (river T m n d x)=f x
lemma shelves : (∃ F, Dales.Order (d:=d) (flowing R H d C) (Yard.rake Y) F) ∧∃ F,Dales.Order (d:=d) (marble R hG t H d he C) u F:=by
    have hm:Firm (river A.B.a (m+1) n d):= (d.weather ..)
    have hp := @skies G X D A R N m n ε hG t H d u T C hc V he
    constructor
    · obtain ⟨F,a,b,c,g⟩:= Oriel.conquest _ hm (show Charted _ (flowing R H d C) (Yard.rake Y) from ⟨fun W he=> (hp W he).1⟩); exact ⟨F,⟨a,b,c⟩,g⟩
    obtain ⟨F,a,b,c,g⟩:= Oriel.conquest _ hm (show Charted _ (marble R hG t H d he C) u from ⟨fun W he=> (hp W he).2⟩); exact ⟨F,⟨a,b,c⟩,g⟩
end YM.UVExtension.Dales
#print axioms YM.UVExtension.Dales.shelves
