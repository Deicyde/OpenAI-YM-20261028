import YM.UVExtension.Dales.Corn
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

def vi(i:Fin 4): Juice G (A.B.a.S.side (m+1) n):= ⟨(v i).val.1,(v i).val.2⟩
abbrev songs (s: Fin 4 →ℝ):= Oriel.tick v s
lemma modE {b:ℝ}(s : Fin 4→ℝ): chunk Pv (blend (vi d v) s) b=mount R N (m+1) n (songs d v s).val b 0:= by
  have he(i U): (blend (vi d v) s).E i U=(songs d v s).val.1 i U:=by
     unfold blend songs Oriel.tick; dsimp; rw [Submodule.coe_sum]; simp [vi,Fin.sum_univ_four]
  have hh(i U): (blend (vi d v) s).K i U=(songs d v s).val.2 i U:=by
     unfold blend songs Oriel.tick; dsimp; rw [Submodule.coe_sum]; simp [vi,Fin.sum_univ_four]
  unfold chunk mount; unfold Wick.flight Tabernacle.floor; dsimp only; rw [show (blend (vi d v) s).E= _ from funext fun i=> funext (he i), show (blend (vi d v) s).K= _ from funext fun i=> funext (hh i)]
include hv
lemma realT (b:ℝ)(hx:b∈RG.Shoot.band A.B.a (m+1))(s:Fin 4→ℝ)(hp:∀ i,|s i|≤realcap): Reality A.B.a (m+1) n d (songs d v s) b:= by
    refine ⟨hx,?_⟩
    unfold songs Oriel.tick; rw [map_sum]; apply (norm_sum_le ..).trans
    refine le_trans (Finset.sum_le_sum (g:=fun _=>realcap) (fun i _=>?_)) (by norm_num [realcap]); rw [map_smul,norm_smul]; exact (mul_le_of_le_one_right (norm_nonneg _) (hv i)).trans (hp i)
include H
lemma fetes : Festa (R.target N₁ N₀) d₁ H.atTopH (vi d v) realcap (Payroll.hearts G d₁ B₀) := by
  have ht : Y=T₁:= PriceCompiler.beta_eq A.B.valid m
  have hc:1< T₁:= ht ▸ A.B.a.fits.delayed _
  have hp(k)(_h:k∈ Wick.aisle T₁): Complex.re k∈RG.Shoot.band A.B.a (m+1):=by unfold RG.Shoot.band; rw [ht]; exact ⟨_h.1.le,_h.2.1.le⟩
  refine ⟨by norm_num [realcap],?_, fun x hx=>?_,fun i x hx=>?_,fun z hz=>?_⟩
  · unfold Payroll.hearts; exact (by norm_num [realcap] : realcap ≤1).trans (Real.one_le_rpow hc.le (by norm_num [Payroll.fillSpeed]))
  · let z: Valve (m+1) n A.B.a d:=0; obtain ⟨f,h⟩:=outset R z.val _ 0 ((tapT _ n _ d z).1 (by simp [z])) (hp x hx) H.hm; exact ⟨f⟩
  · exact ⟨(outset R (v i).val _ 0 ((tapT (m+1) n _ d _).1 (hv i)) (hp x hx) H.hm).choose⟩
  let a:= z ∘ some; have he := hp (↑(z none)) (show _ from hz none)
  have hx := H.oracle R d (realT d v hv _ he a (fun i=>mem_ball_zero_iff.mp (hz (some i)) |>.le)) 0
  rw [modE R d v]; exact ⟨hx.atH⟩

-- J payout including scalar (0 here)
omit hv H
lemma notch (T:Paperwork R.shape ε u A.delay): Lamppost.Chateau G d₁ ε (X.p.profile N₀) B₀:= (T.chord _ _ (step_paid A.B.a m) _ (A.B.valid.pays m)).2.1 -- should lemma
include hc
lemma staple : InsideB T₁ C:= PriceCompiler.beta_eq A.B.valid m ▸ hc
-- sells to all real chart; mapping
local notation "J0"=> Canvas (T₁) realcap (Fin 4)
local notation "η!"=> vi d v
def openingA (x:Canvas T₁ realcap (Fin 4)) := freshen x Pv (vi d v)
abbrev mapsA (x:Arbor) : Fin 4→ ℝ:= x.val∘ some
include hv H d
omit hc in
lemma topbar (x : Canvas T₁ realcap (Fin 4)):∃ J:Guide A.B R.shape N m n (openingA R (N:=N) d v x), Opera.Price A.B R.shape N m n (openingA R (N:=N) d v x) J:=by
    unfold openingA freshen; rw [modE R (N:=N) d v]; apply outset
    · have h:=realT d v hv (x.val none) (Payroll.stageNote x|>.property) (x.val∘some) (fun i=> mem_ball_zero_iff.mp (x.2 (some i))|>.le); exact (tapT (m+1) n A.B.a d _|>.1 h.2)
    · exact Payroll.stageNote x|>.property
    exact H.hm

-- map from real Arbor
include T hc
variable (s:Arbor)
def billA (x:Arbor) : Canvas T₁ realcap (Fin 4):= Guild.maple (notch R T) (staple hc) x
-- use s around C, physical β coordinate

def art (y : ℝ) (C v:ℝ): ℝ:= C+stretchB y*v
omit H in
lemma spent (s:Arbor) : Reality A.B.a (m+1) n d (songs d v (mapsA s)) (art Y C (s.val none)):= by
  apply realT d v hv
  · have hz:= Payroll.stageNote (billA R T hc s)|>.property
    change C+stretchB (T₁)* s.val none∈ RG.Shoot.band A.B.a (m+1) at hz -- not defin because Function.update
    rw [show Y=T₁ from PriceCompiler.beta_eq A.B.valid m]; exact hz
  intro i; exact s.2 _ |>.le
end YM.UVExtension.Dales
