import YM.UVExtension.Spire.That
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Spire
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
open Dales Camp Whirl Oriel Oriel.Charted Tour Above Tabernacle WilsonStartup
variable {G : Gauge} {X: Metals G} {D:Rolls X.p} {A : Alloy X D} (R:Factor A)
    (hG:G.Simple){ε:ℝ}(t:Crest R ε)(u:Paperwork R.shape ε Camp.soft A.delay)
    (hk:Planned.Port.AtTop A.B.kin)(hp:∀ N,Start.Allows A.B.a N)(h:∀ N,Entry A.B.a N soft)(N n:ℕ)
open Cart
namespace Fitted
variable {R hG t hk hp N n} (H:Fitted R hG t hk hp N n)
    (V:Cart A.B.a N H.Hut)(he:H.Took V) {z:PlotN N}(hv:z∈Harbor N)(hZ: Cart.Light N z)
    {b:ℝ}
local notation "a!" => A.B.a
local notation "cN" => A.B.kin.alpha N
local notation "W#"=> H.W N
variable {f: ∀ i, H.Home i}{β:ℕ→ℝ}{s:ℕ→ℝ}(hs:Shot H f β s)
    (hb: (↑b:ℂ)∈ Camp.Broad A.B.a)(hr:β 0=A.B.a.clock.bar+b)
include hs
variable (hf: Fees A.B.a)
local notation "u!"=> port R N β
omit hs in
lemma here (i:ℕ)(hi:i≤N): lock R (port R N β) i hi= β i:= by
   unfold lock Dales.art Cart.node port; simp only [Complex.ofReal_re]; unfold cut; rw [← show (Camp.pulse A.B.a i)= _ from rfl] -- rw pattern
   change _ + Camp.pulse A.B.a i* (_/Camp.pulse A.B.a i)= _; rw [mul_div_cancel₀ _ (pulse_pos A.B.a i).ne',add_sub_cancel]

lemma files (i:ℕ)(hi:i≤N): H.file (port R N β) i hi = f i:= by
    induction hi using Nat.decreasingInduction with
    | self=>
      rw [H.top_mom hs]; unfold file; rw [Nat.decreasingInduction_self]; rw [here N le_rfl,singleA,dif_pos (hs.alive N le_rfl).1] -- recursive binder
    | of_succ i hi ih=>
      let J:= H.charts i hi; have hF: H.file u! i hi.le= Tour.choiceV R hG t J _ (H.shirts i hi) (H.file u! _ hi) (lock R u! _ hi):= Nat.decreasingInduction_succ_left _ _ _ _
      rw [hF,ih,here _ hi,Tour.choiceV,dif_pos (hs.alive _ hi)]; exact (H.doors hs i hi).2.1.symm
include u h hb hr he hf
lemma solos : port R N β = V.picked hG a! N H.Hut hf (b:=(b:ℂ)):=by
    have hv:= H.pivots u h hs hb hr hf; have hS : Cart.Light N u! := fun i=> Complex.ofReal_im _; let z:= u!
    have hm (i:ℕ) (hi:i<N) : V.tally a! N H.Hut z i= ↑(Tour.bonus R (H.charts i hi) _ (hs.alive _ hi)):= by
       rw [H.bonusR V he hv hS i hi]
       simp_rw [H.files hs _ hi,here _ hi]
    refine (Cart.unique hG a! N H.Hut V hf hb ?_ hv).symm
    have hE (i:ℕ)(hi:i≤N): (β i:ℂ)= (Camp.slope a! cN i:ℂ)+((b:ℂ)- ∑ j∈Finset.range i, V.tally a! N H.Hut z j):= by
       induction i with
       | zero=> rw [hr, Complex.ofReal_add,Camp.first]; simp
       | succ i ih=>
         let u:=Tour.bonus R (H.charts i hi) _ (hs.alive _ hi); have hf : (↑(β i):ℂ)=(β (i+1):ℂ)+(A.B.kin.alpha N i:ℂ)+ (u:ℂ):= by rw [show _+_+(u:ℂ)= (↑(β (i+1)+A.B.kin.alpha N i + u):ℂ) from (by push_cast; rfl)]; exact congr_arg Complex.ofReal (H.doors hs i hi).1 -- tactic risk
         rw [show (β (i+1):ℂ)= ((β i:ℂ)-(A.B.kin.alpha N i:ℂ))-(u:ℂ) from (by rw [hf]; abel), ih (Nat.le_of_succ_le hi),← Camp.plus A.B.a i,Finset.sum_range_succ,hm _ hi,Complex.ofReal_add]; change _ - (u:ℂ)=_ + (_ - (_+ (u:ℂ))); abel
    funext i; unfold Cart.veil; conv_rhs => rw [port,cut]
    push_cast
    rw [hE _ (Nat.le_of_lt_succ i.isLt)]; change (Camp.pulse A.B.a i.val:ℂ)⁻¹*( (b:ℂ)- ∑ j∈Finset.range i.val,V.tally a! N H.Hut z j)= _; ring

lemma unions {g:∀ i,H.Home i} {w q:ℕ→ℝ}(hp:H.Shot g w q)(hy:w 0=A.B.a.clock.bar+b) (i)(hi:i≤N): f i=g i ∧ β i=w i ∧ s i=q i:= by
    have hh : port R N β=port R N w:= (H.solos u h V he hs hb hr hf).trans (H.solos u h V he hp hb hy hf).symm
    have he'(i)(hi:i≤N): f i=g i∧ β i=w i:=by
       refine ⟨(H.files hs i hi).symm.trans ((congr_arg (fun z=> H.file z i hi) hh).trans (H.files hp i hi)),?_⟩; exact (here (R:=R) (β:=β) i hi).symm.trans ((congr_arg (fun z=> lock R z i hi) hh).trans (here ..))
    induction hi using Nat.decreasingInduction with
    | self=> refine ⟨(he' N le_rfl).1,(he' N le_rfl).2,?_⟩; exact (show s N=0 from congr_arg RG.Rep.v hs.bare).trans (show q N=0 from congr_arg RG.Rep.v hp.bare).symm
    | of_succ i hi ih=> refine ⟨(he' i hi.le).1,(he' i hi.le).2,?_⟩; rw [(H.doors hs i hi).2.2,(H.doors hp i hi).2.2]; simp only [race,ih.1,ih.2.1,ih.2.2]
end Fitted
end YM.UVExtension.Spire
#print axioms YM.UVExtension.Spire.Fitted.unions
