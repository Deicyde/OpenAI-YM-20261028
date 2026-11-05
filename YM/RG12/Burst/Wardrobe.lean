import YM.RG12.Burst.Keys
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Eco
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Daisy.Charity.RG12
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond Mixed Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
open Greenbelt Gas Multiple Ursell Trees Letter OmitClusters Blaze.March
open Mallow
open Push.SectorMeasure
-- parameterized public chronological requests, so future consumers share grant easily.
structure Decal (G : Gauge) where
    rub : ∀ (P : Teller G) (Q : ConnectedActivityE6.Target G P) (_:Target.Expense Q)(_L:Side)(W _μ:ℝ), Target.Order G W → RG.Stage → ℕ → ℝ → Prop
    good (P_ : Teller G) (Q : ConnectedActivityE6.Target G P_) (E : Target.Expense Q) : ∃ n:ℕ, ∀ (L:Side), n ≤ L.val → ∀ W μ o h i, E.wanting ≤ (-(7/16):ℝ) →  0<W → 0<μ → ∀ᶠ x:ℝ in atTop, rub P_ Q E L W μ o h i x
namespace Decal
def paired (D E:Decal G):Decal G where
    rub P Q R S A B h j i x:= D.rub P Q R S A B h j i x ∧ E.rub P Q R S A B h j i x
    good P Q R:= by obtain ⟨n,h⟩:=D.good P Q R; obtain ⟨m,h'⟩:=E.good P Q R; exact ⟨max n m,fun _ hu _ _ _ _ _ hz hp hv=> (h _ ((le_max_left ..).trans hu) _ _ _ _ _ hz hp hv).and (h' _ ((le_max_right ..).trans hu) _ _ _ _ _ hz hp hv)⟩
end Decal
-- `N10` count horizon: can issue through any fixed (e.g. J) mark price; no growing proof use unless calendar.A.E. Use spectral exponent inside eligible Q.
def height (Q:ConnectedActivityE6.Target G P):ℝ:=(-Q.rate+7/16)/2
def beam10 (_Q:ConnectedActivityE6.Target G P) (m:ℕ) : ℝ:= if 3 ≤ m then -(7/16)*(m-1:ℝ) else -(7/16)*(m-1:ℝ)+1/8

def Attic (Q:ConnectedActivityE6.Target G P) (Γ:Target.Expense Q)(L:Side) (W μ:ℝ) (o:Target.Order G W) (D:RG.Stage) (p:ℕ) (x:ℝ) : Prop:=
   let s : ℝ:= betaF G x L^ height Q
   1≤ s ∧ 0< betaF G x L ∧ foam Q L ∧ Trees.degreePrice (radiusB x) (s*(Q.costs L μ 1 x 0).rootHit) Q.δ≤1/2 ∧ Trees.degreePrice (radiusB x) (s*(swing Q L μ 1 x 0).rootHit) Q.δ ≤1/2 ∧
    ∀ (c f:Side)(S:StepData c f)(T:Tube G S), Stamp T → ∀ R C (H :Cash W x μ L Q o C T R), ∃ (A a q d v t r B k E :ℝ) (n:ℕ), Bikes Q L μ x Γ.earn E B D.order n ∧ Trees.degreePrice (radiusB x) (Q.goal L x+ value10 Q L μ x s B D.order n) E≤1/2 ∧
      (∀ m ≤ p,∀ d ≤ p, 2*(Push.Local.readPrice (Next.Foundations.hol G) ((Labels.frames G).level d)*1)*(((L.val:ℝ)^d))*cash10 Q L μ x s B D.order n E D.power m ≤ betaF G x L^(beam10 (G:=G) Q m)) ∧ ∃ N : Captain H D.order q d v t A a r B k n Chi.canonical, Herd H N.conduit A B n

lemma annex (Q:ConnectedActivityE6.Target G P) (Γ:Target.Expense Q) : ∃ n:ℕ,∀ L:Side,n ≤ L.val → ∀ W μ o h i, Γ.wanting ≤ -(7/16:ℝ) →0<W → 0<μ → ∀ᶠ x in atTop, Attic Q Γ L W μ o h i x:=by
  obtain ⟨n,h⟩:= Charity.rocketsC P Q; obtain ⟨m,hE⟩:= early Q
  refine ⟨max n m,fun L hx W μ o U i hw hW hM=>?_⟩
  set b:= height Q; have hb:7/16 < b:=by unfold b height; linarith [Γ.reach]
  have hB:b+Q.rate<0:=by unfold b height; linarith [Γ.reach]
  let s x:= betaF G x L^ height Q; have hR:Rate G L b s:=Rate.power
  have hf:=hE L ((le_max_right ..).trans hx)
  have hk:∀ᶠ x:ℝ in atTop, (1≤ s x)∧0<betaF G x L:= ((Work.E09.betaF_growth G L).eventually_ge_atTop 1).mono fun x hl=>⟨Real.one_le_rpow hl (by linarith:0≤b),zero_lt_one.trans_le hl⟩
  have help : ∀ᶠ x in atTop,
    ∀ (c f:Side)(S:StepData c f)(T:Tube G S), Stamp T → ∀ R C (H :Cash W x μ L Q o C T R), ∃ (A a q d v t r B k E :ℝ) (n:ℕ), Bikes Q L μ x Γ.earn E B U.order n ∧ Trees.degreePrice (radiusB x) (Q.goal L x+ value10 Q L μ x (s x) B U.order n) E≤1/2 ∧
      (∀ m ≤ i,∀ d ≤ i, 2*(Push.Local.readPrice (Next.Foundations.hol G) ((Labels.frames G).level d)*1)*(((L.val:ℝ)^d))*cash10 Q L μ x (s x) B U.order n E U.power m ≤ betaF G x L^(beam10 (G:=G) Q m)) ∧ ∃ N : Captain H U.order q d v t A a r B k n Chi.canonical, Herd H N.conduit A B n:=by

    by_cases he:∃ D:Patch,D.Branches P.bind G∧D.L=L∧D.J=P.j
    swap; · exact Eventually.of_forall fun x c f S T _ R C H=>let h:=H.laws.data.funds; False.elim (he ⟨S.patch,h.funds.kernel,h.length_eq,h.funds.atStep⟩)
    obtain ⟨D,he,hL,hJ⟩:=he; obtain ⟨A,a,q,d,v,t,r,B,k,n',hp,-,hT⟩:= h L ((le_max_left ..).trans hx) D he U.order Chi.canonical W hW μ hM o
    let e :=(Q.exp-Γ.earn)/2; have he':0<e:=by unfold e; linarith [Γ.first,Γ.worth,Γ.second]
    have hy := ready10 Q L μ hM U.order n' B s hp hR (by linarith) hB e
    have ht(m k:ℕ):= ((paid10 Q L μ hM U.order n' U.power B (b:=b) hp (by linarith) m e).mul_left (2*(Push.Local.readPrice (Next.Foundations.hol G) ((Labels.frames G).level k)*1)*(((L.val:ℝ)^k)))) (beam10 (G:=G) Q m) (by
        have hf : b< 1/2:=by linarith [Q.start]
        unfold beam10; split
        next h=> have hh:1<(m:ℝ):=by exact_mod_cast (show (1:ℕ)< m from by omega)
                 nlinarith only [hb,hh]
        next h=> interval_cases m <;> norm_num <;> linarith)
    filter_upwards [hT, stables L Q hM B he' (v:=Γ.earn) (by unfold e; linarith) Γ.price hp U.order n' U.power, hy,eventually_all.mpr (fun m:Fin (i+1)=> eventually_all.mpr (fun k:Fin (i+1)=> ht m k))] with x hv hh hh' hz c f S T h' R C H
    exact ⟨A,a,q,d x,v x,t x,r x,B x,k x,e,n',hh.1,hh',fun m hm k hk=>(le_abs_self _).trans (hz (⟨m,Nat.lt_succ_of_le hm⟩:Fin (i+1)) (⟨k,Nat.lt_succ_of_le hk⟩:Fin (i+1))), hv c f S T ((H.laws.data.funds).patch hL hJ) h' R C H⟩
  filter_upwards [ready10' Q L μ hM s hR hB,hk,help] with x he ht hh; exact ⟨ht.1,ht.2,hf,he.1,he.2,hh⟩

def garment10 (G : Gauge) : Decal G:=⟨fun _ Q Γ L W μ=>Attic Q Γ L W μ,fun _P Q Γ=>annex Q Γ⟩
end YM.PhysicalNext.Repeat.Daisy.Charity.RG12
