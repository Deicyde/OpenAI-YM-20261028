import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cadre.Tassel
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Curtail
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Kiln
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Morning
import YM.Push.BETA_TRANSPORT.Score



set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Daisy
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond Mixed Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
open Greenbelt Gas Multiple Ursell Trees Letter OmitClusters March
namespace Charity
variable (M:Leaf R) (H:Cash W x μ L Q o C T R)
    {s Y A b B C' v d q u r:ℝ}{j n:ℕ}{χ:Chi} (N: Captain H j q d v Y A b r B C' n χ)

-- values with marked parameter, still original projection. scalar λ applied unnormalized all branches and before path W. 
abbrev color (M:Leaf R)(H:Cash W x μ L Q o C T R) (χ : Chi) (V : Config G c) (t : ℝ) (m:Molecule S):= H.spawn χ V m+t*M.lotus T x χ o.K W o.a Q.table Q.halo V m
variable (χ : Chi)
lemma sprouting (V:Config G c)(t:ℝ): H.TaggedW (color M H χ V t):=by
  intro i hi; by_cases hp: H.spawn χ V i=0
  swap
  · obtain ⟨hx,-,hq,-⟩:= H.resident χ V _ hp; exact ⟨hx,hq⟩
  unfold color at hi; rw [hp,zero_add] at hi; obtain ⟨h,-,-,-,-,ha⟩:= withermore M H V (χ:=χ) (right_ne_zero_of_mul hi); exact ⟨h,ha⟩

private lemma one_mark {A : Type*} [DecidableEq A] (p:A→ℝ)(q:A→ℝ)(t:ℝ)(S : Finset A)(h:∀i∈ S,q i≠0→ ∀j∈S,j≠i→ q j=0) :
    (∏ i∈S,(p i+t*q i))=(∏ i∈S,p i)+t*∑ i∈ S,q i * ∏ j∈ S.erase i, p j :=by
  by_cases ht:∃ i∈ S,q i≠0
  · obtain ⟨i,hi,hq⟩:= ht
    rw [← mul_prod_erase _ _ hi, Finset.sum_eq_single i, show ∏ j∈ S, p j=p i * ∏j∈ S.erase i,p j from (mul_prod_erase S p hi).symm]
    · rw [show ∏ i∈ S.erase i,(p i+t*q i)=_ from (prod_congr (g:=p) rfl fun j hj=> by rw [h i hi hq j (mem_of_mem_erase hj) (ne_of_mem_erase hj),mul_zero,add_zero])]; ring
    · intro j hj hx; rw [h _ hi hq j hj hx,zero_mul]
    simp [hi]
  push Not at ht; rw [show (∑ i∈S,q i * ∏ j∈ S.erase i,p j)=0 from Finset.sum_eq_zero fun i hi=> by rw [ht i hi,zero_mul],mul_zero,add_zero]; exact prod_congr rfl fun i hi=>by rw [ht i hi,mul_zero,add_zero]
lemma sprained (V: Config G c) (t:ℝ)(Z:Finset (Molecule S)): H.festo V (color M H χ V t) Z=festival T x χ o.K Q.table V R W o.a Q.halo Z+t*M.blossom T x χ o.K W o.a Q.table Q.halo V Z:=by
  unfold Cash.festo festival Leaf.blossom; dsimp only; split_ifs with hx
  swap; · simp
  let f m:=M.lotus T x χ o.K W o.a Q.table Q.halo V m; have hh i (hi:i∈Z)(hm:f i≠0) j (hj:j∈Z)(he:j≠i):f j=0:=by by_contra h; apply Finset.disjoint_left.mp (Matter.unweave hx.1 hj hi he) (show M.turn.badge S∈id j from (withermore M H V h).2.2.1) (show M.turn.badge S∈ id i from (withermore M H V hm).2.2.1)
  exact one_mark (H.spawn χ V) f t Z hh
lemma tint (V:Config G c)(t:ℝ)(F:Forest S.ratio): HasSum (fun p=> overhead (prism T x χ o.K V F) R Q.table * H.festo V (color M H χ V t) p)
    (S.push R.beta R.eval V+t*S.push R.beta M.cicada V):=by
  have he:= (Greenbelt.organizes T x χ H V (prism T x χ o.K V F) rfl rfl); have hp := M.summons T x χ H F V
  simp_rw [sprained M H χ,mul_add,mul_left_comm (overhead _ _ _) t]; exact he.add (hp.mul_left t)
section energy
-- λ orders <1/D. regular weight Stern inflated.
local notation "d0" => jewelDebt M Q L x
-- energy: universal Stern

def sip (i:H.ThinP):=B*persona M H q (N.conduit.flair) 0 n 0 i.val
def momentS (i:H.ThinP):=B*N.conduit.meant i.val n
-- 2^(j+2) slack accounts for marked order+ also reanchoring.
def zoe (i:H.ThinP):ℝ:=2^(j+2)*(momentS H N i +2*sip M H N i)
def za (i:H.ThickP):=H.broadPay n i +2*persona M H C H.opt 0 0 1 i.val
lemma rise (i:H.ThinP):0≤ sip M H N i:= mul_nonneg N.balance (earned M H q _ (N.conduit.fares) ..)
lemma right (i:H.ThinP):0≤ momentS H N i:= mul_nonneg N.balance (N.conduit.meant_nonneg ..)
lemma rises (i:H.ThinP):0≤ zoe M H N i:=by unfold zoe; have hp:=rise M H N i; have hv:=right H N i; positivity
lemma rides (n:ℕ)(i:H.ThickP):0≤ za (n:=n) M H i:=by unfold za; have hp:=earned M H C H.opt H.positive 0 0 1 i.val; have hx:0≤ H.broadPay n i:= H.ours_pos ..; positivity

-- Strom at endpoint
lemma warm {χ:Chi} {N: Captain H j q d v Y A b r B C' n χ}(h:Herd H N.conduit A B n)(V: Config G c)(y:ℝ)(hy:|y| * (d0) ≤1)(i:H.ThinP) : Est (zoe M H N i) d0 y (fun t=> H.entriesMill (color M H χ V t) i) :=by
  have hm:= N.collective i V
  have he':= debtor (p:=i.val) M H h i.2.2
  have he:H.entriesMill (M.lotus T x χ o.K W o.a Q.table Q.halo V) i=masked (Pressure.temp x) (H.unionP i.val)
      (escort M χ Q.table i.val Q.halo T W x o.K o.a) V:= congr_fun he'.2.2.2.1 V
  have hb (w : Config G c → ℝ) (f : ℝ)(hU: 0≤f)(hw:Healthy (Pressure.temp x) (H.smallAt i) V→Ore V w v f j) : |masked (Pressure.temp x) (H.smallAt i) w V| ≤ f :=by
    by_cases hu: Healthy (Pressure.temp x) (H.smallAt i) V
    · rw [masked_eq _ _ _ _ hu]; exact (hw hu ℝ (fun _=> V) 0 rfl (show Mode .. from ⟨N.position.le,fun i=> a_oneB G _ N.position.le⟩)).bound
    rw [masked_ne _ _ _ _ hu,abs_zero]; exact hU
  have hQ' := (dew M H).2.1
  have hp : Est (momentS H N i+2*sip M H N i) d0 y (fun t=>H.entriesMill (color M H χ V t) i):= by
    apply (Est.tilted y (H.entriesPool χ V i) (H.entriesMill (M.lotus T x χ o.K W o.a Q.table Q.halo V) i) (momentS H N i) (sip M H N i) d0 _ _ hy (rise M H N i) hQ')
    · rw [hm.1]; exact hb _ _ (right H N i) hm.2
    rw [he]; exact hb _ _ (mul_nonneg hQ' (rise M H N i)) (he'.2.2.2.2 V)
  exact hp.upto (le_mul_of_one_le_left hp.good (one_le_pow₀ (by norm_num : (1:ℝ)≤2)))
lemma cold (V:Config G c)(y:ℝ)(hy: |y| * d0 ≤1)(i:H.ThickP): Est (za M H (n:=n) i) d0 y (fun t=>H.depositsMill (color M H χ V t) i):=by
  have hp:= petals M H (χ:=χ) V 0 0 1 (Nat.zero_le _) (Cash.forced_cost i.val i.2.2); rw [pow_zero, mul_one] at hp
  exact Est.tilted _ _ _ _ _ _ ((H.renew χ V n).2 i) hp hy (earned M H C _ H.positive ..) (dew M H|>.2.1) -- parse
end energy
end Charity
end YM.PhysicalNext.Repeat.Daisy
