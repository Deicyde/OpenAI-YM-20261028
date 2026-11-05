import YM.UVExtension.Lacing.Wallet
/-! strengthening of Gust era sockets. Follows actual expressions explicitly. `δ=0`
 genuine path.N r origins. Uses observer.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Lacing
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open Eyelet MergeProof
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}(B:SectionData F) (H : History G) (N p m : ℕ) (A : Hol G)
open Extra.Histories.InputColumn
local notation "κ"=> Real.sqrt (H.levels.clock.forcedAllowance (m+1))
local notation "Λ"=> Real.sqrt (H.levels.clock.forcedAllowance m)
variable {T : Extra.Histories.Heading F} {C η t w : ℝ}
local notation "n"=> H.S.side m p
local notation "n'"=> H.S.side (m+1) p
local notation "Old"=> H.rep N p (m+1)
set_option quotPrecheck false
local notation "R"=> H.rep N p m
local notation "O" => Bucket F (R).p A n
set_option quotPrecheck false
section
variable {ι:Type}[Nonempty ι][Countable ι]
  {f : ι → Config G (H.S.side (m+1) p)→ℂ}
  {v : ι→ F.Coeff}{u a z:ι→ℝ}
set_option synthInstance.maxHeartbeats 160000 in
set_option maxHeartbeats 400000 in
lemma vouchers {X:Set Wing} (q:GaugeDoor Old R)(hq: SoundDoor (H.levels.clock.op m p) q)
    (h:Vintage.YM.RG.History.Selected H)(hm:m≤N)(hCoins: Nonempty (Keeper (R).p (R).activities)) {g:ι→ Config G n'→ℂ}{w':ι→ Res G n'}{t:ι→ℂ}{φ:Config G n'→ℂ}{ψ:Res G n'}{σ:ℂ}(y:ι→Bucket F (R).p A n)(hp:∀ j,Sends B H N p m A q X (g j) (w' j) (t j) (f j) (v j) (u j) (a j) (z j) (y j))(hg:∀ U,HasSum (fun i=>g i U) (φ U))(hx:∀ i U,HasSum (fun j=> w' j i U) (ψ i U))(ht:HasSum t σ)
    (hf:Dominated f)(hk:∀i,Measurable (f i)) (hv:Summable fun i=> F.coeffSize (v i))(hu:Summable u)(ha:Summable a)(hζ:Summable z):
    Sends B H N p m A q X φ ψ σ (fun V=> ∑' i,f i V) (∑' i,v i) (∑' i,u i) (∑' i,a i) (∑' i,z i) (∑' j,rooms n F A (R).p (aisleN (code ι) j) (y j)):=by
   choose Q hQ Hq hδ using fun j=> (hp j).mints
   let P:= Extra.Histories.merge (code ι) Q
   have hκ:0<Λ:= Real.sqrt_pos.2 (forcedPos ..)
   have hA':= Vintage.YM.MergeProof.Gig.all_in B H N p m A h hm hQ hf hk hv hu ha
   refine ⟨P,hA', Tale.upon hq Hq hg hx (fun i U=> profile_merge (code _) Q hκ (fun i=> (hQ i).bound) ha i U) ht ⟨fun i=>?_,hζ,le_rfl⟩ ⟨fun i=> rem_nonneg ((hQ i).bound),ha,le_rfl⟩,?_⟩
   · obtain ⟨ι,h,P,p,ψ,H⟩:= Hq _; exact sumBudget_credit H.purchase
   have hj(i):Eligible (Q i) A (R) Λ:=⟨hCoins,(hQ i).format,_,(hQ i).bound⟩
   have hz':Eligible P A (R) Λ:=⟨hCoins,hA'.format,_,hA'.bound⟩
   have heZ(i):  F.coeffSize (Q i).x ≤ u i + F.coeffSize (v i):= by
      let z:= v i; let y':=(Q i).x-z
      have he' := Work.G08.size_triangle F (Q i).x z
      have hy := (hQ i).leadP; linarith only [le_mul_of_one_le_left (Work.G08.size_nonneg F y') (orbitCost_one_le F),he',hy]
   have hh:= stanza (code _) Q (fun i=> (hQ i).bound) ha hj hz' ((hu.add hv).of_nonneg_of_le (fun _=> Work.G08.size_nonneg ..) heZ)
   simp_rw [hδ] at hh; exact hh.tsum_eq.symm
end
end YM.UVExtension.Lacing
