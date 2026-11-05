import YM.MergeProof.Montage
import YM.MergeProof.Wallet

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}(B:SectionData F) (H : History G) (N p i : ℕ) (Y : Hol G)
local notation "Rout" => H.rep N p i
local notation "Old" => H.rep N p (i+1)
local notation "c'" => H.S.side i p
local notation "StartSite" => H.S.side (i+1) p
local notation "g₀" => Config G StartSite → ℂ
local notation "Lℓ" => H.S.block i
local notation "κ" => kappa H i
open Extra.Histories
set_option quotPrecheck false
section
variable {B H N p i Y} {x:Config G (H.S.side (i+1) p)→ℂ}{P:Coefficient F (H.S.side i p)}
    {q:ℝ}{v:F.Coeff}{a b t r:ℝ}
lemma Gig.weaken (h:Gig B H N p i Y x P v a b) (ht:a≤t)(hu:b≤r) : Gig B H N p i Y x P v t r:= ⟨h.format,h.agrees,h.leadP.trans ht,by obtain ⟨u,t,hf,h₁⟩:=h.future; exact ⟨u,t,hf,h₁.trans hu⟩⟩
lemma Gig.bound (h:Gig B H N p i Y x P v a b):P.remBound 0 Rout κ b:=by
   obtain ⟨u,t,hf,ht⟩:=h.future
   have he:1 ≤ turnCost (Rout).p.order (Rout).p.power:= one_le_pow₀ (one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ one_le_two))
   exact hf.bound ((add_le_add_left (le_mul_of_one_le_left hf.first he) t).trans ht)
lemma Coupon.weaken {X:Wing→Prop} {Q:GaugeDoor (H.rep N p (i+1)) (H.rep N p i)}{s z:ℝ}{v':Res G (H.S.side (i+1) p)}{T:ℂ}
    {u:Config G (H.S.side (i+1) p)→ℂ} (h:Coupon B H N p i Y x v' T Q X u v a b s)(hp:a≤t)(hq:b≤r)(hz:s≤z): Coupon B H N p i Y x v' T Q X u v t r z:=by
    obtain ⟨P,hP,hR⟩:=h; exact ⟨P,hP.weaken hp hq,hR.climb le_rfl hz hq⟩
end
section
variable {ι:Type}[Nonempty ι][Countable ι]
  {f : ι → Config G (H.S.side (i+1) p)→ℂ}{Q:ι→ Coefficient F (H.S.side i p)}
  {v : ι→ F.Coeff}{u a z:ι→ℝ}
lemma Gig.all_in (h: H.Selected)(hm:i≤N)(he : ∀ j, Gig B H N p i Y (f j) (Q j) (v j) (u j) (a j))(hf:Dominated f)(hk:∀j, Measurable (f j))
    (hv:Summable fun i=> F.coeffSize (v i))(hu:Summable u)(ha:Summable a): Gig B H N p i Y (fun V=>∑' i,f i V) (Extra.Histories.merge (code ι) Q) (∑' i,v i) (∑' i,u i) (∑' i,a i):=by
   let t:= orbitCost F
   let C:= turnCost (Rout).p.order (Rout).p.power
   have ht:1≤t:=orbitCost_one_le F; have ht':0≤t:= zero_le_one.trans ht
   have hc:1≤ C:= one_le_pow₀ (one_le_mul_of_one_le_of_one_le one_le_two (one_le_pow₀ one_le_two))
   have hk' (i):= (he i).bound; have hf' i:= (he i).format
   choose s b hB hQ using fun i=> (he i).future
   have hs:Summable s:= .of_nonneg_of_le (fun i=> (hB i).first) (fun i=> (le_mul_of_one_le_left (hB i).first hc).trans ((le_add_of_nonneg_right (hB i).second).trans (hQ i))) ha
   have hx:Summable b:= .of_nonneg_of_le (fun i=> (hB i).second) (fun i=> (le_add_of_nonneg_left (mul_nonneg (zero_le_one.trans hc) (hB i).first)).trans (hQ i)) ha
   let X i:= (Q i).x-v i
   have hp: Summable fun i=> F.coeffSize (X i):=.of_nonneg_of_le (fun i=> Work.G08.size_nonneg ..) (fun i=> (le_mul_of_one_le_left (Work.G08.size_nonneg ..) ht).trans (he i).leadP) hu
   have hζ: Summable fun i=>F.coeffSize (Q i).x:= .of_nonneg_of_le (fun i=> Work.G08.size_nonneg ..) (fun i=> Work.G08.size_triangle F _ _) (hv.add hp)
   have hκ: 0<κ:= Real.sqrt_pos.2 (forcedPos ..)
   refine ⟨merge_format (code _) Q hf',funext fun U=> ?_, ?_,∑' i,s i,∑' i,b i,(merge_tab (code _) Q hκ hB hs hx).1,?_⟩
   · rw [← (merge_density (code _) Q hκ (h.represents N p i hm).good hk' ha hζ B U).tsum_eq]; simp_rw [fun i => (he i).agrees]; rw [blast_sum H N p i d hf hk]
   · change t*F.coeffSize ((∑' i,(Q i).x)-_) ≤ _
     rw [← Summable.tsum_sub (Size.series F hζ).of_norm (Size.series F hv).of_norm]; refine (mul_le_mul_of_nonneg_left (Size.bound F hp) ht').trans ?_
     rw [← tsum_mul_left]; exact (hp.mul_left t).tsum_le_tsum (fun i=> (he i).leadP) hu
   rw [← tsum_mul_left,← (hs.mul_left C).tsum_add hx]; exact ((hs.mul_left C).add hx).tsum_le_tsum hQ ha
lemma coupons {X:Wing→Prop} (q:GaugeDoor Old Rout)(hq: SoundDoor (H.levels.clock.op i p) q)
    (h:H.Selected)(hm:i≤N){g:ι→ g₀}{w':ι→ Res G StartSite}{t:ι→ℂ}{φ:g₀}{ψ:Res G StartSite}{σ:ℂ}(hp:∀ j,Coupon B H N p i Y (g j) (w' j) (t j) q X (f j) (v j) (u j) (a j) (z j))(hg:∀ U,HasSum (fun i=>g i U) (φ U))(hx:∀ i U,HasSum (fun j=> w' j i U) (ψ i U))(ht:HasSum t σ)
    (hf:Dominated f)(hk:∀i,Measurable (f i)) (hv:Summable fun i=> F.coeffSize (v i))(hu:Summable u)(ha:Summable a)(hζ:Summable z):
    Coupon B H N p i Y φ ψ σ q X (fun V=> ∑' i,f i V) (∑' i,v i) (∑' i,u i) (∑' i,a i) (∑' i,z i):=by
   choose Q hQ Hq using hp
   let P:= Extra.Histories.merge (code _) Q
   have hκ:0<κ:= Real.sqrt_pos.2 (forcedPos ..)
   refine ⟨P,Gig.all_in B H N p i Y h hm hQ hf hk hv hu ha, Tale.upon hq Hq hg hx (fun i U=> profile_merge (code _) Q hκ (fun i=> (hQ i).bound) ha i U) ht ⟨fun i=>?_,hζ,le_rfl⟩ ⟨fun i=> rem_nonneg ((hQ i).bound),ha,le_rfl⟩⟩
   obtain ⟨ι,h,P,p,ψ,H⟩:= Hq i; exact sumBudget_credit H.purchase
end
end YM.MergeProof
