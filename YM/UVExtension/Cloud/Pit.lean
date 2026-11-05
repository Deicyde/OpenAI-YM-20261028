import YM.UVExtension.Cloud.Pop
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Cloud
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open Bid Planned.GuardedAtom Guard Metric Lamppost Motion Work.G08
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{E:Type}[NormedAddCommGroup E][NormedSpace ℂ E] {a M b:ℝ}{z:ℂ}(h: Speed M z)
    {p:BudgetPoint} {d:ℕ}{F:Frame G d}{n:Side}{A:Hol G}
local notation "Z'"=> spreadK.span
local notation "T!"=> spreadK.call
local notation "P"=> Bucket F p A n
local notation "V"=> Motion.orbitCost F
local notation "s₀"=> Push.Local.turnCost p.order p.power
local notation "N₀"=> (((F.extra+1:ℕ)):ℝ)
variable (f:ℂ→Bucket F p A n)
include h
set_option quotPrecheck false
lemma hearth (v:F.Coeff)(hf:Bumps Z' f)(hp:∀ x,Rainfall.Wallet (f (T! x)) v a b)(hz:∀ x∈Z',Rainfall.Wallet (f x) v (a*Real.exp M) (b*Real.exp M))(ha:0≤a)(hb:0≤b): Rainfall.Wallet (f z) v (2*a) (2*b):= ⟨bucks h F ha V (zero_le_one.trans (orbitCost_one_le ..)) (fun x=>(f x).1-v) (fun s p hs hv ht=> (hf s p hs hv ht|>.fst).sub_const _) (fun _=> hp _|>.earns) (fun _ h=> hz _ h|>.earns),costly h hb s₀ (zero_le_one.trans (turnCost_near ..)) (fun x=> (f x).2.1) (fun s p hs hv ht=> (hf s p hs hv ht).snd.fst) (fun _=> hp _|>.rain) (fun _ h=> hz _ h|>.rain),trusts h hb (fun x=> (f x).2.2) (fun s p hs hv ht=> (hf s p hs hv ht).snd.snd) (fun _=> hp _|>.stem) (fun _ h=> hz _ h|>.stem)⟩

-- uniform hull.Ar. Cal.Complex large at ALL coordinates.Mark.Tips. weights ask pre_L
structure Mind (F:Frame G d) (L:Side)(order power:ℕ)(u c a b M:ℝ): Prop where
    glass : orbitCost F*((F.extra+1:ℕ):ℝ)*a ≤ u*Real.exp M
    co : Push.Local.turnCost order power*a ≤ u*Real.exp M
    primary: orbitCost F*(((F.extra+1:ℕ):ℝ)*b+c*(L.val:ℝ)^d) ≤ u * Real.exp M
    ray: Push.Local.turnCost order power * b ≤ c*Real.exp M
variable {L:Side}{u c x y:ℝ}(hp: Mind F L p.order p.power u c a b M)
include hp
lemma sparks (hv:0≤u)(hx:0≤x) (hf:Bumps Z' f)(hg:∀ j,Rainfall.Wallet (f (T! j)) 0 (u*x) (u*x))(ht:∀ w∈Z', ‖f w‖≤a*x) : Rainfall.Wallet (f z) 0 (2*u*x) (2*u*x):= by
   have he:0≤V:= zero_le_one.trans (orbitCost_one_le ..); have h1: 1≤ s₀:= turnCost_near ..
   rw [mul_assoc 2]; apply hearth h f 0 hf hg _ (mul_nonneg hv hx) (mul_nonneg hv hx)
   intro z hz; let g:= f z; let l:= g.1; have ht: ‖g‖≤ a*x:=ht z hz; have hn: 0≤ (N₀):=Nat.cast_nonneg _
   have ht' : V*F.coeffSize l≤ (u*Real.exp M)*x:=by calc
       _ ≤ V*(N₀* (a*x)):=mul_le_mul_of_nonneg_left ((Push.Local.size_le_norm F l).trans (mul_le_mul_of_nonneg_left ((le_max_left ‖l‖ _).trans ht) hn)) he
       _ = V*N₀*a*x:=by ring
       _ ≤ _:=mul_le_mul_of_nonneg_right hp.glass hx
   rw [mul_right_comm u x]
   exact ⟨by rw [sub_zero]; exact ht',(mul_le_mul_of_nonneg_left ((le_max_left ..).trans ((le_max_right ‖l‖ _).trans ht)) (zero_le_one.trans h1)).trans (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hp.co hx),((le_mul_of_one_le_left (norm_nonneg _) h1).trans (mul_le_mul_of_nonneg_left ((le_max_right ..).trans ((le_max_right ‖l‖ _).trans ht)) (zero_le_one.trans h1))).trans (by rw [←mul_assoc];exact mul_le_mul_of_nonneg_right hp.co hx)⟩
variable (q:Heading F)
lemma howls (i:F.Index)(hi:i≠0)(hv:0≤u)(hc:0≤c)(hm:∀ x,F.coeffSize (q.map x) ≤ c*F.coeffSize x) (hf:Bumps Z' f)(ht:∀ w∈Z',‖f w‖≤b) : let v:=Size.axis F i; let x:= q.leads L v; let p(y:ℝ):=y * F.coeffSize (F.core v); let g(y:ℝ):=y*F.coeffSize (vowel F L (F.core v))
    (∀ i,Rainfall.Wallet (f (T! i)) x (p u) (g c))→ Rainfall.Wallet (f z) x (p (2*u)) (g (2*c)):=by
    intro v x p' g he; have hV:0≤V:= zero_le_one.trans (orbitCost_one_le ..)
    have hm': F.core v=v:= (Size.core_axis F i).trans (if_neg hi)
    have hs y:p' y=y:=by unfold p'; rw [hm',Size.size_axis,mul_one]
    have hx:F.coeffSize x ≤ c*(L.val:ℝ)^d := (hm _).trans (mul_le_mul_of_nonneg_left ((size_vowel ..).2.trans_eq (by rw [Size.size_axis,mul_one])) hc)
    have hζ: c≤ g c:= (show c≤ _ from le_of_eq (mul_one c).symm).trans (mul_le_mul_of_nonneg_left ((by rw [show F.core v=v from hm',← Size.size_axis F i]; exact (size_vowel ..).1) : 1 ≤ F.coeffSize (vowel F L (F.core v))) hc)
    rw [show p' (2*u)= 2*p' u from by unfold p'; ring, show g (2*c)=2*g c from by unfold g; ring]
    refine hearth h f x hf he ?_ (by rw [hs]; exact hv) (hc.trans hζ)
    intro w hw; have htb:=ht w hw; let a1:=(f w).1; let P':=(f w).2; have hF:F.coeffSize a1≤(N₀)*b:=(Push.Local.size_le_norm F a1).trans (mul_le_mul_of_nonneg_left ((le_max_left ..).trans htb) (Nat.cast_nonneg _))
    rw [hs]; have h1 : 1 ≤ s₀:= turnCost_near ..
    have he(v:ℝ)(hz:v ≤ b) : s₀*v ≤ g c*Real.exp M:=(mul_le_mul_of_nonneg_left hz (zero_le_one.trans h1)).trans (hp.ray.trans (mul_le_mul_of_nonneg_right hζ (Real.exp_pos _).le))
    refine ⟨(mul_le_mul_of_nonneg_left ?_ hV).trans hp.primary,he _ ((le_max_left ..).trans ((le_max_right ..).trans htb)), (le_mul_of_one_le_left (norm_nonneg _) h1).trans (he _ ((le_max_right ..).trans ((le_max_right ..).trans htb)))⟩
    rw [sub_eq_add_neg]; have he':F.coeffSize (-x)=F.coeffSize x:=by simp only [Frame.coeffSize,Pi.neg_apply,norm_neg]
    exact (Size.add ..).trans (add_le_add hF (he'.trans_le hx))
end YM.UVExtension.Cloud
