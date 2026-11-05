import YM.UVExtension.Eyelet.Wares
import YM.UVExtension.Orchard.Apple
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
structure Sends (D:GaugeDoor Old R) (X:Set Wing) (α : Config G n'→ℂ)(ρ:Res G n') (ψ:ℂ) (g:Config G n'→ℂ) (v:F.Coeff) (c t w:ℝ)(q:Bucket F (R).p A n) : Prop where
    mints: ∃ P:Coefficient F n, Gig B H N p m A g P v c t ∧ Tale X 0 0 (((H.S.block m).val:ℂ)^d) α ρ (profile (R).activities P.forced) ψ w t D ∧ Eye P A R Λ=q
variable (Z : Keeper (H.rep N p (m+1)).p (H.rep N p (m+1)).activities)
    (D:GaugeDoor (H.rep N p (m+1)) (H.rep N p m)) (X:Set Wing)
lemma rents (q:(O)) {α : Config G n'→ℂ}{ρ:Res G n'}{ψ:ℂ}{g:Config G n'→ℂ} {v:F.Coeff}{c t w p0 u y:ℝ}(h:Sends B H N p m A D X α ρ ψ g v c t w q)(hc:c≤p0)(hu:t≤ u)(hw:w≤ y): Sends B H N p m A D X α ρ ψ g v p0 u y q:=by
    obtain ⟨P,h,hS,hZ⟩:= h.mints; exact ⟨P,h.weaken hc hu,hS.climb le_rfl hw hu,hZ⟩

-- None = sil audio. corner primaries charged even zero. Different pa sets.
def seed (F:Frame G d) (i: Option F.Index):=i.elim 0 (Size.axis F)
def peat (t:ℝ)(i:Option F.Index): ℝ:= i.elim 0 (fun _=>t)

structure RoutesF (F:Frame G d) (n0 n1 : Side) (P B:BudgetPoint)(A: Hol G) where
    vane : Option F.Index → Bucket F B A n0
    glass (i: Eyelet.Slot n1) : Gondola d A i.1 P→L[ℂ] Bucket F B A n0
    wing (i: StockTag n1) : Eyelet.Stream G P i→L[ℂ] Bucket F B A n0
    route : StockTag n1↪ℕ

abbrev Fence := RoutesF F n n' (Old).p (R).p A
variable (L:RoutesF F (H.S.side m p) (H.S.side (m+1) p) (H.rep N p (m+1)).p (H.rep N p m).p A)
namespace RoutesF
variable {G:Gauge}{n0 n1:Side} {P B0:BudgetPoint} {d : ℕ}{F:Frame G d} {A:Hol G}
variable (M: RoutesF F n0 n1 P B0 A)
def income (v:Cow G n1 P d A)(i:Option F.Index): Listing→ Bucket F B0 A n0:= consist (M.vane i) (fun j=> M.glass (key n1 j) (v.1 (key n1 j))) (extend M.route (fun j=> M.wing j (v.2 j)) 0)
def rain (v:Cow G n1 P d A)(i:Option F.Index): Bucket F B0 A n0:= ∑' l, rooms n0 F A B0 (aisleN (code Listing) l) (M.income v i l)
end RoutesF
structure Manor (V :Heading F)(C η t:ℝ) : Prop where
    coins : Nonempty (Keeper (R).p (R).activities)
    route : L.route= cart («R»:=Old) Z
    good : SoundDoor (H.levels.clock.op m p) D
    map_norm x: F.coeffSize (V.map x) ≤ C*F.coeffSize x ∧ F.coeffSize (V.map.symm x)≤ C*F.coeffSize x
    pivot i: let v:=seed F i; let P:=Extra.Histories.primary (0:Site n') v
             Sends B H N p m A D X (P.exponentialEntry 0 B Old) 0 (v 0) (P.density 0 B Old) (V.leads (H.S.block m) v) (η*F.coeffSize (F.core v)) (C*F.coeffSize (vowel F (H.S.block m) (F.core v))) (peat t (F:=F) i) (L.vane i)
    glass (i:Eyelet.Slot n') (j:Birth A i.1 (Old).p d) c: let u:= (Old).p.mass i.1.val c
              (Old).p.supBounds 0 i.1.val j.val c → Sends B H N p m A D X (masked (Old).p.threshold i.1.val j.val) 0 0 (salary Old i.1.val j.val) 0 (η*u) (η*u) (2*u) (L.glass i ((fee (Old).p i.1.val:ℂ) • twig (tin d A i.1 (Old).p) j))
    wing i (x:Eyelet.Bolt (G:=G) (Old).p i) a : let j:= L.route i; let u:=(Old).p.mass i.val.1 a
               0 ≤ a → (∀ U, ‖x.val U‖ ≤ a) → Sends B H N p m A D X 0 (exactGas (Old).activities j x.val) 0 (Extra.Histories.fare Old j x.val) 0 (η*(u/κ)) (η*(u/κ)) (2*u) (L.wing i ((((fee (Old).p i.val.1 / κ):ℝ):ℂ) • twig (sink (G:=G) (Old).p i) x))

local notation "t'"=> Doors.rate (H.S.block m)
lemma leisure (q:GaugeDoor Old R)  {t u:ℝ}(ht:0≤ t)(hu:0≤u) : Sends B H N p m A q X 0 0 0 0 0 t t u 0:=by
   -- Need Keeper for Eligible to see projection.Eye=0 even if not.
   let P:Coefficient F n:= Extra.Histories.primary 0 0; have hp: P.Format 0 A R:= primary_format _
   have he: P.density 0 B R=0:=by
      funext V; rw [show P.density 0 B R V= _ from primary_density B (R) 0 V];change _*part B 0 R V 0=0;rw [map_zero,mul_zero]
   have hκ: P.remBound 0 R (kappa H m) 0:= primary_rem _ (Real.sqrt_pos.mpr (forcedPos _ _))
   obtain ⟨a,b,hb,h₁⟩:= rem_tabs.mp hκ
   have h2:a=0∧ b=0:= by have hz:=hb.first; have hr:=hb.second; constructor<;>linarith
   obtain ⟨rfl,rfl⟩:=h2
   refine ⟨P,⟨hp,?_,by simpa only [P, Extra.Histories.primary,sub_zero,Frame.coeffSize,Pi.zero_apply,norm_zero,sum_const_zero,mul_zero] using ht, 0,0,hb,by rw [mul_zero,add_zero]; exact ht⟩,?_,?_⟩
   · have hx:= (H.levels.transition_mass m p (Old).beta); rw [he,Extra.Histories.blast]; funext x; simp [StepData.push]
   · rw [show profile (R).activities P.forced = 0 by funext i j; simp [profile,P,cram,Extra.Histories.primary]]; exact taped hu ht
   unfold Eye; split; next h=> exact Prod.ext rfl (Prod.ext (Eligible.blankC h|>.1) (Eligible.blankC h|>.2))
   next =>rfl
end YM.UVExtension.Lacing

#print axioms YM.UVExtension.Lacing.rents
#check YM.UVExtension.Lacing.Manor
#print axioms YM.UVExtension.Lacing.Manor
