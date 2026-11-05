import YM.FullVolume.Panel.Fleece
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
open Extra.Histories
set_option quotPrecheck false
open MergeProof.Matric
-- pin costs laid out concrete stamp. b_H denominators etc
variable (Z: Rep G (H.S.side (i+1) p))(L:Side) (P:MergeProof.Matric.Plate F (H.S.side (i+1) p) (H.S.side i p))
local notation "f"=>H.S.side (i+1) p
open Bid
structure Prints (T:Heading F)(u ζ v:ℝ)(S:GaugeDoor (H.rep N p (i+1)) (H.rep N p i))(X:Wing→Prop):Prop where
  heading z: F.coeffSize (T.map z) ≤ u * F.coeffSize z ∧ F.coeffSize (T.map.symm z) ≤ u*F.coeffSize z
  main j:let x:= Size.axis F j; let Q:= Extra.Histories.primary (0:Site f) x
    Span B H N p i Y (tell (P.main j)) (Q.exponentialEntry 0 B Z) 0 (x 0) S X (Q.density 0 B Z) (T.leads L x) (ζ*F.coeffSize (F.core x)) (u*F.coeffSize (vowel F L (F.core x))) v
  regular j U t: let b:= mapSeat (n:=f) j; let x:=(Z).p.mass b t -- f unknown in mapSeat
    RegFit Z 0 d Y b U→ (Z).p.supBounds 0 b U t→ Span B H N p i Y (tell (P.tint j U)) (masked (Z).p.threshold b U) 0 0 S X (Extra.Histories.salary (Z) b U) 0 (ζ*x) (ζ*x) (2*x)
  forced l U t: let a:=(Z).p.mass ((Z).activities.forced l).support t
    U≠0→ X (.gasKey l)→ SlotFit Z 0 l U→ 0 ≤ t → (∀ V, ‖U V‖ ≤ t) → Span B H N p i Y (tell (P.ink l U)) 0 (exactGas (Z).activities l U) 0 S X (Extra.Histories.fare Z l U) 0 (ζ*(a/Real.sqrt (H.levels.clock.forcedAllowance (i+1)))) (ζ*(a/Real.sqrt (H.levels.clock.forcedAllowance (i+1)))) (2*a)
  blank i: P.ink i 0=0
lemma printsWave (ht:H.rep N p (i+1)=Z)(hH:H.S.block i=L) {T r u v S X} (hp: Prints B H N p i Y Z L P T r u v S X): Matric.Plate.Prints B H N p i Y P T r u v S X:=by
   subst L Z; exact ⟨hp.heading,hp.main,hp.regular,hp.forced,hp.blank⟩
lemma currencyX (s:Wing→Prop)(q:GaugeDoor Old Rout)(h:H.Selected)(hm:i<N) (hz:H.rep N p (i+1)=Z)(hl:H.S.block i=L)(c w t:ℝ)(hp:0≤t)(T:Heading F):let P:= Extra.Histories.primary 0 F.e0
    Matric.Span B H N p i Y (Extra.Histories.primary (0:Site c') (((L.val:ℂ)^d) • F.e0)) (P.exponentialEntry 0 B Z) 0 1 q s (P.density 0 B Z) (T.leads L F.e0)
      (w*F.coeffSize (F.core F.e0)) (c*F.coeffSize (vowel F L (F.core F.e0))) t:=by
   subst Z L; exact cashJ B H N p i Y s q h hm c w t hp T
end YM.MergeProof
