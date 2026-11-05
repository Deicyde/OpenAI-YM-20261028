import YM.MergeProof.Chalet
import YM.MergeProof.Memo
-- import Sails bulky? unavoidable separate later. no yet
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}(B:SectionData F) (H : History G) (N p i : ℕ) (Y : Hol G)
local notation "Rout" => H.rep N p i
local notation "Old" => H.rep N p (i+1)
local notation "WorkSite" => H.S.side i p
local notation "StartSite" => H.S.side (i+1) p
local notation "g₀" => Config G StartSite → ℂ
local notation "Lℓ" => H.S.block i
-- sockets. Uses Chart selected for proofs. turnset X budget.
def Coupon (α : Config G StartSite→ℂ)(ρ:Res G StartSite) (δ:ℂ) (Q:GaugeDoor Old Rout)(A:Wing→Prop)(f:g₀)(lead:F.Coeff)(c t u:ℝ):Prop:=∃ P:Coefficient F WorkSite, Gig B H N p i Y f P lead c t ∧ Tale A 0 0 ((↑(Lℓ).val:ℂ)^d) α ρ (profile (Rout).activities P.forced) δ u t Q

def exactGas {f:Side}(A:Activities G f)(j:ℕ) (p:Config G f→ℂ) : Res G f:= Pi.single (barcode A j) p
variable (Q:GaugeDoor (H.rep N p (i+1)) (H.rep N p i))
-- AND unit private. C0 root cost for main axis; cQ≈Cred.Cover. calendar.
structure Stampede (C w t:ℝ)(T:Heading F) (A:Wing→Prop) : Prop where
   -- insert Q binder
   main (j:F.Index): j≠0 → let v:=Size.axis F j; let Z:=Extra.Histories.primary (0:Site StartSite) v
    Coupon B H N p i Y (Z.exponentialEntry 0 B Old) 0 0 Q A (Z.density 0 B Old) (T.leads Lℓ v) (w*F.coeffSize (F.core v)) (C*F.coeffSize (Bid.vowel F Lℓ (F.core v))) t
   regular (f:g₀)(b:Support StartSite)(x:ℝ): let u:=(Old).p.mass b x
    RegFit Old 0 d Y b f→ (Old).p.supBounds 0 b f x→ Coupon B H N p i Y (masked (Old).p.threshold b f) 0 0 Q A (salary Old b f) 0 (w*u) (w*u) (2*u)
   forced (f:g₀)(j:ℕ)(x:ℝ): let u:=(Old).p.mass ((Old).activities.forced j).support x
    f≠0 → A (.gasKey j)→ SlotFit Old 0 j f→ 0≤x → (∀ U,‖f U‖≤x) → Coupon B H N p i Y 0 (exactGas (Old).activities j f) 0 Q A (Extra.Histories.fare Old j f) 0 (w*(u / Real.sqrt (H.levels.clock.forcedAllowance (i+1)))) (w*(u / Real.sqrt (H.levels.clock.forcedAllowance (i+1)))) (2*u)
   map_norm v : F.coeffSize (T.map v) ≤ C * F.coeffSize v ∧ F.coeffSize (T.map.symm v) ≤ C * F.coeffSize v
-- version parameter alternate docks Rin & E given by equalities. Syntax.
end YM.MergeProof
